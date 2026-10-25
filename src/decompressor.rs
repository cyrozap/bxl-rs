/*
 *  src/decompressor.rs - BXL decompression functionality.
 *  Copyright (C) 2019, 2025-2026  Forest Crossman <cyrozap@gmail.com>
 *
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program.  If not, see <https://www.gnu.org/licenses/>.
 */

//! BXL decompression.
//!
//! # Format
//!
//! A BXL payload begins with a four-byte header containing the decompressed
//! size as a bit-reversed big-endian `u32`. The remaining bytes form an
//! adaptive-Huffman bitstream packed most-significant-bit first.
//!
//! The decoder behaves as if a single zero padding bit preceded the stream.
//! That lets the first symbol be decoded with seven explicit bits; every
//! subsequent symbol uses the full eight-bit path through the code tree.
//!
//! # Code tree
//!
//! The initial tree is the complete binary tree of depth 8: 255 internal
//! nodes and 256 leaves, for 511 nodes total. A 1 bit selects the left child
//! and a 0 bit selects the right child. Leaves store the byte values.
//!
//! The tree is kept in a flat arena. Each node stores its weight, parent, left
//! and right child indices, and an optional leaf symbol. Interior nodes have
//! no symbol, while a leaf's symbol identifies the decoded byte. The flat
//! representation lets rotations relink a few indices without allocating.
//!
//! # Adaptive update
//!
//! Every node starts with weight 0. After a leaf is decoded, its weight is
//! incremented. If the leaf has become heavier than its parent, the decoder
//! rotates the leaf, its parent, and the parent's sibling so that the heavier
//! node moves closer to the root. The weights of the rotated parent and
//! grandparent are recomputed from their new children, and the update
//! continues upward from the nodes whose links changed.
//!
//! This keeps the tree ordered by weight (the sibling property), allowing
//! frequently occurring bytes to be represented by shorter paths.
//!
//! Decoding stops as soon as the header's declared number of output bytes has
//! been produced. Any remaining padding bits in the final compressed byte are
//! ignored.
//!
//! # Input and output
//!
//! The slice-based functions operate directly on memory and are the fastest
//! option when the compressed input is already available:
//!
//! | Input | Output | Function |
//! |---|---|---|
//! | `&[u8]` | `Vec<u8>` | [`decompress_from_slice`] |
//! | `&[u8]` | `Write` | [`decompress_from_slice_to_writer`] |
//! | `Read` | `Vec<u8>` | [`decompress_from_reader`] |
//! | `Read` | `Write` | [`decompress_from_reader_to_writer`] |
//!
//! The reader functions read one compressed byte at a time and do not buffer
//! internally. Wrap file-backed readers in [`std::io::BufReader`] to avoid a
//! system call per byte. Likewise, writer output is unbuffered; use
//! [`std::io::BufWriter`] when writing to a file. If an error occurs after
//! output has started, the destination may already contain partial data.
//!
//! # Errors
//!
//! All public functions return [`Error`], which distinguishes malformed or
//! truncated input, I/O failures, size mismatches, and allocation failure.

use std::collections::TryReserveError;
use std::fmt;
use std::io::{self, Read, Write};

use bit_reverse::ParallelReverse;

// BXL decompression uses an adaptive Huffman code tree. The tree always
// has the same shape: a complete binary tree with 8 levels of edges
// (255 internal nodes and 256 leaves, 511 nodes total). Leaves represent
// byte values; internal nodes just route bits. Decoding maps a 1 bit to
// the left child and a 0 bit to the right child.
//
// Each leaf starts with weight 0. Every time a byte is decoded, its leaf's
// weight is incremented and the tree is adjusted so heavier nodes tend to
// move closer to the root. Because the shape never changes, the tree can
// be stored in fixed-size structure-of-arrays and updated by relinking indices.
const NODE_COUNT: usize = 511;
// Sentinel used for absent parents/children. All real node indices fit in u16.
const NIL: u16 = u16::MAX;

/// Errors returned by the BXL decompression API.
#[derive(Debug)]
pub enum Error {
    /// The input does not contain a complete four-byte size header.
    InputTooShort,
    /// The compressed length cannot be represented as a bit count.
    InputTooLarge,
    /// The compressed input ended before the declared output size was produced.
    UnexpectedEof { expected: usize, decoded: usize },
    /// Decoding produced a different number of bytes than the header declared.
    SizeMismatch { expected: usize, actual: usize },
    /// The output buffer could not be allocated.
    Allocation(TryReserveError),
    /// Reading compressed input failed.
    Read(io::Error),
    /// Writing decompressed output failed.
    Write(io::Error),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::InputTooShort => f.write_str("input is too short to contain a BXL size header"),
            Error::InputTooLarge => f.write_str("compressed input is too large to process"),
            Error::UnexpectedEof { expected, decoded } => write!(
                f,
                "compressed input ended after {decoded} of {expected} output bytes"
            ),
            Error::SizeMismatch { expected, actual } => write!(
                f,
                "decompressed size mismatch: header says {expected} bytes, decoded {actual} bytes"
            ),
            Error::Allocation(err) => write!(f, "failed to allocate output buffer: {err}"),
            Error::Read(err) => write!(f, "failed to read compressed input: {err}"),
            Error::Write(err) => write!(f, "failed to write decompressed data: {err}"),
        }
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Error::Allocation(err) => Some(err),
            Error::Read(err) | Error::Write(err) => Some(err),
            _ => None,
        }
    }
}

/// Adaptive Huffman tree stored as a structure-of-arrays.
///
/// All five node fields live in their own fixed-size array. The tree is a
/// complete 8-level binary tree, so a node index fully identifies a node and
/// the arrays never grow.
struct NodeTree {
    // Number of decoded bytes that pass through this node.
    weight: [u32; NODE_COUNT],
    parent: [u16; NODE_COUNT],
    left: [u16; NODE_COUNT],
    right: [u16; NODE_COUNT],
    // Non-negative for leaves (the represented byte), -1 for internal nodes.
    symbol: [i16; NODE_COUNT],
}

impl NodeTree {
    /// Build the initial complete tree in heap (level) order.
    ///
    /// Root is index 0; `left(i) = 2*i + 1`, `right(i) = 2*i + 2`.
    /// Decoding maps a 1 bit to the left child and a 0 bit to the right
    /// child, so the leaf for symbol `s` lives at `510 - s`.
    const fn new() -> Self {
        let weight = [0u32; NODE_COUNT];
        let mut parent = [NIL; NODE_COUNT];
        let mut left = [NIL; NODE_COUNT];
        let mut right = [NIL; NODE_COUNT];
        let mut symbol = [-1i16; NODE_COUNT];

        let mut idx = 0;
        while idx < NODE_COUNT {
            // Heap layout: children of `idx` are 2*idx+1 (left/1-bit) and
            // 2*idx+2 (right/0-bit).
            if idx != 0 {
                parent[idx] = ((idx - 1) / 2) as u16;
            }
            if idx < (NODE_COUNT - 1) / 2 {
                left[idx] = (2 * idx + 1) as u16;
                right[idx] = (2 * idx + 2) as u16;
            } else {
                // Leaves occupy the second half of the arena. With the
                // left/right convention above, symbol `s` starts at 510 - s.
                symbol[idx] = (NODE_COUNT - 1 - idx) as i16;
            }
            idx += 1;
        }

        Self {
            weight,
            parent,
            left,
            right,
            symbol,
        }
    }

    #[inline]
    fn replace_child(&mut self, parent: u16, old: u16, new: u16) {
        // Replace one of `parent`'s children and repair the new child's
        // parent link. Used when rotating nodes during an update.
        let parent_idx = parent as usize;
        if self.right[parent_idx] == old {
            self.right[parent_idx] = new;
        } else if self.left[parent_idx] == old {
            self.left[parent_idx] = new;
        } else {
            debug_assert!(false, "node {old} is not a child of {parent}");
            return;
        }
        if new != NIL {
            self.parent[new as usize] = parent;
        }
    }

    /// Update the adaptive Huffman tree after a symbol's weight increases.
    ///
    /// Only the local three-node rotation and the affected ancestor weights
    /// are touched; no hashing, scanning, cloning, or allocation is needed.
    fn update(&mut self, current: u16) {
        // The adaptive Huffman update maintains the sibling property:
        // nodes are ordered by weight, with heavier nodes closer to the
        // root. A node only needs to move when it has become heavier than
        // its parent. The root and its children have no valid rotation, so
        // they stop the walk.
        let current_idx = current as usize;
        let parent = self.parent[current_idx];
        if parent == NIL {
            return;
        }
        let parent_idx = parent as usize;
        let grandparent = self.parent[parent_idx];
        if grandparent == NIL {
            return;
        }
        if self.weight[current_idx] <= self.weight[parent_idx] {
            return;
        }

        // The parent's sibling is the other child of the grandparent.
        let grandparent_idx = grandparent as usize;
        let parent_sibling = if self.left[grandparent_idx] == parent {
            self.right[grandparent_idx]
        } else {
            self.left[grandparent_idx]
        };

        // Rotate three nodes: `current` takes its parent's place, the
        // parent takes the parent's sibling's place, and the parent's
        // sibling takes `current`'s old place. This preserves the complete
        // tree shape while moving the heavier node upward.
        self.replace_child(grandparent, parent, current);
        self.replace_child(grandparent, parent_sibling, parent);
        self.replace_child(parent, current, parent_sibling);

        // The rotation changed which children belong to `parent` and
        // `grandparent`, so recompute their weights from their new children.
        let left = self.left[parent_idx];
        let right = self.right[parent_idx];
        let parent_weight = self.weight[left as usize] + self.weight[right as usize];
        self.weight[parent_idx] = parent_weight;
        self.weight[grandparent_idx] = self.weight[current_idx] + parent_weight;

        // The rotation may have made another local relationship invalid;
        // continue upward from each node whose position or children changed.
        self.update(parent);
        self.update(grandparent);
        self.update(current);
    }
}

#[inline]
fn get_bit(input: &[u8], bit: usize) -> u8 {
    // Bits are packed most-significant-bit first within each byte.
    (input[bit >> 3] >> (7 - (bit & 7))) & 1
}

fn parse_header(input: &[u8]) -> Result<(usize, &[u8]), Error> {
    // The format begins with a four-byte, bit-reversed big-endian size.
    // Reversing the bits yields the number of bytes the payload expands to.
    let header = match input.first_chunk::<4>() {
        Some(header) => header,
        None => return Err(Error::InputTooShort),
    };
    let u_size = u32::from_be_bytes(*header).swap_bits() as usize;
    let compressed = input.get(4..).unwrap_or(&[]);

    Ok((u_size, compressed))
}

#[inline(always)]
fn decode<F: FnMut(u8)>(compressed: &[u8], u_size: usize, mut emit: F) -> Result<(), Error> {
    let num_bits = match compressed.len().checked_mul(8) {
        Some(num_bits) => num_bits,
        None => return Err(Error::InputTooLarge),
    };

    let mut tree = NodeTree::new();

    // The bitstream is padded with a leading zero bit, which selects the
    // root's right child. Start there and consume the real bits.
    let mut node: u16 = 2;
    let mut decoded = 0usize;

    for bit in 0..num_bits {
        // The header gives the exact output size; any remaining bits in the
        // final compressed byte are padding and are deliberately ignored.
        if decoded == u_size {
            break;
        }

        // 1 selects the left child, 0 the right child.
        let bit_value = get_bit(compressed, bit);
        let node_idx = node as usize;
        node = if bit_value != 0 {
            tree.left[node_idx]
        } else {
            tree.right[node_idx]
        };

        // A non-negative symbol marks a leaf. Emit it, then increase its
        // weight and adapt the tree before starting the next symbol at root.
        let node_idx = node as usize;
        let symbol = tree.symbol[node_idx];
        if symbol >= 0 {
            emit(symbol as u8);
            decoded += 1;
            tree.weight[node_idx] += 1;
            tree.update(node);
            node = 0;
        }
    }

    if decoded != u_size {
        return Err(Error::SizeMismatch {
            expected: u_size,
            actual: decoded,
        });
    }

    Ok(())
}

fn read_header<R: Read>(reader: &mut R) -> Result<usize, Error> {
    // The stream has the same four-byte bit-reversed size header as the
    // slice-based format. Read it separately so decoding can start at the
    // first compressed byte.
    let mut header = [0u8; 4];
    match reader.read_exact(&mut header) {
        Ok(()) => Ok(u32::from_be_bytes(header).swap_bits() as usize),
        Err(err) if err.kind() == io::ErrorKind::UnexpectedEof => Err(Error::InputTooShort),
        Err(err) => Err(Error::Read(err)),
    }
}

struct ByteReader<R> {
    reader: R,
}

impl<R: Read> ByteReader<R> {
    fn new(reader: R) -> Self {
        Self { reader }
    }

    /// Read the next compressed byte, returning `None` at end of input.
    ///
    /// Buffering is intentionally left to the caller (for example with a
    /// `BufReader`); this adapter never allocates or buffers internally.
    #[inline]
    fn next_byte(&mut self) -> io::Result<Option<u8>> {
        let mut byte = [0u8; 1];
        match self.reader.read_exact(&mut byte) {
            Ok(()) => Ok(Some(byte[0])),
            Err(err) if err.kind() == io::ErrorKind::UnexpectedEof => Ok(None),
            Err(err) => Err(err),
        }
    }
}

#[inline(always)]
fn decode_reader<R: Read, F: FnMut(u8)>(
    reader: &mut R,
    u_size: usize,
    mut emit: F,
) -> Result<(), Error> {
    let mut bytes = ByteReader::new(reader);
    let mut tree = NodeTree::new();
    let mut node: u16 = 2;
    let mut decoded = 0usize;

    // Read one byte at a time and walk its eight bits from MSB to LSB.
    // This is the streaming equivalent of `decode`: the tree state and bit
    // order are identical, but the input arrives through `Read`.
    while decoded < u_size {
        let byte = match bytes.next_byte() {
            Ok(Some(byte)) => byte,
            Ok(None) => {
                return Err(Error::UnexpectedEof {
                    expected: u_size,
                    decoded,
                });
            }
            Err(err) => return Err(Error::Read(err)),
        };

        for shift in (0..8).rev() {
            if decoded == u_size {
                break;
            }

            let bit_value = (byte >> shift) & 1;
            let node_idx = node as usize;
            node = if bit_value != 0 {
                tree.left[node_idx]
            } else {
                tree.right[node_idx]
            };

            let node_idx = node as usize;
            let symbol = tree.symbol[node_idx];
            if symbol >= 0 {
                emit(symbol as u8);
                decoded += 1;
                tree.weight[node_idx] += 1;
                tree.update(node);
                node = 0;
            }
        }
    }

    Ok(())
}

/// Decompress a BXL payload from a reader into a newly allocated `Vec`.
///
/// Wrap file-backed readers in a `BufReader` to avoid one read per byte.
///
/// # Errors
///
/// Returns [`Error::InputTooShort`] if the header is incomplete, [`Error::Read`]
/// if reading the header or compressed data fails, [`Error::UnexpectedEof`] if
/// the input ends before the declared output size, and [`Error::Allocation`]
/// if the output buffer cannot be allocated.
pub fn decompress_from_reader<R: Read>(mut reader: R) -> Result<Vec<u8>, Error> {
    let u_size = read_header(&mut reader)?;

    let mut decompressed: Vec<u8> = Vec::new();
    decompressed
        .try_reserve_exact(u_size)
        .map_err(Error::Allocation)?;

    decode_reader(&mut reader, u_size, |byte| decompressed.push(byte))?;

    Ok(decompressed)
}

/// Decompress a BXL payload from a reader, writing to `writer`.
///
/// Wrap file-backed readers in a `BufReader` to avoid one read per byte.
/// Bytes are written directly to `writer`; wrap it in a `BufWriter` if
/// desired. The number of bytes written is returned on success.
///
/// # Errors
///
/// Returns [`Error::InputTooShort`] if the header is incomplete, [`Error::Read`]
/// if reading the header or compressed data fails, [`Error::UnexpectedEof`] if
/// the input ends before the declared output size, and [`Error::Write`] if
/// writing the decompressed data fails.
pub fn decompress_from_reader_to_writer<R: Read, W: Write>(
    mut reader: R,
    mut writer: W,
) -> Result<usize, Error> {
    let u_size = read_header(&mut reader)?;
    let mut write_error: Option<io::Error> = None;

    decode_reader(&mut reader, u_size, |byte| {
        if write_error.is_some() {
            return;
        }
        if let Err(err) = writer.write_all(&[byte]) {
            write_error = Some(err);
        }
    })?;

    if let Some(err) = write_error {
        return Err(Error::Write(err));
    }

    Ok(u_size)
}

/// Decompress a BXL payload into a newly allocated `Vec`.
///
/// # Errors
///
/// Returns [`Error::InputTooShort`] if the input lacks a complete header,
/// [`Error::InputTooLarge`] if the compressed length overflows, [`Error::SizeMismatch`]
/// if the input does not contain enough data for the declared output size, and
/// [`Error::Allocation`] if the output buffer cannot be allocated.
pub fn decompress_from_slice(input: &[u8]) -> Result<Vec<u8>, Error> {
    let (u_size, compressed) = parse_header(input)?;

    let mut decompressed: Vec<u8> = Vec::new();
    decompressed
        .try_reserve_exact(u_size)
        .map_err(Error::Allocation)?;

    decode(compressed, u_size, |byte| decompressed.push(byte))?;

    Ok(decompressed)
}

/// Decompress a BXL payload, writing the result to `writer`.
///
/// Bytes are written directly to `writer`; wrap it in a `BufWriter` (or use
/// `decompress_from_slice` for a `Vec`) if buffering is desired. The number
/// of bytes written is returned on success. If decoding fails after output
/// has been produced, `writer` may already have received a partial result.
///
/// # Errors
///
/// Returns [`Error::InputTooShort`] if the input lacks a complete header,
/// [`Error::InputTooLarge`] if the compressed length overflows, [`Error::SizeMismatch`]
/// if the input does not contain enough data for the declared output size,
/// and [`Error::Write`] if writing the decompressed data fails.
pub fn decompress_from_slice_to_writer<W: Write>(
    input: &[u8],
    mut writer: W,
) -> Result<usize, Error> {
    let (u_size, compressed) = parse_header(input)?;
    let mut write_error: Option<std::io::Error> = None;

    decode(compressed, u_size, |byte| {
        if write_error.is_some() {
            return;
        }
        if let Err(err) = writer.write_all(&[byte]) {
            write_error = Some(err);
        }
    })?;

    if let Some(err) = write_error {
        return Err(Error::Write(err));
    }

    Ok(u_size)
}

#[cfg(test)]
mod tests {
    use super::*;

    const EMPTY_BXL: &[u8] = &[0x00, 0x00, 0x00, 0x00];
    const HELLO_WORLD_BXL: &[u8] = &[
        0x30, 0x00, 0x00, 0x00, 0xd0, 0x95, 0x63, 0x2b, 0x59, 0xa0, 0x2e, 0x50, 0x51, 0x91, 0x80,
    ];
    const HELLO_WORLD: &[u8] = b"hello, world";

    #[test]
    fn get_bit_ok() {
        assert_eq!(get_bit(&[0x80], 0), 1);
        assert_eq!(get_bit(&[0x80], 3), 0);
        assert_eq!(get_bit(&[0x80, 0x01, 0x10], 0), 1);
        assert_eq!(get_bit(&[0x80, 0x01, 0x10], 7), 0);
        assert_eq!(get_bit(&[0x80, 0x01, 0x10], 9), 0);
        assert_eq!(get_bit(&[0x80, 0x01, 0x10], 15), 1);
        assert_eq!(get_bit(&[0x80, 0x01, 0x10], 16), 0);
        assert_eq!(get_bit(&[0x80, 0x01, 0x10], 19), 1);
    }

    #[test]
    fn decompress_from_slice_rejects_short_input() {
        assert!(matches!(
            decompress_from_slice(&[]),
            Err(Error::InputTooShort)
        ));
        assert!(matches!(
            decompress_from_slice(&[0, 0, 0]),
            Err(Error::InputTooShort)
        ));
    }

    #[test]
    fn decompress_empty_payload() {
        assert_eq!(decompress_from_slice(EMPTY_BXL).unwrap(), Vec::<u8>::new());
        assert_eq!(
            decompress_from_reader(&EMPTY_BXL[..]).unwrap(),
            Vec::<u8>::new()
        );

        let mut output = Vec::new();
        assert_eq!(
            decompress_from_reader_to_writer(&EMPTY_BXL[..], &mut output).unwrap(),
            0
        );
        assert!(output.is_empty());
    }

    #[test]
    fn decompress_hello_world() {
        assert_eq!(decompress_from_slice(HELLO_WORLD_BXL).unwrap(), HELLO_WORLD);
    }

    #[test]
    fn decompress_truncated_hello_world_fails() {
        let truncated = &HELLO_WORLD_BXL[..HELLO_WORLD_BXL.len() - 1];
        assert!(matches!(
            decompress_from_slice(truncated),
            Err(Error::SizeMismatch { .. })
        ));
    }

    #[test]
    fn arena_tree_is_complete() {
        let tree = NodeTree::new();
        assert_eq!(tree.parent.len(), NODE_COUNT);
        assert_eq!((tree.left[0], tree.right[0]), (1, 2));

        let mut leaves = 0;
        for idx in 0..NODE_COUNT {
            if tree.symbol[idx] >= 0 {
                leaves += 1;
                assert_eq!(idx, (NODE_COUNT - 1 - tree.symbol[idx] as usize));
            } else {
                assert!(tree.left[idx] != NIL && tree.right[idx] != NIL);
            }
        }
        assert_eq!(leaves, 256);
        assert_eq!(tree.symbol[510], 0);
        assert_eq!(tree.symbol[255], 255);
    }
}
