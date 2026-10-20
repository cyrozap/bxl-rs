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

extern crate bit_reverse;
use bit_reverse::ParallelReverse;
use std::collections::TryReserveError;
use std::fmt;
use std::io::{self, Read, Write};
use std::ops::{Index, IndexMut};

// The BXL code tree is always a complete binary tree with 8 levels of
// edges: 255 internal nodes plus 256 leaves, for a total of 511 nodes.
// Using a fixed-size arena keyed by u16 indices lets us relink subtrees
// in O(1) without allocating a node per tree node.
const NODE_COUNT: usize = 511;
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

#[derive(Clone, Copy)]
struct TreeNode {
    weight: u32,
    parent: u16,
    left: u16,
    right: u16,
    symbol: i16,
}

struct NodeTree {
    nodes: [TreeNode; NODE_COUNT],
}

impl NodeTree {
    /// Build the initial complete tree in heap (level) order.
    ///
    /// Root is index 0; `left(i) = 2*i + 1`, `right(i) = 2*i + 2`.
    /// Decoding maps a 1 bit to the left child and a 0 bit to the right
    /// child, so the leaf for symbol `s` lives at `510 - s`.
    const fn new() -> Self {
        let mut nodes = [TreeNode {
            weight: 0,
            parent: NIL,
            left: NIL,
            right: NIL,
            symbol: -1,
        }; NODE_COUNT];

        let mut idx = 0;
        while idx < NODE_COUNT {
            if idx != 0 {
                nodes[idx].parent = ((idx - 1) / 2) as u16;
            }
            if idx < (NODE_COUNT - 1) / 2 {
                nodes[idx].left = (2 * idx + 1) as u16;
                nodes[idx].right = (2 * idx + 2) as u16;
            } else {
                nodes[idx].symbol = (NODE_COUNT - 1 - idx) as i16;
            }
            idx += 1;
        }

        Self { nodes }
    }

    #[inline]
    fn replace_child(&mut self, parent: u16, old: u16, new: u16) {
        if self[parent].right == old {
            self[parent].right = new;
        } else if self[parent].left == old {
            self[parent].left = new;
        } else {
            debug_assert!(false, "node {old} is not a child of {parent}");
            return;
        }
        if new != NIL {
            self[new].parent = parent;
        }
    }

    /// Update the adaptive Huffman tree after a symbol's weight increases.
    ///
    /// Only the local three-node rotation and the affected ancestor weights
    /// are touched; no hashing, scanning, cloning, or allocation is needed.
    fn update(&mut self, current: u16) {
        let parent = self[current].parent;
        if parent == NIL {
            return;
        }
        let grandparent = self[parent].parent;
        if grandparent == NIL {
            return;
        }
        if self[current].weight <= self[parent].weight {
            return;
        }

        let parent_sibling = {
            let gp = &self[grandparent];
            if gp.left == parent { gp.right } else { gp.left }
        };

        // Rotate: current takes parent's place, parent takes the parent
        // sibling's place, and the parent sibling takes current's place.
        self.replace_child(grandparent, parent, current);
        self.replace_child(grandparent, parent_sibling, parent);
        self.replace_child(parent, current, parent_sibling);

        let (left, right) = {
            let p = &self[parent];
            (p.left, p.right)
        };
        let parent_weight = self[left].weight + self[right].weight;
        self[parent].weight = parent_weight;
        self[grandparent].weight = self[current].weight + parent_weight;

        self.update(parent);
        self.update(grandparent);
        self.update(current);
    }
}

impl Index<u16> for NodeTree {
    type Output = TreeNode;

    #[inline(always)]
    fn index(&self, index: u16) -> &Self::Output {
        &self.nodes[index as usize]
    }
}

impl IndexMut<u16> for NodeTree {
    #[inline(always)]
    fn index_mut(&mut self, index: u16) -> &mut Self::Output {
        &mut self.nodes[index as usize]
    }
}

#[inline]
fn get_bit(input: &[u8], bit: usize) -> u8 {
    (input[bit >> 3] >> (7 - (bit & 7))) & 1
}

fn parse_header(input: &[u8]) -> Result<(usize, &[u8]), Error> {
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
        if decoded == u_size {
            break;
        }

        let bit_value = get_bit(compressed, bit);
        node = if bit_value != 0 {
            tree[node].left
        } else {
            tree[node].right
        };

        let symbol = tree[node].symbol;
        if symbol >= 0 {
            emit(symbol as u8);
            decoded += 1;
            tree[node].weight += 1;
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
            node = if bit_value != 0 {
                tree[node].left
            } else {
                tree[node].right
            };

            let symbol = tree[node].symbol;
            if symbol >= 0 {
                emit(symbol as u8);
                decoded += 1;
                tree[node].weight += 1;
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
#[inline]
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
#[inline]
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
#[inline]
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
#[inline]
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
    fn decompress_from_reader_accepts_empty_payload() {
        let input = [0u8; 4];

        assert_eq!(
            decompress_from_reader(&input[..]).unwrap(),
            Vec::<u8>::new()
        );

        let mut output = Vec::new();
        assert_eq!(
            decompress_from_reader_to_writer(&input[..], &mut output).unwrap(),
            0
        );
        assert!(output.is_empty());
    }

    #[test]
    fn arena_tree_is_complete() {
        let tree = NodeTree::new();
        let nodes = &tree.nodes;
        assert_eq!(nodes.len(), NODE_COUNT);
        assert_eq!((nodes[0].left, nodes[0].right), (1, 2));

        let mut leaves = 0;
        for (idx, node) in nodes.iter().enumerate() {
            if node.symbol >= 0 {
                leaves += 1;
                assert_eq!(idx, (NODE_COUNT - 1 - node.symbol as usize));
            } else {
                assert!(node.left != NIL && node.right != NIL);
            }
        }
        assert_eq!(leaves, 256);
        assert_eq!(nodes[510].symbol, 0);
        assert_eq!(nodes[255].symbol, 255);
    }
}
