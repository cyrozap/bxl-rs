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
use std::ops::{Index, IndexMut};

// The BXL code tree is always a complete binary tree with 8 levels of
// edges: 255 internal nodes plus 256 leaves, for a total of 511 nodes.
// Using a fixed-size arena keyed by u16 indices lets us relink subtrees
// in O(1) without allocating a node per tree node.
const NODE_COUNT: usize = 511;
const NIL: u16 = u16::MAX;

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

pub fn decompress(input: &[u8]) -> Result<Vec<u8>, String> {
    if input.len() < 5 {
        return Err(format!(
            "Input too short--expected at least 5 bytes, got {} bytes instead.",
            input.len()
        ));
    }

    let u_size = ((input[0] as u32) << 24
        | (input[1] as u32) << 16
        | (input[2] as u32) << 8
        | (input[3] as u32))
        .swap_bits() as usize;
    eprintln!("Decompressed size: {}", &u_size);

    let compressed = &input[4..];
    let c_size = compressed.len();
    eprintln!("Compressed size: {}", &c_size);

    let num_bits = c_size * 8;
    eprintln!("Number of bits: {}", num_bits);

    let mut decompressed: Vec<u8> = Vec::with_capacity(u_size);
    let mut tree = NodeTree::new();

    // The bitstream is padded with a leading zero bit, which selects the
    // root's right child. Start there and consume the real bits.
    let mut node: u16 = 2;

    for bit in 0..num_bits {
        if decompressed.len() == u_size {
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
            decompressed.push(symbol as u8);
            tree[node].weight += 1;
            tree.update(node);
            node = 0;
        }
    }

    assert_eq!(u_size, decompressed.len());

    Ok(decompressed)
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
