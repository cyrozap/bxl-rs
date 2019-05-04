/*
 *  src/lib.rs - BXL decompression functionality.
 *  Copyright (C) 2019  Forest Crossman <cyrozap@gmail.com>
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

use std::collections::HashSet;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::time::{Duration, Instant};

extern crate bit_reverse;
use bit_reverse::ParallelReverse;

fn mask_for_bitlen(bitlen: u8) -> u32 {
    if &bitlen == &0 {
        return 0;
    }

    !(1u32.overflowing_shl((32 - &bitlen).into()).0 - 1)
}

type NodeTree = HashSet<Node>;

fn print_node(tree: &NodeTree, node: &Node) {
    let left_child_addr = node.bit_addr.append_bit(1).unwrap();
    match tree.get(&new_node(left_child_addr, 0, None)) {
        Some(child) => {
            println!(
                //"\t\"{}[{:?}, {}, {}]\"->\"{}[{:?}, {}, {}]\" [label=1]; // left",
                "\t\"{}[{:?}, {}]\"->\"{}[{:?}, {}]\" [label=1]; // left",
                node.bit_addr,
                match node.symbol {
                    Some(s) => s as i32,
                    None => -1,
                },
                node.weight,
                //node.bit_addr.bitlen,
                child.bit_addr,
                match child.symbol {
                    Some(s) => s as i32,
                    None => -1,
                },
                child.weight,
                //child.bit_addr.bitlen
            );
            print_node(tree, child);
        }
        None => (),
    }
    let right_child_addr = node.bit_addr.append_bit(0).unwrap();
    match tree.get(&new_node(right_child_addr, 0, None)) {
        Some(child) => {
            println!(
                //"\t\"{}[{:?}, {}, {}]\"->\"{}[{:?}, {}, {}]\" [label=0]; // right",
                "\t\"{}[{:?}, {}]\"->\"{}[{:?}, {}]\" [label=0]; // right",
                node.bit_addr,
                match node.symbol {
                    Some(s) => s as i32,
                    None => -1,
                },
                node.weight,
                //node.bit_addr.bitlen,
                child.bit_addr,
                match child.symbol {
                    Some(s) => s as i32,
                    None => -1,
                },
                child.weight,
                //child.bit_addr.bitlen
            );
            print_node(tree, child);
        }
        None => (),
    }
}

fn print_dot(tree: &NodeTree) {
    println!("Tree cap: {}", tree.capacity());
    println!("Tree len: {}", tree.len());
    println!("digraph NodeTree{{");
    print_node(tree, &new_node(BitAddr { bits: 0, bitlen: 0 }, 0, None));
    println!("}}");
}

#[derive(Copy, Clone, Debug, Eq)]
struct BitAddr {
    bits: u32,
    bitlen: u8,
}

impl Hash for BitAddr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.get_masked_bits().hash(state);
        self.bitlen.hash(state);
    }
}

impl PartialEq for BitAddr {
    fn eq(&self, other: &Self) -> bool {
        self.bitlen == other.bitlen && self.get_masked_bits() == other.get_masked_bits()
    }
}

impl fmt::Display for BitAddr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut bit_vec: Vec<&str> = vec![];
        for i in 0..self.bitlen {
            if (self.bits & (1 << (31 - i))) == 0 {
                bit_vec.push("0");
            } else {
                bit_vec.push("1");
            }
        }
        write!(f, "{}", bit_vec.join(""))
    }
}

impl BitAddr {
    fn get_masked_bits(&self) -> u32 {
        self.bits & mask_for_bitlen(self.bitlen)
    }

    fn try_from(s: &str) -> Result<BitAddr, String> {
        let len = s.len();
        if len > 32 {
            return Err(format!("Invalid bit string length: {} > 32.", len));
        }
        let bitlen = len as u8;

        let mut bits: u32 = 0;
        let str_bytes = s.as_bytes();
        for i in 0..len {
            match str_bytes[i] {
                b'0' => (),
                b'1' => bits |= 1 << (31 - i),
                s => return Err(format!("Invalid bit string: {}", s)),
            }
        }

        Ok(BitAddr { bits, bitlen })
    }

    fn append_bit(&self, bit: u8) -> Result<BitAddr, String> {
        if self.bitlen >= 32 {
            return Err(format!("Max bitlen: {}", self.bitlen));
        }

        let (bits, bitlen) = match bit {
            0 => (self.bits & !(1 << (31 - self.bitlen)), self.bitlen + 1),
            1 => (self.bits | 1 << (31 - self.bitlen), self.bitlen + 1),
            _ => return Err(format!("Invalid bit value \"{}\"--must be 0 or 1.", bit)),
        };

        Ok(BitAddr { bits, bitlen })
    }

    fn is_root(&self) -> bool {
        self.bitlen == 0
    }

    fn get_last_bit(&self) -> Result<u8, &str> {
        // Special case for root node.
        if self.is_root() {
            return Err("The root node has no bits.");
        }

        let last_bit = match (self.bits & (1 << (32 - self.bitlen))) != 0 {
            false => 0,
            true => 1,
        };
        Ok(last_bit)
    }

    fn get_parent_addr(&self) -> Result<BitAddr, &str> {
        // Special case for root node.
        if self.is_root() {
            return Err("The root node has no parents.");
        }

        let parent_bitlen = self.bitlen - 1;
        let mask = mask_for_bitlen(parent_bitlen);

        Ok(BitAddr {
            bits: self.bits & mask,
            bitlen: parent_bitlen,
        })
    }

    fn is_prefix_of(&self, other: BitAddr) -> bool {
        if self.bitlen > other.bitlen {
            return false;
        }

        let mask = mask_for_bitlen(self.bitlen);
        self.bits == other.bits & mask
    }

    fn is_ancestor_of(&self, other: BitAddr) -> bool {
        if self.bitlen >= other.bitlen {
            return false;
        }

        let mask = mask_for_bitlen(self.bitlen);
        self.bits == other.bits & mask
    }

    fn is_parent_of(&self, other: BitAddr) -> bool {
        if self.bitlen + 1 != other.bitlen {
            return false;
        }

        match other.get_parent_addr() {
            Ok(parent_addr) => {
                //println!("self: {:?}", self);
                //println!("&parent_addr: {:?}", &parent_addr);
                self == &parent_addr
            }
            Err(_) => false,
        }
    }

    fn get_sibling_addr(&self) -> Result<BitAddr, &str> {
        // Special case for root node.
        if self.is_root() {
            return Err("The root node has no siblings.");
        }

        let sibling_bits = self.bits ^ (1 << (32 - self.bitlen));
        Ok(BitAddr {
            bits: sibling_bits,
            bitlen: self.bitlen,
        })
    }

    fn is_left_child(&self) -> Result<bool, String> {
        match self.get_last_bit() {
            Ok(0) => Ok(false),
            Ok(1) => Ok(true),
            Ok(bit) => Err(format!("Invalid last bit \"{}\".", bit)),
            Err(err) => Err(err.to_string()),
        }
    }

    fn prefix_swap(&self, old: BitAddr, new: BitAddr) -> Result<BitAddr, String> {
        if !old.is_prefix_of(*self) {
            return Err(format!(
                "Old prefix {} does not match the target address {}.",
                old, self
            ));
        }

        // Mask off LSBs.
        let mask = mask_for_bitlen(old.bitlen);
        let lsbits = (self.bits & !mask) << old.bitlen;

        // Shift bits and add new prefix.
        let bits = new.bits | (lsbits >> new.bitlen);
        let bitlen = self.bitlen - old.bitlen + new.bitlen;

        Ok(BitAddr { bits, bitlen })
    }
}

#[derive(Copy, Clone, Debug, Eq)]
struct Node {
    bit_addr: BitAddr,
    weight: u32,
    symbol: Option<u8>,
}

impl Hash for Node {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.bit_addr.hash(state)
    }
}

impl PartialEq for Node {
    fn eq(&self, other: &Self) -> bool {
        self.bit_addr == other.bit_addr
    }
}

impl Node {
    fn is_leaf(&self) -> bool {
        match self.symbol {
            Some(_) => true,
            None => false,
        }
    }

    fn increase_weight(&self) -> Node {
        let new_weight = self.weight + 1;

        /*
        println!(
            "increase_weight, self: {}, self.weight: {}->{}, self.symbol: {:?}",
            self.bit_addr, self.weight, new_weight, self.symbol,
        );
        */

        Node {
            bit_addr: self.bit_addr,
            weight: new_weight,
            symbol: self.symbol,
        }
    }
}

fn new_node(bit_addr: BitAddr, weight: u32, symbol: Option<u8>) -> Node {
    Node {
        bit_addr,
        weight,
        symbol,
    }
}

fn initialize_tree() -> NodeTree {
    let mut tree = NodeTree::with_capacity(511);
    for symbol in 0..256 {
        for bitlen in 0..(8 + 1) {
            let mask = mask_for_bitlen(bitlen);
            let node_symbol = if bitlen == 8 {
                Some(symbol as u8)
            } else {
                None
            };
            tree.insert(new_node(
                BitAddr {
                    bits: ((symbol as u32) << (32 - 8)) & mask,
                    bitlen: bitlen,
                },
                0,
                node_symbol,
            ));
        }
    }
    tree
}

fn node_needs_swap(tree: &NodeTree, node: &Node) -> bool {
    let parent_addr = match node.bit_addr.get_parent_addr() {
        Ok(a) => a,
        Err(err) => {
            //println!("{:?}", err);
            return false;
        }
    };
    if parent_addr.is_root() {
        // Parent can't be root because root has no siblings.
        return false;
    }
    let parent_node = match tree.get(&new_node(parent_addr, 0, None)) {
        Some(n) => n,
        None => return false,
    };

    /*
    println!(
        "node: {}, node.weight: {}, parent_node: {}, parent_node.weight: {}, node.weight > parent_node.weight: {}",
        node.bit_addr,
        node.weight,
        parent_node.bit_addr,
        parent_node.weight,
        node.weight > parent_node.weight
    );
    */

    node.weight > parent_node.weight
}

fn update_tree_at_node(tree: &mut NodeTree, node: &Node) -> Result<(), String> {
    //println!("update_tree");
    let child_addr = node.bit_addr;
    let mut child_node = match tree.get(node) {
        Some(n) => n.clone(),
        None => return Err(format!("Couldn't find child node: {}", child_addr)),
    };
    let parent_addr = match child_addr.get_parent_addr() {
        Ok(addr) => addr,
        Err(err) => return Err(format!("Couldn't get address of parent: {}", err)),
    };
    let mut parent_node = match tree.get(&new_node(parent_addr, 0, None)) {
        Some(n) => n.clone(),
        None => return Err(format!("Couldn't find parent node: {}", parent_addr)),
    };
    let parent_sibling_addr = match parent_addr.get_sibling_addr() {
        Ok(addr) => addr,
        Err(err) => return Err(format!("Couldn't get address of parent sibling: {}", err)),
    };
    let mut parent_sibling_node = match tree.get(&new_node(parent_sibling_addr, 0, None)) {
        Some(n) => n.clone(),
        None => {
            return Err(format!(
                "Couldn't find sibling of parent node: {}",
                parent_sibling_addr
            ));
        }
    };

    // Collect the child's descendants.
    let mut c_descendants = NodeTree::new();
    // Collect the parent's descendants.
    let mut p_descendants = NodeTree::new();
    // Collect the parent's sibling's descendants.
    let mut ps_descendants = NodeTree::new();
    for tree_node in tree.iter() {
        if child_addr.is_ancestor_of(tree_node.bit_addr) {
            assert!(c_descendants.insert(tree_node.clone()));
        } else if parent_addr.is_ancestor_of(tree_node.bit_addr)
            && !child_addr.is_prefix_of(tree_node.bit_addr)
        {
            assert!(p_descendants.insert(tree_node.clone()));
        } else if parent_sibling_addr.is_ancestor_of(tree_node.bit_addr) {
            assert!(ps_descendants.insert(tree_node.clone()));
        }
    }

    // Remove descendants being moved.
    for desc in &c_descendants {
        assert!(tree.remove(&desc));
    }
    /*
    println!(
        "child_node before removals: {:?}",
        tree.get(&new_node(child_addr, 0, None))
    );
    */
    assert!(tree.remove(&child_node));
    for desc in &p_descendants {
        assert!(tree.remove(&desc));
    }
    assert!(tree.remove(&parent_node));
    for desc in &ps_descendants {
        assert!(tree.remove(&desc));
    }
    assert!(tree.remove(&parent_sibling_node));
    /*
    println!(
        "child_node after removals: {:?}",
        tree.get(&new_node(child_addr, 0, None))
    );
    */

    // Replace P's tree with C's.
    assert_eq!(child_addr, child_node.bit_addr);
    for mut desc in c_descendants {
        //println!("Old c_descendant: {}", desc.bit_addr);
        desc.bit_addr = match desc.bit_addr.prefix_swap(child_addr, parent_addr) {
            Ok(addr) => addr,
            Err(err) => return Err(format!("Failed to replace P's tree with C's: {}", err)),
        };
        //println!("New c_descendant: {}", desc.bit_addr);
        assert!(tree.insert(desc));
    }
    /*
    println!(
        "child_node before child_node insertion: {:?}",
        tree.get(&new_node(child_addr, 0, None))
    );
    */
    //println!("Old child_node.bit_addr: {}", child_node.bit_addr);
    child_node.bit_addr = parent_addr;
    //println!("New child_node.bit_addr: {}", child_node.bit_addr);
    assert!(tree.insert(child_node));
    /*
    println!(
        "child_node after child_node insertion: {:?}",
        tree.get(&new_node(child_addr, 0, None))
    );
    */
    assert_eq!(child_node.bit_addr, parent_addr);

    // Replace PS's tree with P's.
    assert_eq!(parent_addr, parent_node.bit_addr);
    for mut desc in p_descendants {
        //println!("Old p_descendant: {}", desc.bit_addr);
        desc.bit_addr = match desc.bit_addr.prefix_swap(parent_addr, parent_sibling_addr) {
            Ok(addr) => addr,
            Err(err) => return Err(format!("Failed to replace PS's tree with P's: {}", err)),
        };
        //println!("New p_descendant: {}", desc.bit_addr);
        assert!(tree.insert(desc));
        //tree.replace(desc);
    }
    //println!("Old parent_node.bit_addr: {}", parent_node.bit_addr);
    parent_node.bit_addr = parent_sibling_addr;
    //println!("New parent_node.bit_addr: {}", parent_node.bit_addr);
    assert!(tree.insert(parent_node));
    /*
    println!(
        "child_node after parent_node insertion: {:?}",
        tree.get(&new_node(child_addr, 0, None))
    );
    */
    assert_eq!(parent_node.bit_addr, parent_sibling_addr);

    // Replace C's tree with PS's.
    assert_eq!(parent_sibling_addr, parent_sibling_node.bit_addr);
    let new_child_addr = match child_addr.prefix_swap(parent_addr, parent_sibling_addr) {
        Ok(addr) => addr,
        Err(err) => return Err(format!("Failed to get new child address: {}", err)),
    };
    for mut desc in ps_descendants {
        //println!("Old ps_descendant: {}", desc.bit_addr);
        desc.bit_addr = match desc
            .bit_addr
            .prefix_swap(parent_sibling_addr, new_child_addr)
        {
            Ok(addr) => addr,
            Err(err) => return Err(format!("Failed to replace C's tree with PS's: {}", err)),
        };
        //println!("New ps_descendant: {}", desc.bit_addr);
        assert!(tree.insert(desc));
    }
    /*
    println!(
        "Old parent_sibling_node.bit_addr: {}",
        parent_sibling_node.bit_addr
    );
    */
    parent_sibling_node.bit_addr = new_child_addr;
    /*
    println!(
        "New parent_sibling_node.bit_addr: {}",
        parent_sibling_node.bit_addr
    );
    println!(
        "child_node before parent_sibling_node insertion: {:?}",
        tree.get(&new_node(new_child_addr, 0, None))
    );
    */
    assert!(tree.insert(parent_sibling_node));
    assert_eq!(parent_sibling_node.bit_addr, new_child_addr);

    // Update parent weights.
    let parent_left_child_addr = match parent_node.bit_addr.append_bit(1) {
        Ok(addr) => addr,
        Err(err) => {
            return Err(format!(
                "Couldn't get address for left child of parent: {}",
                err
            ));
        }
    };
    let parent_left_child = match tree.get(&new_node(parent_left_child_addr, 0, None)) {
        Some(n) => n.clone(),
        None => {
            return Err(format!(
                "Couldn't find left child node: {}",
                parent_left_child_addr
            ));
        }
    };
    let parent_right_child_addr = match parent_node.bit_addr.append_bit(0) {
        Ok(addr) => addr,
        Err(err) => {
            return Err(format!(
                "Couldn't get address for right child of parent: {}",
                err
            ));
        }
    };
    let parent_right_child = match tree.get(&new_node(parent_right_child_addr, 0, None)) {
        Some(n) => n.clone(),
        None => {
            return Err(format!(
                "Couldn't find right child node: {}",
                parent_right_child_addr
            ));
        }
    };
    parent_node.weight = parent_left_child.weight + parent_right_child.weight;
    assert!(tree.replace(parent_node).is_some());

    // Update grandparent weights.
    let grandparent_addr = match parent_node.bit_addr.get_parent_addr() {
        Ok(addr) => addr,
        Err(err) => return Err(format!("Couldn't get grandparent address: {}", err)),
    };
    let mut grandparent_node = match tree.get(&new_node(grandparent_addr, 0, None)) {
        Some(n) => n.clone(),
        None => {
            return Err(format!(
                "Couldn't find grandparent node: {}",
                grandparent_addr
            ));
        }
    };
    grandparent_node.weight = child_node.weight + parent_node.weight;
    assert!(tree.replace(grandparent_node).is_some());

    //print_dot(tree);

    Ok(())
}

fn update_tree(tree: &mut NodeTree, target: &Node) -> Result<(), String> {
    let mut node = target.clone();
    while node_needs_swap(tree, &node) {
        // The update_tree_at_node() function takes ~7-93 us to run.
        // Best case number of executions: 0
        // Best case total delay: 0 ns
        // Worst case number of executions: > ~7 us
        // Worst case total delay: > ~650 us
        let r = update_tree_at_node(tree, &node);
        match r {
            Ok(()) => (),
            //Ok(()) => println!("Updated tree for node {}.", node.bit_addr),
            Err(err) => {
                return Err(format!(
                    "Failed to update tree at node {}: {}",
                    node.bit_addr, err
                ));
            }
        }
        match node.bit_addr.get_parent_addr()?.get_parent_addr() {
            Ok(addr) => node.bit_addr = addr,
            Err(_) => break,
        }
        node = match tree.get(&node) {
            Some(n) => n.clone(),
            None => return Err(format!("Couldn't find target node {}.", node.bit_addr)),
        };
    }
    //println!("Finished updating trees.");
    Ok(())
}

fn get_bit(input: &[u8], bit: usize) -> u8 {
    let byte = input[bit / 8];
    if (byte & (1 << (7 - (bit % 8)))) > 0 {
        1
    } else {
        0
    }
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
    let mut tree = initialize_tree();
    //print_dot(&tree);

    let mut total_checks = 0;
    let mut total_check_time = Duration::new(0, 0);
    let mut search_addr = BitAddr { bits: 0, bitlen: 1 }; // bitlen is 1 because the sequence is padded with a zero bit to start.
    for bit in 0..num_bits {
        if u_size == decompressed.len() {
            break;
        }

        let bit_value = get_bit(compressed, bit);
        if bit_value > 1 {
            return Err(format!("Bit is neither zero nor one: {}", bit_value));
        }

        search_addr = match search_addr.append_bit(bit_value) {
            Ok(addr) => addr,
            Err(err) => return Err(format!("Failed to append bit to search_addr: {}", err)),
        };
        //println!("{}", search_addr);
        let mut node = match tree.get(&new_node(search_addr, 0, None)) {
            Some(n) => n.clone(),
            None => return Err(format!("Node {} does not exist!", search_addr)),
        };
        if node.is_leaf() {
            //println!("{}", search_addr);
            decompressed.push(node.symbol.unwrap());
            node = node.increase_weight();
            tree.replace(node);
            //println!("Updating tree for reference node {}.", node.bit_addr);
            let now = Instant::now();
            // The update_tree() function on average takes ~800-1400 ns to run.
            // This function runs for every character in the output file.
            let r = update_tree(&mut tree, &node);
            let dur = now.elapsed();
            total_checks += 1;
            total_check_time += dur;
            match r {
                Ok(()) => (),
                Err(err) => {
                    return Err(format!(
                        "Failed to update tree for leaf node {}: {}",
                        node.bit_addr, err
                    ));
                }
            }
            assert!(tree.len() == 511);
            search_addr = BitAddr { bits: 0, bitlen: 0 };
        }
    }
    /*
    println!(
        "Did {} checks in {} ns.",
        total_checks,
        total_check_time.as_nanos()
    );
    */
    //print_dot(&tree);

    assert_eq!(u_size, decompressed.len());

    Ok(decompressed)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bitaddr_to_string() {
        assert_eq!(
            BitAddr {
                bits: 1 << 31,
                bitlen: 1
            }
            .to_string(),
            "1"
        );
        assert_eq!(
            BitAddr {
                bits: 0,
                bitlen: 16
            }
            .to_string(),
            "0000000000000000"
        );
        assert_eq!(
            BitAddr {
                bits: 0,
                bitlen: 32
            }
            .to_string(),
            "00000000000000000000000000000000"
        );
        assert_eq!(
            BitAddr {
                bits: 0xff,
                bitlen: 32
            }
            .to_string(),
            "00000000000000000000000011111111"
        );
    }

    #[test]
    fn bitaddr_from_string() {
        assert_eq!(BitAddr::try_from(""), Ok(BitAddr { bits: 0, bitlen: 0 }));
        assert_eq!(
            BitAddr::try_from("101010"),
            Ok(BitAddr {
                bits: 0b101010 << (32 - 6),
                bitlen: 6
            })
        );
        assert_eq!(
            BitAddr::try_from("00000000000000000000000011111111"),
            Ok(BitAddr {
                bits: 0xff,
                bitlen: 32
            })
        );
    }

    #[test]
    fn bitaddr_append_bit() {
        assert_eq!(
            BitAddr {
                bits: 0,
                bitlen: 31
            }
            .append_bit(0)
            .unwrap(),
            BitAddr {
                bits: 0,
                bitlen: 32
            }
        );
        assert_eq!(
            BitAddr {
                bits: 0,
                bitlen: 31
            }
            .append_bit(1)
            .unwrap(),
            BitAddr {
                bits: 1,
                bitlen: 32
            }
        );
        assert_eq!(
            BitAddr::try_from("").unwrap().append_bit(0).unwrap(),
            BitAddr::try_from("0").unwrap()
        );
        assert_eq!(
            BitAddr::try_from("").unwrap().append_bit(1).unwrap(),
            BitAddr::try_from("1").unwrap()
        );
        assert_eq!(
            BitAddr::try_from("101010").unwrap().append_bit(1).unwrap(),
            BitAddr::try_from("1010101").unwrap()
        );
    }

    #[test]
    fn bitaddr_append_bit_err() {
        assert!(BitAddr { bits: 0, bitlen: 0 }.append_bit(2).is_err());
        assert!(BitAddr {
            bits: 0,
            bitlen: 32
        }
        .append_bit(0)
        .is_err());
    }

    #[test]
    fn bitaddr_get_last_bit() {
        assert_eq!(BitAddr::try_from("0").unwrap().get_last_bit().unwrap(), 0);
        assert_eq!(BitAddr::try_from("1").unwrap().get_last_bit().unwrap(), 1);
        assert_eq!(
            BitAddr::try_from("0101010010101010110100101000")
                .unwrap()
                .get_last_bit()
                .unwrap(),
            0
        );
        assert_eq!(
            BitAddr::try_from("0101010010101010110100101001")
                .unwrap()
                .get_last_bit()
                .unwrap(),
            1
        );
        assert_eq!(
            BitAddr::try_from("111111010101100110")
                .unwrap()
                .get_last_bit()
                .unwrap(),
            0
        );
        assert_eq!(
            BitAddr::try_from("111111010101100111")
                .unwrap()
                .get_last_bit()
                .unwrap(),
            1
        );
    }

    #[test]
    fn bitaddr_is_left_child() {
        assert_eq!(
            BitAddr::try_from("0").unwrap().is_left_child().unwrap(),
            false
        );
        assert_eq!(
            BitAddr::try_from("1").unwrap().is_left_child().unwrap(),
            true
        );
        assert_eq!(
            BitAddr::try_from("0101010010101010110100101000")
                .unwrap()
                .is_left_child()
                .unwrap(),
            false
        );
        assert_eq!(
            BitAddr::try_from("0101010010101010110100101001")
                .unwrap()
                .is_left_child()
                .unwrap(),
            true
        );
        assert_eq!(
            BitAddr::try_from("111111010101100110")
                .unwrap()
                .is_left_child()
                .unwrap(),
            false
        );
        assert_eq!(
            BitAddr::try_from("111111010101100111")
                .unwrap()
                .is_left_child()
                .unwrap(),
            true
        );
    }

    #[test]
    fn bitaddr_get_parent_addr() {
        assert_eq!(
            BitAddr::try_from("0").unwrap().get_parent_addr().unwrap(),
            BitAddr::try_from("").unwrap()
        );
        assert_eq!(
            BitAddr::try_from("1").unwrap().get_parent_addr().unwrap(),
            BitAddr::try_from("").unwrap()
        );
        assert_eq!(
            BitAddr::try_from("1010100")
                .unwrap()
                .get_parent_addr()
                .unwrap(),
            BitAddr::try_from("101010").unwrap()
        );
        assert_eq!(
            BitAddr::try_from("1010101")
                .unwrap()
                .get_parent_addr()
                .unwrap(),
            BitAddr::try_from("101010").unwrap()
        );
    }

    #[test]
    fn bitaddr_is_ancestor_of() {
        assert!(!BitAddr::try_from("")
            .unwrap()
            .is_ancestor_of(BitAddr::try_from("").unwrap()));
        assert!(!BitAddr::try_from("0")
            .unwrap()
            .is_ancestor_of(BitAddr::try_from("0").unwrap()));
        assert!(BitAddr::try_from("")
            .unwrap()
            .is_ancestor_of(BitAddr::try_from("0").unwrap()));
        assert!(BitAddr::try_from("")
            .unwrap()
            .is_ancestor_of(BitAddr::try_from("1").unwrap()));
        assert!(BitAddr::try_from("101010")
            .unwrap()
            .is_ancestor_of(BitAddr::try_from("1010100").unwrap()));
        assert!(BitAddr::try_from("101010")
            .unwrap()
            .is_ancestor_of(BitAddr::try_from("1010101").unwrap()));
        assert!(BitAddr::try_from("")
            .unwrap()
            .is_ancestor_of(BitAddr::try_from("00").unwrap()));
        assert!(BitAddr::try_from("")
            .unwrap()
            .is_ancestor_of(BitAddr::try_from("10").unwrap()));
        assert!(BitAddr::try_from("101010")
            .unwrap()
            .is_ancestor_of(BitAddr::try_from("101010000000").unwrap()));
        assert!(BitAddr::try_from("101010")
            .unwrap()
            .is_ancestor_of(BitAddr::try_from("101010111111").unwrap()));
    }

    #[test]
    fn bitaddr_is_parent_of() {
        assert!(BitAddr::try_from("")
            .unwrap()
            .is_parent_of(BitAddr::try_from("0").unwrap()));
        assert!(BitAddr::try_from("")
            .unwrap()
            .is_parent_of(BitAddr::try_from("1").unwrap()));
        assert!(BitAddr::try_from("101010")
            .unwrap()
            .is_parent_of(BitAddr::try_from("1010100").unwrap()));
        assert!(BitAddr::try_from("101010")
            .unwrap()
            .is_parent_of(BitAddr::try_from("1010101").unwrap()));
    }

    #[test]
    fn bitaddr_get_sibling_addr() {
        assert_eq!(
            BitAddr::try_from("0").unwrap().get_sibling_addr(),
            Ok(BitAddr::try_from("1").unwrap())
        );
        assert_eq!(
            BitAddr::try_from("1").unwrap().get_sibling_addr(),
            Ok(BitAddr::try_from("0").unwrap())
        );
        assert_eq!(
            BitAddr::try_from("101010").unwrap().get_sibling_addr(),
            Ok(BitAddr::try_from("101011").unwrap())
        );
        assert_eq!(
            BitAddr::try_from("101011").unwrap().get_sibling_addr(),
            Ok(BitAddr::try_from("101010").unwrap())
        );
    }

    #[test]
    fn bitaddr_prefix_swap() {
        assert_eq!(
            BitAddr::try_from("000").unwrap().prefix_swap(
                BitAddr::try_from("00").unwrap(),
                BitAddr::try_from("11").unwrap()
            ),
            Ok(BitAddr::try_from("110").unwrap())
        );
        assert_eq!(
            BitAddr::try_from("111").unwrap().prefix_swap(
                BitAddr::try_from("11").unwrap(),
                BitAddr::try_from("00").unwrap()
            ),
            Ok(BitAddr::try_from("001").unwrap())
        );
        assert_eq!(
            BitAddr::try_from("111").unwrap().prefix_swap(
                BitAddr::try_from("1").unwrap(),
                BitAddr::try_from("000").unwrap()
            ),
            Ok(BitAddr::try_from("00011").unwrap())
        );
        assert_eq!(
            BitAddr::try_from("000").unwrap().prefix_swap(
                BitAddr::try_from("00").unwrap(),
                BitAddr::try_from("").unwrap()
            ),
            Ok(BitAddr::try_from("0").unwrap())
        );
        assert_eq!(
            BitAddr::try_from("").unwrap().prefix_swap(
                BitAddr::try_from("").unwrap(),
                BitAddr::try_from("0").unwrap()
            ),
            Ok(BitAddr::try_from("0").unwrap())
        );
        assert_eq!(
            BitAddr::try_from("101010100101010010101010")
                .unwrap()
                .prefix_swap(
                    BitAddr::try_from("101010100101").unwrap(),
                    BitAddr::try_from("01010100101").unwrap()
                ),
            Ok(BitAddr::try_from("01010100101010010101010").unwrap())
        );
    }

    #[test]
    fn bitaddr_check_equivalence() {
        // Trivial cases.
        assert_eq!(
            BitAddr { bits: 0, bitlen: 0 },
            BitAddr { bits: 0, bitlen: 0 }
        );
        assert_eq!(
            BitAddr {
                bits: 1,
                bitlen: 32
            },
            BitAddr {
                bits: 1,
                bitlen: 32
            }
        );

        // Equivalence between two BitAddr instances should be determined using the bitlen and the
        // masked bits, not just the bitlen and bits.
        assert_eq!(
            BitAddr { bits: 1, bitlen: 0 },
            BitAddr { bits: 0, bitlen: 0 }
        );
        assert_eq!(
            BitAddr { bits: 1, bitlen: 0 },
            BitAddr { bits: 0, bitlen: 0 }
        );
        assert_eq!(
            BitAddr {
                bits: 1,
                bitlen: 31
            },
            BitAddr {
                bits: 0,
                bitlen: 31
            }
        );
    }

    #[test]
    fn node_is_leaf() {
        assert!(new_node(BitAddr::try_from("").unwrap(), 0, Some(b'A')).is_leaf());
        assert!(!new_node(BitAddr::try_from("").unwrap(), 0, None).is_leaf());
        assert!(new_node(BitAddr::try_from("101010").unwrap(), 0, Some(b'A')).is_leaf());
        assert!(!new_node(BitAddr::try_from("101010").unwrap(), 0, None).is_leaf());
    }

    #[test]
    fn node_increase_weight() {
        assert_eq!(
            new_node(BitAddr::try_from("").unwrap(), 0, Some(b'A')).increase_weight(),
            new_node(BitAddr::try_from("").unwrap(), 1, Some(b'A'))
        );
        assert_eq!(
            new_node(BitAddr::try_from("").unwrap(), 0, None).increase_weight(),
            new_node(BitAddr::try_from("").unwrap(), 1, None)
        );
        assert_eq!(
            new_node(BitAddr::try_from("101010").unwrap(), 0, Some(b'A')).increase_weight(),
            new_node(BitAddr::try_from("101010").unwrap(), 1, Some(b'A'))
        );
        assert_eq!(
            new_node(BitAddr::try_from("101010").unwrap(), 0, None).increase_weight(),
            new_node(BitAddr::try_from("101010").unwrap(), 1, None)
        );
    }

    #[test]
    fn node_needs_swap_ok() {
        let mut tree = NodeTree::new();
        tree.insert(new_node(BitAddr::try_from("").unwrap(), 0, None));
        tree.insert(new_node(BitAddr::try_from("0").unwrap(), 10, None));
        tree.insert(new_node(BitAddr::try_from("00").unwrap(), 1, None));
        tree.insert(new_node(BitAddr::try_from("01").unwrap(), 100, None));
        assert_eq!(
            node_needs_swap(&tree, &new_node(BitAddr::try_from("").unwrap(), 0, None)),
            false
        );
        assert_eq!(
            node_needs_swap(&tree, &new_node(BitAddr::try_from("0").unwrap(), 10, None)),
            false
        );
        assert_eq!(
            node_needs_swap(&tree, &new_node(BitAddr::try_from("00").unwrap(), 1, None)),
            false
        );
        assert_eq!(
            node_needs_swap(
                &tree,
                &new_node(BitAddr::try_from("01").unwrap(), 100, None)
            ),
            true
        );
    }

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
}
