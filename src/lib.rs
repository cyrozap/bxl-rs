//! A Rust library for parsing Ultra Librarian `.bxl` files.
//!
//! BXL is a proprietary CAD/CAE file format used for electronic component
//! symbols, footprints, and 3D models. This crate currently implements the
//! decompression stage: it turns a BXL payload into the original text data.
//!
//! # Quick start
//!
//! If the whole BXL file is already in memory, use
//! [`decompress_from_slice`] to get a `Vec<u8>`:
//!
//! ```no_run
//! use std::fs;
//!
//! fn main() -> Result<(), Box<dyn std::error::Error>> {
//!     let input = fs::read("design.bxl")?;
//!     let decompressed = bxl::decompress_from_slice(&input)?;
//!     fs::write("design.txt", decompressed)?;
//!     Ok(())
//! }
//! ```
//!
//! For larger files, the reader/writer APIs avoid holding the entire output
//! in memory. Buffering is left to the caller:
//!
//! ```no_run
//! use std::fs::File;
//! use std::io::{BufReader, BufWriter};
//!
//! fn main() -> Result<(), Box<dyn std::error::Error>> {
//!     let input = BufReader::new(File::open("design.bxl")?);
//!     let output = BufWriter::new(File::create("design.txt")?);
//!     bxl::decompress_from_reader_to_writer(input, output)?;
//!     Ok(())
//! }
//! ```
//!
//! # Choosing an API
//!
//! | Input | Output | Function |
//! |---|---|---|
//! | `&[u8]` | `Vec<u8>` | [`decompress_from_slice`] |
//! | `&[u8]` | `Write` | [`decompress_from_slice_to_writer`] |
//! | `Read` | `Vec<u8>` | [`decompress_from_reader`] |
//! | `Read` | `Write` | [`decompress_from_reader_to_writer`] |
//!
//! All functions return [`Error`] on malformed input, I/O failures, or
//! allocation failure. See the [`decompressor`] module for format and
//! algorithm details.

pub mod decompressor;

pub use decompressor::{
    Error, decompress_from_reader, decompress_from_reader_to_writer, decompress_from_slice,
    decompress_from_slice_to_writer,
};
