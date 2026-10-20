pub mod decompressor;

pub use decompressor::{
    Error, decompress_from_reader, decompress_from_reader_to_writer, decompress_from_slice,
    decompress_from_slice_to_writer,
};
