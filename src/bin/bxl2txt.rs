/*
 *  src/bin/bxl2txt.rs - A simple utility to convert a BXL file to plaintext.
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

use std::io::{self, Write};
use std::{env, fs};

extern crate bxl;
use bxl::decompress;

fn main() {
    let filename = env::args().nth(1).expect("please supply a filename");
    let file = fs::read(&filename);
    let file = match file {
        Ok(f) => f,
        Err(error) => {
            eprintln!("Error opening file {:?}: {:?}", &filename, error);
            return;
        }
    };
    match decompress(&file) {
        Ok(d) => match io::stdout().write(&d) {
            Ok(_) => (),
            Err(e) => eprintln!("Failed to write to stdout: {}", e),
        },
        Err(e) => eprintln!("Failed to decompress: {}", e),
    }
}
