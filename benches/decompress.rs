/*
 *  Copyright (C) 2026  Forest Crossman <cyrozap@gmail.com>
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

use std::io::{self, Cursor};
use std::time::Duration;

use criterion::{Criterion, Throughput, black_box, criterion_group, criterion_main};

const FIXTURES: &[(&str, &[u8])] = &[
    ("COPYING", include_bytes!("../tests/fixtures/COPYING.bxl")),
    ("alice", include_bytes!("../tests/fixtures/alice.bxl")),
    (
        "don_quixote",
        include_bytes!("../tests/fixtures/don_quixote.bxl"),
    ),
    ("gatsby", include_bytes!("../tests/fixtures/gatsby.bxl")),
    (
        "jabberwocky",
        include_bytes!("../tests/fixtures/jabberwocky.bxl"),
    ),
    (
        "peter_rabbit",
        include_bytes!("../tests/fixtures/peter_rabbit.bxl"),
    ),
    ("scarlet", include_bytes!("../tests/fixtures/scarlet.bxl")),
];

fn bench_decompress(c: &mut Criterion) {
    let mut group = c.benchmark_group("decompress_from_slice");
    group.sample_size(20);
    group.measurement_time(Duration::from_secs(3));

    for &(name, data) in FIXTURES {
        group.throughput(Throughput::Bytes(data.len() as u64));
        group.bench_function(name, |b| {
            b.iter(|| black_box(bxl::decompress_from_slice(black_box(data)).unwrap()));
        });
    }
    group.finish();

    let mut group = c.benchmark_group("decompress_from_reader_to_writer");
    group.sample_size(20);
    group.measurement_time(Duration::from_secs(3));

    for &(name, data) in FIXTURES {
        group.throughput(Throughput::Bytes(data.len() as u64));
        group.bench_function(name, |b| {
            b.iter(|| {
                let mut reader = Cursor::new(black_box(data));
                let written =
                    bxl::decompress_from_reader_to_writer(&mut reader, io::sink()).unwrap();
                black_box(written)
            });
        });
    }
    group.finish();
}

criterion_group!(benches, bench_decompress);
criterion_main!(benches);
