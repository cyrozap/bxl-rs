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

use sha2::{Digest, Sha256};

const FIXTURES: &[(&str, &[u8], &str)] = &[
    (
        "COPYING",
        include_bytes!("fixtures/COPYING.bxl"),
        "8ceb4b9ee5adedde47b31e975c1d90c73ad27b6b165a1dcd80c7c545eb65b903",
    ),
    (
        "alice",
        include_bytes!("fixtures/alice.bxl"),
        "8df8404123aa50b53c5e982fd65e7efbcdd39a96b3c1d1e77de8665d80b07a48",
    ),
    (
        "don_quixote",
        include_bytes!("fixtures/don_quixote.bxl"),
        "6a1667425aeb2716d0359a1824ce2b62868579319f918dea3d2cd856acf3e84e",
    ),
    (
        "gatsby",
        include_bytes!("fixtures/gatsby.bxl"),
        "144284135106d8acedbc6a6878b42bc76ee4d18f11ca66078e44b27437ef2e72",
    ),
    (
        "jabberwocky",
        include_bytes!("fixtures/jabberwocky.bxl"),
        "070134517f8517fe66b39289c92eb253dbf1ecf78550f828f30bda8ccb290e30",
    ),
    (
        "peter_rabbit",
        include_bytes!("fixtures/peter_rabbit.bxl"),
        "d2dbdbede010ae316332fec365b6ff41053fcdd73f42e4da026a9d017e10c439",
    ),
    (
        "scarlet",
        include_bytes!("fixtures/scarlet.bxl"),
        "76022b869c9891e60fbe95b26d5c9988056c96e7f1b74fd5068daee81d1569ed",
    ),
];

#[test]
fn fixtures_decompress_to_expected_hashes() {
    for &(name, fixture, expected_hash) in FIXTURES {
        let decompressed = bxl::decompress_from_slice(fixture)
            .unwrap_or_else(|err| panic!("failed to decompress {name}: {err}"));
        let actual_hash = format!("{:x}", Sha256::digest(&decompressed));
        assert_eq!(actual_hash, expected_hash, "hash mismatch for {name}");
    }
}
