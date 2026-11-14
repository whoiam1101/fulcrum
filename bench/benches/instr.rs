//! Instruction counts of the core operations under Callgrind (gungraun): the
//! performance gate of CI.
//!
//! Wall-clock time on shared runners drifts by 5–15 %, instruction counts do
//! not, so `.github/workflows/perf.yml` runs this file on the base and on the
//! head commit and fails when any benchmark executes more instructions than
//! the limit allows. Every benchmark runs one operation over [`N`] operands
//! from the same generators as `benches/ops.rs`; the operands are built in
//! `setup` and are not counted.
//!
//! Run locally with Valgrind and `gungraun-runner` of the same version as the
//! `gungraun` dev-dependency: `cargo bench --bench instr`.

use fulcrum::{FixedFloat16, FixedFloat32, FixedFloat64, FixedFloat8};
use fulcrum_bench::{divisor, ff16, ff32, ff64, ff8, inputs, operand, radicand};
use gungraun::prelude::*;
use std::fmt::Write;
use std::hint::black_box;

/// Operands per benchmark.
const N: usize = 256;

macro_rules! width {
    ($module:ident, $T:ident, $make:ident) => {
        mod $module {
            use super::*;

            fn values(seed: u64, raw: fn(u64) -> i64) -> Vec<$T> {
                inputs(N, seed).into_iter().map(|x| $make(raw(x))).collect()
            }

            pub fn pairs() -> (Vec<$T>, Vec<$T>) {
                (values(1, operand), values(2, operand))
            }

            pub fn quotients() -> (Vec<$T>, Vec<$T>) {
                (values(3, operand), values(4, divisor))
            }

            pub fn triples() -> (Vec<$T>, Vec<$T>, Vec<$T>) {
                (values(5, operand), values(6, operand), values(7, operand))
            }

            pub fn texts() -> Vec<String> {
                values(8, operand).iter().map(|x| x.to_string()).collect()
            }

            pub fn formatted() -> (Vec<$T>, String) {
                (values(9, operand), String::with_capacity(64))
            }

            #[library_benchmark]
            #[bench::ops(setup = pairs)]
            pub fn add((a, b): (Vec<$T>, Vec<$T>)) {
                for (x, y) in a.iter().zip(&b) {
                    black_box(black_box(*x) + black_box(*y));
                }
            }

            #[library_benchmark]
            #[bench::ops(setup = pairs)]
            pub fn mul((a, b): (Vec<$T>, Vec<$T>)) {
                for (x, y) in a.iter().zip(&b) {
                    black_box(black_box(*x) * black_box(*y));
                }
            }

            #[library_benchmark]
            #[bench::ops(setup = quotients)]
            pub fn div((a, d): (Vec<$T>, Vec<$T>)) {
                for (x, y) in a.iter().zip(&d) {
                    black_box(black_box(*x) / black_box(*y));
                }
            }

            #[library_benchmark]
            #[bench::ops(setup = triples)]
            pub fn mul_add((a, b, c): (Vec<$T>, Vec<$T>, Vec<$T>)) {
                for ((x, y), z) in a.iter().zip(&b).zip(&c) {
                    black_box(black_box(*x).mul_add(black_box(*y), black_box(*z)));
                }
            }

            #[library_benchmark]
            #[bench::ops(setup = texts)]
            pub fn parse(texts: Vec<String>) {
                for s in &texts {
                    black_box($T::parse(black_box(s.as_str())).unwrap());
                }
            }

            #[library_benchmark]
            #[bench::ops(setup = formatted)]
            pub fn display((a, mut out): (Vec<$T>, String)) {
                for x in &a {
                    out.clear();
                    write!(out, "{}", black_box(*x)).unwrap();
                    black_box(&out);
                }
            }

            library_benchmark_group!(
                name = group,
                benchmarks = [add, mul, div, mul_add, parse, display]
            );
        }
    };
}

macro_rules! roots {
    ($module:ident, $T:ident, $make:ident) => {
        mod $module {
            use super::*;

            fn values(seed: u64) -> Vec<$T> {
                inputs(N, seed)
                    .into_iter()
                    .map(|x| $make(radicand(x)))
                    .collect()
            }

            pub fn radicands() -> Vec<$T> {
                values(10)
            }

            pub fn legs() -> (Vec<$T>, Vec<$T>) {
                (values(11), values(12))
            }

            #[library_benchmark]
            #[bench::ops(setup = radicands)]
            pub fn sqrt(a: Vec<$T>) {
                for x in &a {
                    black_box(black_box(*x).sqrt());
                }
            }

            #[library_benchmark]
            #[bench::ops(setup = radicands)]
            pub fn rsqrt(a: Vec<$T>) {
                for x in &a {
                    black_box(black_box(*x).rsqrt());
                }
            }

            #[library_benchmark]
            #[bench::ops(setup = legs)]
            pub fn hypot((a, b): (Vec<$T>, Vec<$T>)) {
                for (x, y) in a.iter().zip(&b) {
                    black_box(black_box(*x).hypot(black_box(*y)));
                }
            }

            library_benchmark_group!(name = group, benchmarks = [sqrt, rsqrt, hypot]);
        }
    };
}

width!(w8, FixedFloat8, ff8);
width!(w16, FixedFloat16, ff16);
width!(w32, FixedFloat32, ff32);
width!(w64, FixedFloat64, ff64);
roots!(r32, FixedFloat32, ff32);
roots!(r64, FixedFloat64, ff64);

use r32::group as roots32;
use r64::group as roots64;
use w16::group as width16;
use w32::group as width32;
use w64::group as width64;
use w8::group as width8;

main!(
    library_benchmark_groups = width8,
    width16,
    width32,
    width64,
    roots32,
    roots64
);
