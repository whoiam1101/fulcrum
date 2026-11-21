//! Instruction counts of the core operations under Callgrind (gungraun): the
//! performance gate of CI.
//!
//! Wall-clock time on shared runners drifts by 5–15 %, instruction counts do
//! not, so `.github/workflows/perf.yml` runs this file on the base and on the
//! head commit and fails when any benchmark executes more instructions than
//! the limit allows. Every benchmark runs one operation over [`N`] operands
//! from the same generators as `benches/ops.rs`; the operands are built in
//! `setup` and are not counted. The loops of `fulcrum_bench::loops` run
//! whole, with no `black_box` per element, so that a loop that stops
//! vectorizing executes more instructions. The vector operations of
//! `Vec2` and `Vec3` on 32 and 64 bits run one per element, like the scalar
//! operations.
//!
//! Run locally with Valgrind and `gungraun-runner` of the same version as the
//! `gungraun` dev-dependency: `cargo bench --bench instr`.

use fulcrum::{
    Angle32, Angle64, FixedFloat16, FixedFloat32, FixedFloat64, FixedFloat8, Vec2, Vec3,
};
use fulcrum_bench::{divisor, ff16, ff32, ff64, ff8, inputs, loops, operand, radicand};
use gungraun::prelude::*;
use std::fmt::Write;
use std::hint::black_box;

/// Operands per benchmark.
const N: usize = 256;

/// [`N`] values of a type from the raw generator `raw` and its constructor
/// `make`.
fn values<T>(seed: u64, raw: fn(u64) -> i64, make: fn(i64) -> T) -> Vec<T> {
    fulcrum_bench::values(N, seed, raw, make)
}

macro_rules! width {
    ($module:ident, $T:ident, $make:ident) => {
        mod $module {
            use super::*;

            pub fn pairs() -> (Vec<$T>, Vec<$T>) {
                (values(1, operand, $make), values(2, operand, $make))
            }

            pub fn quotients() -> (Vec<$T>, Vec<$T>) {
                (values(3, operand, $make), values(4, divisor, $make))
            }

            pub fn triples() -> (Vec<$T>, Vec<$T>, Vec<$T>) {
                (
                    values(5, operand, $make),
                    values(6, operand, $make),
                    values(7, operand, $make),
                )
            }

            pub fn texts() -> Vec<String> {
                values(8, operand, $make)
                    .iter()
                    .map(|x| x.to_string())
                    .collect()
            }

            pub fn formatted() -> (Vec<$T>, String) {
                (values(9, operand, $make), String::with_capacity(64))
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

            pub fn radicands() -> Vec<$T> {
                values(10, radicand, $make)
            }

            pub fn legs() -> (Vec<$T>, Vec<$T>) {
                (values(11, radicand, $make), values(12, radicand, $make))
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

macro_rules! vectors {
    ($module:ident, $T:ident, $A:ident, $make:ident) => {
        mod $module {
            use super::*;

            fn plane(seed: u64) -> Vec<Vec2<$T>> {
                values(seed, operand, $make)
                    .into_iter()
                    .zip(values(seed + 1, operand, $make))
                    .map(|(x, y)| Vec2::new(x, y))
                    .collect()
            }

            fn space(seed: u64) -> Vec<Vec3<$T>> {
                plane(seed)
                    .into_iter()
                    .zip(values(seed + 2, operand, $make))
                    .map(|(v, z)| Vec3::new(v.x, v.y, z))
                    .collect()
            }

            pub fn pairs() -> (Vec<Vec2<$T>>, Vec<Vec2<$T>>) {
                (plane(20), plane(22))
            }

            pub fn turns() -> (Vec<Vec2<$T>>, Vec<$A>) {
                let t = inputs(N, 24)
                    .into_iter()
                    .map(|r| $A::from_bits(r as _))
                    .collect();
                (plane(25), t)
            }

            pub fn triples() -> (Vec<Vec3<$T>>, Vec<Vec3<$T>>) {
                (space(27), space(30))
            }

            #[library_benchmark]
            #[bench::ops(setup = pairs)]
            pub fn dot((a, b): (Vec<Vec2<$T>>, Vec<Vec2<$T>>)) {
                for (x, y) in a.iter().zip(&b) {
                    black_box(black_box(*x).dot(black_box(*y)));
                }
            }

            #[library_benchmark]
            #[bench::ops(setup = pairs)]
            pub fn distance_sq((a, b): (Vec<Vec2<$T>>, Vec<Vec2<$T>>)) {
                for (x, y) in a.iter().zip(&b) {
                    black_box(black_box(*x).distance_sq(black_box(*y)));
                }
            }

            #[library_benchmark]
            #[bench::ops(setup = pairs)]
            pub fn angle_to((a, b): (Vec<Vec2<$T>>, Vec<Vec2<$T>>)) {
                for (x, y) in a.iter().zip(&b) {
                    black_box(black_box(*x).angle_to(black_box(*y)));
                }
            }

            #[library_benchmark]
            #[bench::ops(setup = pairs)]
            pub fn length((a, _): (Vec<Vec2<$T>>, Vec<Vec2<$T>>)) {
                for x in &a {
                    black_box(black_box(*x).length());
                }
            }

            #[library_benchmark]
            #[bench::ops(setup = pairs)]
            pub fn normalize((a, _): (Vec<Vec2<$T>>, Vec<Vec2<$T>>)) {
                for x in &a {
                    black_box(black_box(*x).normalize());
                }
            }

            #[library_benchmark]
            #[bench::ops(setup = pairs)]
            pub fn clamp_length((a, _): (Vec<Vec2<$T>>, Vec<Vec2<$T>>)) {
                let (lo, hi) = ($make(1 << 15), $make(3 << 15));
                for x in &a {
                    black_box(black_box(*x).clamp_length(lo, hi));
                }
            }

            #[library_benchmark]
            #[bench::ops(setup = turns)]
            pub fn rotate((a, t): (Vec<Vec2<$T>>, Vec<$A>)) {
                for (x, r) in a.iter().zip(&t) {
                    black_box(black_box(*x).rotate(black_box(*r)));
                }
            }

            #[library_benchmark]
            #[bench::ops(setup = triples)]
            pub fn cross3((a, b): (Vec<Vec3<$T>>, Vec<Vec3<$T>>)) {
                for (x, y) in a.iter().zip(&b) {
                    black_box(black_box(*x).cross(black_box(*y)));
                }
            }

            #[library_benchmark]
            #[bench::ops(setup = triples)]
            pub fn normalize3((a, _): (Vec<Vec3<$T>>, Vec<Vec3<$T>>)) {
                for x in &a {
                    black_box(black_box(*x).normalize());
                }
            }

            library_benchmark_group!(
                name = group,
                benchmarks = [
                    dot,
                    distance_sq,
                    angle_to,
                    length,
                    normalize,
                    clamp_length,
                    rotate,
                    cross3,
                    normalize3
                ]
            );
        }
    };
}

macro_rules! slices {
    ($module:ident, $T:ident, $Bits:ty, $make:ident, $add:ident, $sub:ident, $mul:ident, $mul_int:ident, $mul_add:ident, $lerp:ident) => {
        mod $module {
            use super::*;

            pub fn pairs() -> (Vec<$T>, Vec<$T>, Vec<$T>) {
                (
                    values(13, operand, $make),
                    values(14, operand, $make),
                    vec![$T::ZERO; N],
                )
            }

            pub fn scaled() -> (Vec<$T>, Vec<$Bits>, Vec<$T>) {
                let n = inputs(N, 15)
                    .into_iter()
                    .map(|x| ((x >> 60) as i64 - 8) as $Bits)
                    .collect();
                (values(16, operand, $make), n, vec![$T::ZERO; N])
            }

            pub fn triples() -> (Vec<$T>, Vec<$T>, Vec<$T>, Vec<$T>) {
                (
                    values(17, operand, $make),
                    values(18, operand, $make),
                    values(19, operand, $make),
                    vec![$T::ZERO; N],
                )
            }

            #[library_benchmark]
            #[bench::ops(setup = pairs)]
            pub fn add((a, b, mut out): (Vec<$T>, Vec<$T>, Vec<$T>)) {
                loops::$add(&a, &b, &mut out);
                black_box(&out);
            }

            #[library_benchmark]
            #[bench::ops(setup = pairs)]
            pub fn sub((a, b, mut out): (Vec<$T>, Vec<$T>, Vec<$T>)) {
                loops::$sub(&a, &b, &mut out);
                black_box(&out);
            }

            #[library_benchmark]
            #[bench::ops(setup = pairs)]
            pub fn mul((a, b, mut out): (Vec<$T>, Vec<$T>, Vec<$T>)) {
                loops::$mul(&a, &b, &mut out);
                black_box(&out);
            }

            #[library_benchmark]
            #[bench::ops(setup = scaled)]
            pub fn mul_int((a, n, mut out): (Vec<$T>, Vec<$Bits>, Vec<$T>)) {
                loops::$mul_int(&a, &n, &mut out);
                black_box(&out);
            }

            #[library_benchmark]
            #[bench::ops(setup = triples)]
            pub fn mul_add((a, b, c, mut out): (Vec<$T>, Vec<$T>, Vec<$T>, Vec<$T>)) {
                loops::$mul_add(&a, &b, &c, &mut out);
                black_box(&out);
            }

            #[library_benchmark]
            #[bench::ops(setup = triples)]
            pub fn lerp((a, b, t, mut out): (Vec<$T>, Vec<$T>, Vec<$T>, Vec<$T>)) {
                loops::$lerp(&a, &b, &t, &mut out);
                black_box(&out);
            }

            library_benchmark_group!(
                name = group,
                benchmarks = [add, sub, mul, mul_int, mul_add, lerp]
            );
        }
    };
}

width!(w8, FixedFloat8, ff8);
width!(w16, FixedFloat16, ff16);
width!(w32, FixedFloat32, ff32);
width!(w64, FixedFloat64, ff64);
roots!(r32, FixedFloat32, ff32);
roots!(r64, FixedFloat64, ff64);
vectors!(v32, FixedFloat32, Angle32, ff32);
vectors!(v64, FixedFloat64, Angle64, ff64);
slices!(
    s8,
    FixedFloat8,
    i8,
    ff8,
    add_8,
    sub_8,
    mul_8,
    mul_int_8,
    mul_add_8,
    lerp_8
);
slices!(
    s16,
    FixedFloat16,
    i16,
    ff16,
    add_16,
    sub_16,
    mul_16,
    mul_int_16,
    mul_add_16,
    lerp_16
);
slices!(
    s32,
    FixedFloat32,
    i32,
    ff32,
    add_32,
    sub_32,
    mul_32,
    mul_int_32,
    mul_add_32,
    lerp_32
);

use r32::group as roots32;
use r64::group as roots64;
use s16::group as loops16;
use s32::group as loops32;
use s8::group as loops8;
use v32::group as vectors32;
use v64::group as vectors64;
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
    roots64,
    loops8,
    loops16,
    loops32,
    vectors32,
    vectors64
);
