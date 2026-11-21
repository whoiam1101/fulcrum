//! Operations of fulcrum vs the `fixed` crate (same formats) vs native floats.
//!
//! Operands lie in `[-2, 2)`, divisors in `±[0.5, 2)`: realistic magnitudes,
//! results rarely saturate.
//!
//! `throughput`: independent operations over arrays of 4096 operands, the
//! compiler may vectorize. `latency`: a dependent chain, one result feeds the
//! next operation. `fixed` is measured with its default operators (wrapping in
//! release, truncating) and with `saturating_*` (closest to fulcrum).
//!
//! The latency chains keep `|x|` in `[0.25, 4)`, see [`bounded_chain`].
//!
//! `int/i32`, `int/i64` and `int/i128` run the same throughput loops on plain integers
//! (wrapping `+` and `*`, truncating `/`): a lower bound, not a competitor.
//!
//! Combined operations (`mul_add`, `mul_div`, `lerp`) and a dot product of
//! 4096 terms are measured for throughput, integers included. `fixed` has
//! `saturating_mul_add` and `saturating_lerp`, which truncate once; its
//! `mul_div` is `x * y / z`, truncated twice, and its dot product sums
//! saturating products, truncated per term, while fulcrum rounds to nearest
//! once (`add_product` for the dot product).
//!
//! `loops`: the batch operations of stage 7, `+`, `-`, `*`, `mul_int`,
//! `mul_add` and `lerp` over 4096 operands, fulcrum through the loops of
//! `fulcrum_bench::loops` that `bin/asm.rs` checks for vectorization, `fixed`
//! with saturating arithmetic through the same loop shapes (`saturating_*`,
//! `saturating_mul_int`, `saturating_mul_add`, `saturating_lerp`, which
//! truncate), and `i16`, `i32` with wrapping arithmetic and no rounding. The
//! integer factors of `mul_int` lie in `[-8, 8)`.
//!
//! Square roots (`sqrt`, `rsqrt`, `hypot`) are measured for throughput on
//! operands in `(0, 256)`, against the software floats of `libm` and the
//! hardware floats of `std` (`rsqrt` of a float is `1 / x.sqrt()`).
//!
//! Trigonometry is measured for throughput: angles in `[-2, 2)` (radians, or
//! turns for `sin_turns` and `cos_turns`), `asin` and `acos` on `[-1, 1)`,
//! `atan2` on two operands, against `libm`, the `std` floats (both get
//! `sin(τ·x)` for the functions in turns) and the `cordic` crate on the
//! `fixed` types of the same format (it has no functions in turns).
//!
//! Exponentials and logarithms are measured for throughput: `log2` and `ln`
//! on `(0, 256)`, `exp2` and `exp` on `[-2, 2)`, `pow` of a base in
//! `(0, 4)` to an exponent in `[-2, 2)`, `powi` of a base in `[-2, 2)` to an
//! integer in `[-8, 8]`, against `libm` (its `pow` for `powi`), the `std`
//! floats and the `exp` of the `cordic` crate, its only function of the
//! group; `fixed` has only integer logarithms.
//!
//! Vectors: `dot`, `length`, `normalize`, `distance_sq`, `rotate`,
//! `angle_to` and `clamp_length` of `Vec2` and `cross`, `length`,
//! `normalize` of `Vec3` for throughput, coordinates in `[-2, 2)`, against
//! `glam` on `f32`. The macro benchmark "one tick" of `fulcrum_bench::tick`
//! steers 5 000 units from a fresh state each time; its time is reported
//! per unit.

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use fulcrum::{FixedFloat16, FixedFloat32, FixedFloat64, FixedFloat8};
use fulcrum_bench::loops::{self, map2, map3, map_int};
use fulcrum_bench::{divisor, ff16, ff32, ff64, ff8, inputs, operand, q32_32, radicand, values};
use std::hint::black_box;

const N: usize = 4096;
const CHAIN: usize = 1024;

macro_rules! bench_ops {
    ($c:expr, $name:literal, $T:ty, $make:expr, $add:expr, $mul:expr, $div:expr) => {{
        bench_ops!(@throughput $c, $name, $T, $make, $add, $mul, $div);
        let (mul, div) = ($mul, $div);
        let (mul_start, mul_chain) = bounded_chain($make, mul, 3);
        let (div_start, div_chain) = bounded_chain($make, div, 4);

        let mut g = $c.benchmark_group("latency");
        g.throughput(Throughput::Elements(CHAIN as u64));
        g.bench_function(BenchmarkId::new("mul", $name), |bn| {
            bn.iter(|| {
                let ys = black_box(&mul_chain);
                let mut x = black_box(mul_start);
                for y in ys {
                    x = mul(x, *y);
                }
                black_box(x)
            })
        });
        g.bench_function(BenchmarkId::new("div", $name), |bn| {
            bn.iter(|| {
                let ys = black_box(&div_chain);
                let mut x = black_box(div_start);
                for y in ys {
                    x = div(x, *y);
                }
                black_box(x)
            })
        });
        g.finish();
    }};
    (@throughput $c:expr, $name:literal, $T:ty, $make:expr, $add:expr, $mul:expr, $div:expr) => {{
        let a: Vec<$T> = values(N, 1, operand, $make);
        let b: Vec<$T> = values(N, 2, divisor, $make);
        let mut out: Vec<$T> = a.clone();
        let add = $add;
        let mul = $mul;
        let div = $div;

        let mut g = $c.benchmark_group("throughput");
        g.throughput(Throughput::Elements(N as u64));
        g.bench_function(BenchmarkId::new("add", $name), |bn| {
            bn.iter(|| {
                let (a, b) = (black_box(&a), black_box(&b));
                for ((o, x), y) in out.iter_mut().zip(a).zip(b) {
                    *o = add(*x, *y);
                }
                black_box(&out);
            })
        });
        g.bench_function(BenchmarkId::new("mul", $name), |bn| {
            bn.iter(|| {
                let (a, b) = (black_box(&a), black_box(&b));
                for ((o, x), y) in out.iter_mut().zip(a).zip(b) {
                    *o = mul(*x, *y);
                }
                black_box(&out);
            })
        });
        g.bench_function(BenchmarkId::new("div", $name), |bn| {
            bn.iter(|| {
                let (a, b) = (black_box(&a), black_box(&b));
                for ((o, x), y) in out.iter_mut().zip(a).zip(b) {
                    *o = div(*x, *y);
                }
                black_box(&out);
            })
        });
        g.finish();
    }};
}

/// Operands for a dependent chain `x = op(x, y)` that keeps `|x|` in
/// `[0.25, 4)`.
///
/// Random factors from `±[0.5, 2)` drift: a product of 1024 of them overflows
/// and a quotient underflows, so floats would hit subnormals or infinity and
/// fixed-point would saturate or reach zero, which measures special cases
/// instead of ordinary arithmetic. Each step takes the factor `y` or its
/// reciprocal, whichever keeps `x` in range, simulated in the type's own
/// arithmetic.
fn bounded_chain<T: Copy + PartialOrd>(
    make: impl Fn(i64) -> T,
    op: impl Fn(T, T) -> T,
    seed: u64,
) -> (T, Vec<T>) {
    let (lo, hi) = (make(1 << 14), make(1 << 18));
    let (nlo, nhi) = (make(-(1 << 14)), make(-(1 << 18)));
    let ok = |t: T| (t >= lo && t < hi) || (t <= nlo && t > nhi);
    let start = make(1 << 16);
    let mut x = start;
    let ys = inputs(CHAIN, seed)
        .into_iter()
        .map(|r| {
            let q = divisor(r);
            let y = make(q);
            let y = if ok(op(x, y)) { y } else { make((1 << 32) / q) };
            x = op(x, y);
            assert!(ok(x), "chain left the range");
            y
        })
        .collect();
    (start, ys)
}

fn to_f64(q16: i64) -> f64 {
    q16 as f64 / 65536.0
}

fn ops(c: &mut Criterion) {
    use fixed::types::{I16F16, I32F32, I8F8};

    bench_ops!(
        c,
        "fulcrum/FixedFloat8",
        FixedFloat8,
        ff8,
        |x, y| x + y,
        |x, y| x * y,
        |x, y| x / y
    );
    bench_ops!(
        c,
        "fulcrum/FixedFloat16",
        FixedFloat16,
        ff16,
        |x, y| x + y,
        |x, y| x * y,
        |x, y| x / y
    );
    bench_ops!(
        c,
        "fulcrum/FixedFloat32",
        FixedFloat32,
        ff32,
        |x, y| x + y,
        |x, y| x * y,
        |x, y| x / y
    );
    bench_ops!(
        c,
        "fulcrum/FixedFloat64",
        FixedFloat64,
        ff64,
        |x, y| x + y,
        |x, y| x * y,
        |x, y| x / y
    );

    let i8f8 = |q: i64| I8F8::from_bits((q >> 8) as i16);
    let i16f16 = |q: i64| I16F16::from_bits(q as i32);
    let i32f32 = |q: i64| I32F32::from_bits(q32_32(q));
    bench_ops!(
        c,
        "fixed/I8F8",
        I8F8,
        i8f8,
        |x, y| x + y,
        |x, y| x * y,
        |x, y| x / y
    );
    bench_ops!(
        c,
        "fixed/I16F16",
        I16F16,
        i16f16,
        |x, y| x + y,
        |x, y| x * y,
        |x, y| x / y
    );
    bench_ops!(
        c,
        "fixed/I32F32",
        I32F32,
        i32f32,
        |x, y| x + y,
        |x, y| x * y,
        |x, y| x / y
    );
    bench_ops!(
        c,
        "fixed-sat/I8F8",
        I8F8,
        i8f8,
        |x: I8F8, y| x.saturating_add(y),
        |x: I8F8, y| x.saturating_mul(y),
        |x: I8F8, y| x.saturating_div(y)
    );
    bench_ops!(
        c,
        "fixed-sat/I16F16",
        I16F16,
        i16f16,
        |x: I16F16, y| x.saturating_add(y),
        |x: I16F16, y| x.saturating_mul(y),
        |x: I16F16, y| x.saturating_div(y)
    );
    bench_ops!(
        c,
        "fixed-sat/I32F32",
        I32F32,
        i32f32,
        |x: I32F32, y| x.saturating_add(y),
        |x: I32F32, y| x.saturating_mul(y),
        |x: I32F32, y| x.saturating_div(y)
    );

    bench_ops!(
        @throughput c,
        "int/i32",
        i32,
        |q: i64| q as i32,
        |x: i32, y| x.wrapping_add(y),
        |x: i32, y| x.wrapping_mul(y),
        |x: i32, y| x / y
    );
    bench_ops!(
        @throughput c,
        "int/i64",
        i64,
        q32_32,
        |x: i64, y| x.wrapping_add(y),
        |x: i64, y| x.wrapping_mul(y),
        |x: i64, y| x / y
    );
    bench_ops!(
        @throughput c,
        "int/i128",
        i128,
        |q: i64| (q as i128) << 48,
        |x: i128, y| x.wrapping_add(y),
        |x: i128, y| x.wrapping_mul(y),
        |x: i128, y| x / y
    );

    let n32 = |q: i64| to_f64(q) as f32;
    bench_ops!(
        c,
        "native/f32",
        f32,
        n32,
        |x, y| x + y,
        |x, y| x * y,
        |x, y| x / y
    );
    bench_ops!(
        c,
        "native/f64",
        f64,
        to_f64,
        |x, y| x + y,
        |x, y| x * y,
        |x, y| x / y
    );
}

macro_rules! bench_combined {
    ($c:expr, $name:literal, $T:ty, $make:expr, mul_add: $mul_add:expr, mul_div: $mul_div:expr, lerp: $lerp:expr, dot: $dot:expr) => {{
        let a: Vec<$T> = values(N, 5, operand, $make);
        let b: Vec<$T> = values(N, 6, operand, $make);
        let d: Vec<$T> = values(N, 7, divisor, $make);
        let t: Vec<$T> = values(N, 8, |x| (x >> 48) as i64, $make);
        let mut out: Vec<$T> = a.clone();
        let dot = $dot;

        let mut g = $c.benchmark_group("throughput");
        g.throughput(Throughput::Elements(N as u64));
        bench_combined!(@each g, out, "mul_add", $name, $mul_add, a, b, d);
        bench_combined!(@each g, out, "mul_div", $name, $mul_div, a, b, d);
        bench_combined!(@each g, out, "lerp", $name, $lerp, a, b, t);
        g.bench_function(BenchmarkId::new("dot", $name), |bn| {
            bn.iter(|| black_box(dot(black_box(&a), black_box(&b))))
        });
        g.finish();
    }};
    (@each $g:ident, $out:ident, $op:literal, $name:literal, $f:expr, $xs:ident, $ys:ident, $zs:ident) => {{
        let f = $f;
        $g.bench_function(BenchmarkId::new($op, $name), |bn| {
            bn.iter(|| {
                let (xs, ys, zs) = (black_box(&$xs), black_box(&$ys), black_box(&$zs));
                for (((o, x), y), z) in $out.iter_mut().zip(xs).zip(ys).zip(zs) {
                    *o = f(*x, *y, *z);
                }
                black_box(&$out);
            })
        });
    }};
}

/// fulcrum: the combined operations and a dot product rounded once.
macro_rules! bench_fulcrum_combined {
    ($c:expr, $name:literal, $T:ident, $make:expr) => {
        bench_combined!(
            $c,
            $name,
            $T,
            $make,
            mul_add: |x: $T, y, z| x.mul_add(y, z),
            mul_div: |x: $T, y, z| x.mul_div(y, z),
            lerp: |x: $T, y, t| x.lerp(y, t),
            dot: |a: &[$T], b: &[$T]| {
                let mut acc = $T::accumulator();
                for (x, y) in a.iter().zip(b) {
                    acc.add_product(*x, *y);
                }
                acc.finish()
            }
        )
    };
}

/// `fixed` with saturating arithmetic: `saturating_mul_add`,
/// `saturating_lerp`, `x * y / z` and a sum of saturating products.
macro_rules! bench_fixed_combined {
    ($c:expr, $name:literal, $T:ident, $make:expr) => {
        bench_combined!(
            $c,
            $name,
            $T,
            $make,
            mul_add: |x: $T, y, z| x.saturating_mul_add(y, z),
            mul_div: |x: $T, y, z| x.saturating_mul(y).saturating_div(z),
            lerp: |x: $T, y, t: $T| t.saturating_lerp(x, y),
            dot: |a: &[$T], b: &[$T]| a
                .iter()
                .zip(b)
                .fold($T::ZERO, |s, (x, y)| s.saturating_add(x.saturating_mul(*y)))
        )
    };
}

/// Plain integers with wrapping arithmetic, the lower bound: `x * y + z`,
/// `x * y / z`, `x + (y - x) * t` and a sum of products.
macro_rules! bench_int_combined {
    ($c:expr, $name:literal, $T:ident, $make:expr) => {
        bench_combined!(
            $c,
            $name,
            $T,
            $make,
            mul_add: |x: $T, y: $T, z| x.wrapping_mul(y).wrapping_add(z),
            mul_div: |x: $T, y: $T, z| x.wrapping_mul(y) / z,
            lerp: |x: $T, y: $T, t| x.wrapping_add(y.wrapping_sub(x).wrapping_mul(t)),
            dot: |a: &[$T], b: &[$T]| a
                .iter()
                .zip(b)
                .fold(0, |s: $T, (x, y)| s.wrapping_add(x.wrapping_mul(*y)))
        )
    };
}

fn combined(c: &mut Criterion) {
    use fixed::types::{I16F16, I32F32};
    bench_fulcrum_combined!(c, "fulcrum/FixedFloat32", FixedFloat32, ff32);
    bench_fulcrum_combined!(c, "fulcrum/FixedFloat64", FixedFloat64, ff64);
    bench_fixed_combined!(c, "fixed-sat/I16F16", I16F16, |q: i64| I16F16::from_bits(
        q as i32
    ));
    bench_fixed_combined!(c, "fixed-sat/I32F32", I32F32, |q: i64| I32F32::from_bits(
        q32_32(q)
    ));
    bench_int_combined!(c, "int/i32", i32, |q: i64| q as i32);
    bench_int_combined!(c, "int/i64", i64, q32_32);
}

/// The six loops of stage 7 over 4096 operands for one implementation; each
/// operation is a function over whole slices.
macro_rules! bench_loops {
    ($c:expr, $name:literal, $T:ty, $Int:ty, $make:expr, add: $add:expr, sub: $sub:expr, mul: $mul:expr, mul_int: $mul_int:expr, mul_add: $mul_add:expr, lerp: $lerp:expr) => {{
        let operands = |seed| -> Vec<$T> { values(N, seed, operand, $make) };
        let (a, b, c) = (operands(13), operands(14), operands(15));
        let n: Vec<$Int> = inputs(N, 16).into_iter().map(|x| ((x >> 60) as i64 - 8) as $Int).collect();
        let mut out = a.clone();
        let mut g = $c.benchmark_group("loops");
        g.throughput(Throughput::Elements(N as u64));
        bench_loops!(@two g, out, "add", $name, $add, a, b);
        bench_loops!(@two g, out, "sub", $name, $sub, a, b);
        bench_loops!(@two g, out, "mul", $name, $mul, a, b);
        bench_loops!(@two g, out, "mul_int", $name, $mul_int, a, n);
        bench_loops!(@three g, out, "mul_add", $name, $mul_add, a, b, c);
        bench_loops!(@three g, out, "lerp", $name, $lerp, a, b, c);
        g.finish();
    }};
    (@two $g:ident, $out:ident, $op:literal, $name:literal, $f:expr, $xs:ident, $ys:ident) => {{
        let f = $f;
        $g.bench_function(BenchmarkId::new($op, $name), |bn| {
            bn.iter(|| {
                f(black_box(&$xs), black_box(&$ys), &mut $out);
                black_box(&$out);
            })
        });
    }};
    (@three $g:ident, $out:ident, $op:literal, $name:literal, $f:expr, $xs:ident, $ys:ident, $zs:ident) => {{
        let f = $f;
        $g.bench_function(BenchmarkId::new($op, $name), |bn| {
            bn.iter(|| {
                f(black_box(&$xs), black_box(&$ys), black_box(&$zs), &mut $out);
                black_box(&$out);
            })
        });
    }};
}

/// `fixed` with saturating arithmetic in the loop shapes of fulcrum.
macro_rules! bench_fixed_loops {
    ($c:expr, $name:literal, $T:ident, $Int:ty, $make:expr) => {
        bench_loops!(
            $c,
            $name,
            $T,
            $Int,
            $make,
            add: |a: &[$T], b: &[$T], o: &mut [$T]| map2(a, b, o, |x, y| x.saturating_add(y)),
            sub: |a: &[$T], b: &[$T], o: &mut [$T]| map2(a, b, o, |x, y| x.saturating_sub(y)),
            mul: |a: &[$T], b: &[$T], o: &mut [$T]| map2(a, b, o, |x, y| x.saturating_mul(y)),
            mul_int: |a: &[$T], n: &[$Int], o: &mut [$T]| map_int(a, n, o, |x, k| x.saturating_mul_int(k)),
            mul_add: |a: &[$T], b: &[$T], c: &[$T], o: &mut [$T]| map3(a, b, c, o, |x, y, z| x.saturating_mul_add(y, z)),
            lerp: |a: &[$T], b: &[$T], t: &[$T], o: &mut [$T]| map3(a, b, t, o, |x, y, z: $T| z.saturating_lerp(x, y))
        )
    };
}

/// Plain integers with wrapping arithmetic and no rounding, the lower bound.
macro_rules! bench_int_loops {
    ($c:expr, $name:literal, $T:ident, $make:expr) => {
        bench_loops!(
            $c,
            $name,
            $T,
            $T,
            $make,
            add: |a: &[$T], b: &[$T], o: &mut [$T]| map2(a, b, o, |x: $T, y| x.wrapping_add(y)),
            sub: |a: &[$T], b: &[$T], o: &mut [$T]| map2(a, b, o, |x: $T, y| x.wrapping_sub(y)),
            mul: |a: &[$T], b: &[$T], o: &mut [$T]| map2(a, b, o, |x: $T, y| x.wrapping_mul(y)),
            mul_int: |a: &[$T], n: &[$T], o: &mut [$T]| map_int(a, n, o, |x: $T, k| x.wrapping_mul(k)),
            mul_add: |a: &[$T], b: &[$T], c: &[$T], o: &mut [$T]| map3(a, b, c, o, |x: $T, y, z| x.wrapping_mul(y).wrapping_add(z)),
            lerp: |a: &[$T], b: &[$T], t: &[$T], o: &mut [$T]| map3(a, b, t, o, |x: $T, y: $T, z| x.wrapping_add(y.wrapping_sub(x).wrapping_mul(z)))
        )
    };
}

fn slice_loops(c: &mut Criterion) {
    use fixed::types::{I16F16, I4F4, I8F8};
    bench_loops!(c, "fulcrum/FixedFloat8", FixedFloat8, i8, ff8, add: loops::add_8, sub: loops::sub_8, mul: loops::mul_8, mul_int: loops::mul_int_8, mul_add: loops::mul_add_8, lerp: loops::lerp_8);
    bench_loops!(c, "fulcrum/FixedFloat16", FixedFloat16, i16, ff16, add: loops::add_16, sub: loops::sub_16, mul: loops::mul_16, mul_int: loops::mul_int_16, mul_add: loops::mul_add_16, lerp: loops::lerp_16);
    bench_loops!(c, "fulcrum/FixedFloat32", FixedFloat32, i32, ff32, add: loops::add_32, sub: loops::sub_32, mul: loops::mul_32, mul_int: loops::mul_int_32, mul_add: loops::mul_add_32, lerp: loops::lerp_32);
    bench_fixed_loops!(c, "fixed-sat/I4F4", I4F4, i8, |q: i64| I4F4::from_bits(
        (q >> 12) as i8
    ));
    bench_fixed_loops!(c, "fixed-sat/I8F8", I8F8, i16, |q: i64| I8F8::from_bits(
        (q >> 8) as i16
    ));
    bench_fixed_loops!(c, "fixed-sat/I16F16", I16F16, i32, |q: i64| {
        I16F16::from_bits(q as i32)
    });
    bench_int_loops!(c, "int/i16", i16, |q: i64| (q >> 8) as i16);
    bench_int_loops!(c, "int/i32", i32, |q: i64| q as i32);
}

/// One root function over 4096 operands for each implementation.
macro_rules! bench_roots {
    ($c:expr, $name:literal, $T:ty, $make:expr, sqrt: $sqrt:expr, rsqrt: $rsqrt:expr, hypot: $hypot:expr) => {{
        let a: Vec<$T> = values(N, 9, radicand, $make);
        let b: Vec<$T> = values(N, 10, radicand, $make);
        let mut out: Vec<$T> = a.clone();
        let (sqrt, rsqrt, hypot) = ($sqrt, $rsqrt, $hypot);
        let mut g = $c.benchmark_group("throughput");
        g.throughput(Throughput::Elements(N as u64));
        g.bench_function(BenchmarkId::new("sqrt", $name), |bn| {
            bn.iter(|| {
                for (o, x) in out.iter_mut().zip(black_box(&a)) {
                    *o = sqrt(*x);
                }
                black_box(&out);
            })
        });
        g.bench_function(BenchmarkId::new("rsqrt", $name), |bn| {
            bn.iter(|| {
                for (o, x) in out.iter_mut().zip(black_box(&a)) {
                    *o = rsqrt(*x);
                }
                black_box(&out);
            })
        });
        g.bench_function(BenchmarkId::new("hypot", $name), |bn| {
            bn.iter(|| {
                let (a, b) = (black_box(&a), black_box(&b));
                for ((o, x), y) in out.iter_mut().zip(a).zip(b) {
                    *o = hypot(*x, *y);
                }
                black_box(&out);
            })
        });
        g.finish();
    }};
}

fn roots(c: &mut Criterion) {
    bench_roots!(c, "fulcrum/FixedFloat32", FixedFloat32, ff32,
        sqrt: |x: FixedFloat32| x.sqrt(), rsqrt: |x: FixedFloat32| x.rsqrt(), hypot: |x: FixedFloat32, y| x.hypot(y));
    bench_roots!(c, "fulcrum/FixedFloat64", FixedFloat64, ff64,
        sqrt: |x: FixedFloat64| x.sqrt(), rsqrt: |x: FixedFloat64| x.rsqrt(), hypot: |x: FixedFloat64, y| x.hypot(y));
    let n32 = |q: i64| to_f64(q) as f32;
    bench_roots!(c, "libm/f32", f32, n32,
        sqrt: libm::sqrtf, rsqrt: |x: f32| 1.0 / libm::sqrtf(x), hypot: libm::hypotf);
    bench_roots!(c, "libm/f64", f64, to_f64,
        sqrt: libm::sqrt, rsqrt: |x: f64| 1.0 / libm::sqrt(x), hypot: libm::hypot);
    bench_roots!(c, "native/f32", f32, n32,
        sqrt: |x: f32| x.sqrt(), rsqrt: |x: f32| 1.0 / x.sqrt(), hypot: |x: f32, y| x.hypot(y));
    bench_roots!(c, "native/f64", f64, to_f64,
        sqrt: |x: f64| x.sqrt(), rsqrt: |x: f64| 1.0 / x.sqrt(), hypot: |x: f64, y| x.hypot(y));
}

/// One benchmark of a function of one or two operands over 4096 values.
fn bench_trig_one<T: Copy, U: Copy, R: Clone + Default>(
    g: &mut criterion::BenchmarkGroup<criterion::measurement::WallTime>,
    op: &str,
    name: &str,
    a: &[T],
    b: &[U],
    f: impl Fn(T, U) -> R,
) {
    let mut out: Vec<R> = vec![R::default(); a.len()];
    g.bench_function(BenchmarkId::new(op, name), |bn| {
        bn.iter(|| {
            let (a, b) = (black_box(a), black_box(b));
            for ((o, x), y) in out.iter_mut().zip(a).zip(b) {
                *o = f(*x, *y);
            }
            black_box(&out);
        })
    });
}

/// The trigonometric functions of one implementation; `turns` is absent
/// for `cordic`.
macro_rules! bench_trig {
    ($c:expr, $name:literal, $T:ty, $make:expr, $unit:expr,
     $(turns: ($sin_turns:expr, $cos_turns:expr),)?
     sin: $sin:expr, cos: $cos:expr, tan: $tan:expr, atan: $atan:expr,
     atan2: $atan2:expr, asin: $asin:expr, acos: $acos:expr) => {{
        let make = $make;
        let unit = $unit;
        let a: Vec<$T> = values(N, 11, operand, &make);
        let b: Vec<$T> = values(N, 12, operand, &make);
        let u: Vec<$T> = values(N, 13, operand, &unit);
        let mut g = $c.benchmark_group("throughput");
        g.throughput(Throughput::Elements(N as u64));
        $(
            let (st, ct) = ($sin_turns, $cos_turns);
            bench_trig_one(&mut g, "sin_turns", $name, &a, &b, |x: $T, _| st(x));
            bench_trig_one(&mut g, "cos_turns", $name, &a, &b, |x: $T, _| ct(x));
        )?
        let (sin, cos, tan, atan, atan2, asin, acos) = ($sin, $cos, $tan, $atan, $atan2, $asin, $acos);
        bench_trig_one(&mut g, "sin", $name, &a, &b, |x: $T, _| sin(x));
        bench_trig_one(&mut g, "cos", $name, &a, &b, |x: $T, _| cos(x));
        bench_trig_one(&mut g, "tan", $name, &a, &b, |x: $T, _| tan(x));
        bench_trig_one(&mut g, "atan", $name, &a, &b, |x: $T, _| atan(x));
        bench_trig_one(&mut g, "atan2", $name, &a, &b, |y: $T, x: $T| atan2(y, x));
        bench_trig_one(&mut g, "asin", $name, &u, &b, |x: $T, _| asin(x));
        bench_trig_one(&mut g, "acos", $name, &u, &b, |x: $T, _| acos(x));
        g.finish();
    }};
}

fn trig(c: &mut Criterion) {
    use fixed::types::{I16F16, I32F32};
    use std::f64::consts::TAU;
    let half32 = |q: i64| ff32(q / 2);
    let half64 = |q: i64| ff64(q / 2);
    bench_trig!(c, "fulcrum/FixedFloat32", FixedFloat32, ff32, half32,
        turns: (|x: FixedFloat32| x.sin_turns(), |x: FixedFloat32| x.cos_turns()),
        sin: |x: FixedFloat32| x.sin(), cos: |x: FixedFloat32| x.cos(), tan: |x: FixedFloat32| x.tan(),
        atan: |x: FixedFloat32| x.atan(), atan2: |y: FixedFloat32, x| y.atan2(x),
        asin: |x: FixedFloat32| x.asin(), acos: |x: FixedFloat32| x.acos());
    bench_trig!(c, "fulcrum/FixedFloat64", FixedFloat64, ff64, half64,
        turns: (|x: FixedFloat64| x.sin_turns(), |x: FixedFloat64| x.cos_turns()),
        sin: |x: FixedFloat64| x.sin(), cos: |x: FixedFloat64| x.cos(), tan: |x: FixedFloat64| x.tan(),
        atan: |x: FixedFloat64| x.atan(), atan2: |y: FixedFloat64, x| y.atan2(x),
        asin: |x: FixedFloat64| x.asin(), acos: |x: FixedFloat64| x.acos());
    let n32 = |q: i64| to_f64(q) as f32;
    let u32f = |q: i64| to_f64(q / 2) as f32;
    let u64f = |q: i64| to_f64(q / 2);
    bench_trig!(c, "libm/f32", f32, n32, u32f,
        turns: (|x: f32| libm::sinf(x * TAU as f32), |x: f32| libm::cosf(x * TAU as f32)),
        sin: libm::sinf, cos: libm::cosf, tan: libm::tanf, atan: libm::atanf,
        atan2: libm::atan2f, asin: libm::asinf, acos: libm::acosf);
    bench_trig!(c, "libm/f64", f64, to_f64, u64f,
        turns: (|x: f64| libm::sin(x * TAU), |x: f64| libm::cos(x * TAU)),
        sin: libm::sin, cos: libm::cos, tan: libm::tan, atan: libm::atan,
        atan2: libm::atan2, asin: libm::asin, acos: libm::acos);
    bench_trig!(c, "native/f32", f32, n32, u32f,
        turns: (|x: f32| (x * TAU as f32).sin(), |x: f32| (x * TAU as f32).cos()),
        sin: |x: f32| x.sin(), cos: |x: f32| x.cos(), tan: |x: f32| x.tan(), atan: |x: f32| x.atan(),
        atan2: |y: f32, x| y.atan2(x), asin: |x: f32| x.asin(), acos: |x: f32| x.acos());
    bench_trig!(c, "native/f64", f64, to_f64, u64f,
        turns: (|x: f64| (x * TAU).sin(), |x: f64| (x * TAU).cos()),
        sin: |x: f64| x.sin(), cos: |x: f64| x.cos(), tan: |x: f64| x.tan(), atan: |x: f64| x.atan(),
        atan2: |y: f64, x| y.atan2(x), asin: |x: f64| x.asin(), acos: |x: f64| x.acos());
    let c16 = |q: i64| I16F16::from_bits(q as i32);
    let c16u = |q: i64| I16F16::from_bits((q / 2) as i32);
    let c32 = |q: i64| I32F32::from_bits(q32_32(q));
    let c32u = |q: i64| I32F32::from_bits(q32_32(q / 2));
    bench_trig!(c, "cordic/I16F16", I16F16, c16, c16u,
        sin: cordic::sin::<I16F16>, cos: cordic::cos::<I16F16>, tan: cordic::tan::<I16F16>,
        atan: cordic::atan::<I16F16>, atan2: cordic::atan2::<I16F16>,
        asin: cordic::asin::<I16F16>, acos: cordic::acos::<I16F16>);
    bench_trig!(c, "cordic/I32F32", I32F32, c32, c32u,
        sin: cordic::sin::<I32F32>, cos: cordic::cos::<I32F32>, tan: cordic::tan::<I32F32>,
        atan: cordic::atan::<I32F32>, atan2: cordic::atan2::<I32F32>,
        asin: cordic::asin::<I32F32>, acos: cordic::acos::<I32F32>);
}

/// The exponentials and logarithms of one implementation; `cordic` has only
/// `exp`.
macro_rules! bench_exp_log {
    ($c:expr, $name:literal, $T:ty, $make:expr,
     $(log2: $log2:expr, exp2: $exp2:expr, ln: $ln:expr,)?
     exp: $exp:expr
     $(, pow: $pow:expr, powi: $powi:expr)?) => {{
        let make = $make;
        let a: Vec<$T> = values(N, 14, operand, &make);
        let mut gr = $c.benchmark_group("throughput");
        gr.throughput(Throughput::Elements(N as u64));
        $(
            let p: Vec<$T> = values(N, 15, radicand, &make);
            let (log2, exp2, ln) = ($log2, $exp2, $ln);
            bench_trig_one(&mut gr, "log2", $name, &p, &a, |x: $T, _| log2(x));
            bench_trig_one(&mut gr, "exp2", $name, &a, &a, |x: $T, _| exp2(x));
            bench_trig_one(&mut gr, "ln", $name, &p, &a, |x: $T, _| ln(x));
        )?
        let exp = $exp;
        bench_trig_one(&mut gr, "exp", $name, &a, &a, |x: $T, _| exp(x));
        $(
            let g: Vec<$T> = values(N, 16, |x| (radicand(x) >> 6) | 1, &make);
            let n: Vec<i32> = inputs(N, 17).into_iter().map(|x| (x % 17) as i32 - 8).collect();
            let (pow, powi) = ($pow, $powi);
            bench_trig_one(&mut gr, "pow", $name, &g, &a, |x: $T, y: $T| pow(x, y));
            bench_trig_one(&mut gr, "powi", $name, &a, &n, |x: $T, k: i32| powi(x, k));
        )?
        gr.finish();
    }};
}

fn exp_log(c: &mut Criterion) {
    use fixed::types::{I16F16, I32F32};
    bench_exp_log!(c, "fulcrum/FixedFloat32", FixedFloat32, ff32,
        log2: |x: FixedFloat32| x.log2(), exp2: |x: FixedFloat32| x.exp2(), ln: |x: FixedFloat32| x.ln(),
        exp: |x: FixedFloat32| x.exp(),
        pow: |x: FixedFloat32, y| x.pow(y), powi: |x: FixedFloat32, n| x.powi(n));
    bench_exp_log!(c, "fulcrum/FixedFloat64", FixedFloat64, ff64,
        log2: |x: FixedFloat64| x.log2(), exp2: |x: FixedFloat64| x.exp2(), ln: |x: FixedFloat64| x.ln(),
        exp: |x: FixedFloat64| x.exp(),
        pow: |x: FixedFloat64, y| x.pow(y), powi: |x: FixedFloat64, n| x.powi(n));
    let n32 = |q: i64| to_f64(q) as f32;
    bench_exp_log!(c, "libm/f32", f32, n32,
        log2: libm::log2f, exp2: libm::exp2f, ln: libm::logf,
        exp: libm::expf,
        pow: libm::powf, powi: |x: f32, n: i32| libm::powf(x, n as f32));
    bench_exp_log!(c, "libm/f64", f64, to_f64,
        log2: libm::log2, exp2: libm::exp2, ln: libm::log,
        exp: libm::exp,
        pow: libm::pow, powi: |x: f64, n: i32| libm::pow(x, f64::from(n)));
    bench_exp_log!(c, "native/f32", f32, n32,
        log2: |x: f32| x.log2(), exp2: |x: f32| x.exp2(), ln: |x: f32| x.ln(),
        exp: |x: f32| x.exp(),
        pow: |x: f32, y| x.powf(y), powi: |x: f32, n| x.powi(n));
    bench_exp_log!(c, "native/f64", f64, to_f64,
        log2: |x: f64| x.log2(), exp2: |x: f64| x.exp2(), ln: |x: f64| x.ln(),
        exp: |x: f64| x.exp(),
        pow: |x: f64, y| x.powf(y), powi: |x: f64, n| x.powi(n));
    bench_exp_log!(c, "cordic/I16F16", I16F16, |q: i64| I16F16::from_bits(q as i32),
        exp: cordic::exp::<I16F16>);
    bench_exp_log!(c, "cordic/I32F32", I32F32, |q: i64| I32F32::from_bits(q32_32(q)),
        exp: cordic::exp::<I32F32>);
}

/// The vector functions of one implementation over 4096 pairs of vectors:
/// `Vec2` and `Vec3`, coordinates in `[-2, 2)`, length bounds in `[0.5, 1.5]`.
macro_rules! bench_vectors {
    ($c:expr, $name:literal, $V:ty, $V3:ty, $A:ty, $vector:expr, $vector3:expr, $angle:expr,
     dot: $dot:expr, length: $length:expr, normalize: $normalize:expr,
     distance_sq: $distance_sq:expr, rotate: $rotate:expr, angle_to: $angle_to:expr,
     clamp_length: $clamp_length:expr,
     cross3: $cross3:expr, length3: $length3:expr, normalize3: $normalize3:expr) => {{
        let (vector, vector3, angle) = ($vector, $vector3, $angle);
        let r = inputs(9 * N, 21);
        let o = |i: usize| operand(r[i]);
        let a: Vec<$V> = (0..N).map(|i| vector(o(9 * i), o(9 * i + 1))).collect();
        let b: Vec<$V> = (0..N).map(|i| vector(o(9 * i + 2), o(9 * i + 3))).collect();
        let t: Vec<$A> = (0..N).map(|i| angle(r[9 * i + 4])).collect();
        let a3: Vec<$V3> = (0..N)
            .map(|i| vector3(o(9 * i), o(9 * i + 1), o(9 * i + 5)))
            .collect();
        let b3: Vec<$V3> = (0..N)
            .map(|i| vector3(o(9 * i + 6), o(9 * i + 7), o(9 * i + 8)))
            .collect();
        let mut g = $c.benchmark_group("throughput");
        g.throughput(Throughput::Elements(N as u64));
        let (dot, length, normalize, distance_sq, rotate) =
            ($dot, $length, $normalize, $distance_sq, $rotate);
        let (angle_to, clamp_length) = ($angle_to, $clamp_length);
        let (cross3, length3, normalize3) = ($cross3, $length3, $normalize3);
        bench_trig_one(&mut g, "vec_dot", $name, &a, &b, |x: $V, y: $V| dot(x, y));
        bench_trig_one(&mut g, "vec_length", $name, &a, &b, |x: $V, _| length(x));
        bench_trig_one(&mut g, "vec_normalize", $name, &a, &b, |x: $V, _| {
            normalize(x)
        });
        bench_trig_one(&mut g, "vec_distance_sq", $name, &a, &b, |x: $V, y: $V| {
            distance_sq(x, y)
        });
        bench_trig_one(&mut g, "vec_angle_to", $name, &a, &b, |x: $V, y: $V| {
            angle_to(x, y)
        });
        bench_trig_one(&mut g, "vec_clamp_length", $name, &a, &b, |x: $V, _| {
            clamp_length(x)
        });
        let pairs: Vec<($V, $A)> = a.iter().copied().zip(t.iter().copied()).collect();
        bench_trig_one(
            &mut g,
            "vec_rotate",
            $name,
            &pairs,
            &pairs,
            |p: ($V, $A), _| rotate(p.0, p.1),
        );
        bench_trig_one(&mut g, "vec3_cross", $name, &a3, &b3, |x: $V3, y: $V3| {
            cross3(x, y)
        });
        bench_trig_one(&mut g, "vec3_length", $name, &a3, &b3, |x: $V3, _| {
            length3(x)
        });
        bench_trig_one(&mut g, "vec3_normalize", $name, &a3, &b3, |x: $V3, _| {
            normalize3(x)
        });
        g.finish();
    }};
}

/// The vector functions of fulcrum on one type `$T` with its angle type
/// `$A`, made from Q16.16 by `$q`.
macro_rules! bench_fulcrum_vectors {
    ($c:expr, $name:literal, $T:ty, $A:ty, $q:expr, $angle:expr) => {{
        use fulcrum::{Vec2, Vec3};
        let q = $q;
        let (lo, hi) = (q(1 << 15), q(3 << 15));
        bench_vectors!($c, $name, Vec2<$T>, Vec3<$T>, $A,
            move |x, y| Vec2::new(q(x), q(y)), move |x, y, z| Vec3::new(q(x), q(y), q(z)), $angle,
            dot: |a: Vec2<$T>, b| a.dot(b), length: |a: Vec2<$T>| a.length(),
            normalize: |a: Vec2<$T>| a.normalize(),
            distance_sq: |a: Vec2<$T>, b| a.distance_sq(b),
            rotate: |a: Vec2<$T>, t| a.rotate(t),
            angle_to: |a: Vec2<$T>, b| a.angle_to(b),
            clamp_length: move |a: Vec2<$T>| a.clamp_length(lo, hi),
            cross3: |a: Vec3<$T>, b| a.cross(b), length3: |a: Vec3<$T>| a.length(),
            normalize3: |a: Vec3<$T>| a.normalize());
    }};
}

fn vectors(c: &mut Criterion) {
    use fulcrum::{Angle32, Angle64};
    bench_fulcrum_vectors!(
        c,
        "fulcrum/FixedFloat32",
        FixedFloat32,
        Angle32,
        ff32,
        |r: u64| Angle32::from_bits(r as u32)
    );
    bench_fulcrum_vectors!(
        c,
        "fulcrum/FixedFloat64",
        FixedFloat64,
        Angle64,
        ff64,
        |r: u64| Angle64::from_bits(r)
    );
    let f = |q: i64| to_f64(q) as f32;
    bench_vectors!(c, "glam/f32", glam::Vec2, glam::Vec3, f32,
        |x, y| glam::Vec2::new(f(x), f(y)), |x, y, z| glam::Vec3::new(f(x), f(y), f(z)),
        |r: u64| (r >> 40) as f32 / (1u64 << 24) as f32 * std::f32::consts::TAU,
        dot: |a: glam::Vec2, b| a.dot(b), length: |a: glam::Vec2| a.length(),
        normalize: |a: glam::Vec2| a.normalize_or_zero(),
        distance_sq: |a: glam::Vec2, b| a.distance_squared(b),
        rotate: |a: glam::Vec2, t: f32| glam::Vec2::from_angle(t).rotate(a),
        angle_to: |a: glam::Vec2, b| a.angle_to(b),
        clamp_length: |a: glam::Vec2| a.clamp_length(0.5, 1.5),
        cross3: |a: glam::Vec3, b| a.cross(b), length3: |a: glam::Vec3| a.length(),
        normalize3: |a: glam::Vec3| a.normalize_or_zero());
}

/// One tick of `fulcrum_bench::tick` per iteration from a fresh starting
/// state (built outside the measurement), reported per unit.
fn tick(c: &mut Criterion) {
    use criterion::BatchSize;
    use fulcrum_bench::tick;
    let mut g = c.benchmark_group("tick");
    g.throughput(Throughput::Elements(tick::UNITS as u64));
    g.bench_function(BenchmarkId::new("one", "fulcrum/FixedFloat32"), |bn| {
        bn.iter_batched_ref(
            tick::fulcrum32,
            |u| tick::fulcrum(u, ff32),
            BatchSize::LargeInput,
        )
    });
    g.bench_function(BenchmarkId::new("one", "fulcrum/FixedFloat64"), |bn| {
        bn.iter_batched_ref(
            tick::fulcrum64,
            |u| tick::fulcrum(u, ff64),
            BatchSize::LargeInput,
        )
    });
    g.bench_function(BenchmarkId::new("one", "fixed-sat/I16F16"), |bn| {
        bn.iter_batched_ref(tick::fixed16_units, tick::fixed16, BatchSize::LargeInput)
    });
    g.bench_function(BenchmarkId::new("one", "fixed-sat/I32F32"), |bn| {
        bn.iter_batched_ref(tick::fixed32_units, tick::fixed32, BatchSize::LargeInput)
    });
    g.bench_function(BenchmarkId::new("one", "glam/f32"), |bn| {
        bn.iter_batched_ref(tick::glam_units, tick::glam, BatchSize::LargeInput)
    });
    g.finish();
}

criterion_group!(
    benches,
    ops,
    combined,
    slice_loops,
    roots,
    trig,
    exp_log,
    vectors,
    tick
);
criterion_main!(benches);
