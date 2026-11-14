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

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use fulcrum::{FixedFloat16, FixedFloat32, FixedFloat64, FixedFloat8};
use fulcrum_bench::inputs;
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
        let a: Vec<$T> = inputs(N, 1)
            .into_iter()
            .map(|x| $make(operand(x)))
            .collect();
        let b: Vec<$T> = inputs(N, 2)
            .into_iter()
            .map(|x| $make(divisor(x)))
            .collect();
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

fn operand(x: u64) -> i64 {
    ((x >> 40) as i64 & ((1 << 18) - 1)) - (1 << 17)
}

fn divisor(x: u64) -> i64 {
    let m = (1 << 15) + ((x >> 40) as i64 % (3 << 15));
    if x & 1 == 0 {
        m
    } else {
        -m
    }
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
    let f8 = |q: i64| FixedFloat8::from_bits((q >> 12) as i8);
    let f16 = |q: i64| FixedFloat16::from_bits((q >> 8) as i16);

    bench_ops!(
        c,
        "fulcrum/FixedFloat8",
        FixedFloat8,
        f8,
        |x, y| x + y,
        |x, y| x * y,
        |x, y| x / y
    );
    bench_ops!(
        c,
        "fulcrum/FixedFloat16",
        FixedFloat16,
        f16,
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
        let a: Vec<$T> = inputs(N, 5).into_iter().map(|x| $make(operand(x))).collect();
        let b: Vec<$T> = inputs(N, 6).into_iter().map(|x| $make(operand(x))).collect();
        let d: Vec<$T> = inputs(N, 7).into_iter().map(|x| $make(divisor(x))).collect();
        let t: Vec<$T> = inputs(N, 8).into_iter().map(|x| $make((x >> 48) as i64)).collect();
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

/// A Q16.16 raw operand as a Q32.32 raw value.
fn q32_32(q: i64) -> i64 {
    q << 16
}

fn ff32(q: i64) -> FixedFloat32 {
    FixedFloat32::from_bits(q as i32)
}

fn ff64(q: i64) -> FixedFloat64 {
    FixedFloat64::from_bits(q32_32(q))
}

criterion_group!(benches, ops, combined);
criterion_main!(benches);
