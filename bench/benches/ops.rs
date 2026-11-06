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

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use fulcrum::{FixedFloat16, FixedFloat32, FixedFloat64, FixedFloat8};
use fulcrum_bench::inputs;
use std::hint::black_box;

const N: usize = 4096;
const CHAIN: usize = 1024;

macro_rules! bench_ops {
    ($c:expr, $name:literal, $T:ty, $make:expr, $add:expr, $mul:expr, $div:expr) => {{
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
        let (mul_start, mul_chain) = bounded_chain($make, mul, 3);
        let (div_start, div_chain) = bounded_chain($make, div, 4);

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
    let f32_ = |q: i64| FixedFloat32::from_bits(q as i32);
    let f64_ = |q: i64| FixedFloat64::from_bits(q << 16);

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
        f32_,
        |x, y| x + y,
        |x, y| x * y,
        |x, y| x / y
    );
    bench_ops!(
        c,
        "fulcrum/FixedFloat64",
        FixedFloat64,
        f64_,
        |x, y| x + y,
        |x, y| x * y,
        |x, y| x / y
    );

    let i8f8 = |q: i64| I8F8::from_bits((q >> 8) as i16);
    let i16f16 = |q: i64| I16F16::from_bits(q as i32);
    let i32f32 = |q: i64| I32F32::from_bits(q << 16);
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

criterion_group!(benches, ops);
criterion_main!(benches);
