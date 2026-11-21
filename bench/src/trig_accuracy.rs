//! Accuracy of the trigonometric functions: fulcrum, the `std` and `libm`
//! floats rounded into the same fixed-point format, and the `cordic` crate on
//! the `fixed` type of the same format, measured against the interval oracle
//! of `fulcrum_oracle` (256 bits).
//!
//! The exact value is clamped to the range of the format, as fulcrum
//! saturates `tan`; the error of a raw result `r` is its distance to the
//! middle of the oracle interval, in ulps, and `r` is correctly rounded when
//! it is the value with `F` fractional bits nearest to every point of the
//! interval. Operands are angles in `[-2, 2)` (radians, or turns for
//! `sin_turns` and `cos_turns`, where the floats compute `sin(τ·x)` and
//! `cos(τ·x)`), `[-1, 1)` for `asin` and
//! `acos`, and pairs of angles for `atan2`.

use crate::inputs;
use fixed::types::{I16F16, I32F32};
use fulcrum::{FixedFloat32, FixedFloat64};
use fulcrum_oracle as oracle;
use num_bigint::BigInt;
use num_traits::{One, Signed, ToPrimitive};
use std::f64::consts::TAU;

pub use crate::accuracy::Accuracy;
use crate::accuracy::{round_float, Tally};

/// The functions of the table, in order.
pub const OPS: [&str; 9] = [
    "sin_turns",
    "cos_turns",
    "sin",
    "cos",
    "tan",
    "atan",
    "atan2",
    "asin",
    "acos",
];

/// The implementations of the table, in order; `cordic` has no functions in
/// turns.
pub const IMPS: [&str; 4] = ["fulcrum", "std", "libm", "cordic"];

/// One row: a function on one format, the accuracy of each implementation of
/// [`IMPS`] that has it.
pub struct Row {
    /// One of [`OPS`].
    pub op: &'static str,
    /// `Q16.16` or `Q32.32`.
    pub format: &'static str,
    /// One entry per implementation of [`IMPS`], `None` where it is absent.
    pub cells: [Option<Accuracy>; 4],
}

/// The oracle interval of one result, clamped to the format, and the values
/// of the format that round it: one when the interval decides the rounding.
pub(crate) struct Exact {
    lo: BigInt,
    hi: BigInt,
    frac: u32,
    nearest: Vec<i128>,
}

impl Exact {
    pub(crate) fn new((lo, hi): (BigInt, BigInt), frac: u32, bits: u32) -> Self {
        let shift = oracle::TRIG_SCALE - frac;
        let (lo, hi) = oracle::Format { bits, frac }.clamp((lo, hi));
        let half = BigInt::one() << (shift - 1);
        let round = |v: &BigInt| ((v + &half) >> shift).to_i128().unwrap();
        let mut nearest = vec![round(&lo)];
        if round(&hi) != nearest[0] {
            nearest.push(round(&hi));
        }
        Self {
            lo,
            hi,
            frac,
            nearest,
        }
    }

    /// The error of the raw result `r` in ulps, its distance to the middle
    /// of the interval, and whether `r` is correctly rounded.
    fn error(&self, r: i128) -> (f64, bool) {
        let shift = oracle::TRIG_SCALE - self.frac;
        let got = BigInt::from(r) << shift;
        let mid: BigInt = (&self.lo + &self.hi) >> 1u32;
        let diff = (&got - &mid).abs() >> (shift - 32);
        let err = diff.to_f64().unwrap_or(f64::INFINITY) / 4_294_967_296.0;
        (err, self.nearest.contains(&r))
    }
}

/// An interval far above the range of a format with `bits` bits, clamped
/// to `MAX` by [`Exact`].
pub(crate) fn huge(bits: u32) -> (BigInt, BigInt) {
    let big = BigInt::one() << (oracle::TRIG_SCALE + bits);
    (big.clone(), big)
}

/// The accuracy of each implementation of [`IMPS`] that `has` the function,
/// where `eval(imp, a, b)` is its raw result at the operands `(a, b)`.
pub(crate) fn cells(
    args: &[(i128, i128)],
    exact: &[Exact],
    has: impl Fn(&str) -> bool,
    eval: impl Fn(&str, i128, i128) -> i128,
) -> [Option<Accuracy>; 4] {
    let mut cells = [None, None, None, None];
    for (k, imp) in IMPS.iter().enumerate() {
        if !has(imp) {
            continue;
        }
        let mut t = Tally::new();
        for (&(a, b), e) in args.iter().zip(exact) {
            let (err, correct) = e.error(eval(imp, a, b));
            t.record(err, correct);
        }
        cells[k] = Some(t.done());
    }
    cells
}

/// The exact value of `op` at raw operands `a` (and `b` for `atan2`).
fn exact(op: &str, a: i128, b: i128, frac: u32, bits: u32) -> Exact {
    let v = match op {
        "sin_turns" => oracle::sin_turns(a, frac),
        "cos_turns" => oracle::sin_turns(a + (1 << (frac - 2)), frac),
        "sin" => oracle::sin(a, frac),
        "cos" => oracle::cos(a, frac),
        "tan" => oracle::tan(a, frac).unwrap_or_else(|| huge(bits)),
        "atan" => oracle::atan(a, frac),
        "atan2" => oracle::atan2(a, b),
        "asin" => oracle::asin(a, frac),
        _ => oracle::acos(a, frac),
    };
    Exact::new(v, frac, bits)
}

/// Raw operands of a format with `frac` fractional bits in `[-2^k, 2^k)`.
pub(crate) fn operands(n: usize, seed: u64, frac: u32, k: u32) -> Vec<i128> {
    inputs(n, seed)
        .into_iter()
        .map(|x| ((x as i64) >> (63 - frac - k)) as i128)
        .collect()
}

/// The row of one function on one format.
fn row(samples: usize, op: &'static str, format: &'static str, frac: u32, bits: u32) -> Row {
    let angles = operands(samples, 31, frac, 1);
    let others = operands(samples, 32, frac, 1);
    let units = operands(samples, 33, frac, 0);
    let scale = (1u64 << frac) as f64;
    let f = |raw: i128| raw as f64 / scale;
    {
        let args: Vec<(i128, i128)> = match op {
            "asin" | "acos" => units.iter().map(|&a| (a, 0)).collect(),
            "atan2" => angles.iter().zip(&others).map(|(&a, &b)| (a, b)).collect(),
            _ => angles.iter().map(|&a| (a, 0)).collect(),
        };
        let exact: Vec<Exact> = args
            .iter()
            .map(|&(a, b)| exact(op, a, b, frac, bits))
            .collect();
        let has = |imp: &str| imp != "cordic" || (op != "sin_turns" && op != "cos_turns");
        let cells = cells(&args, &exact, has, |imp, a, b| match imp {
            "fulcrum" => fulcrum(op, a, b, bits),
            "cordic" => cordic(op, a, b, bits),
            _ => round_float(float(op, f(a), f(b), imp == "std", bits), frac, bits),
        });
        Row { op, format, cells }
    }
}

fn fulcrum(op: &str, a: i128, b: i128, bits: u32) -> i128 {
    macro_rules! call {
        ($T:ident, $Raw:ty) => {{
            let (x, y) = ($T::from_bits(a as $Raw), $T::from_bits(b as $Raw));
            let r = match op {
                "sin_turns" => x.sin_turns(),
                "cos_turns" => x.cos_turns(),
                "sin" => x.sin(),
                "cos" => x.cos(),
                "tan" => x.tan(),
                "atan" => x.atan(),
                "atan2" => x.atan2(y),
                "asin" => x.asin(),
                _ => x.acos(),
            };
            r.to_bits() as i128
        }};
    }
    if bits == 32 {
        call!(FixedFloat32, i32)
    } else {
        call!(FixedFloat64, i64)
    }
}

fn cordic(op: &str, a: i128, b: i128, bits: u32) -> i128 {
    macro_rules! call {
        ($T:ident, $Raw:ty) => {{
            let (x, y) = ($T::from_bits(a as $Raw), $T::from_bits(b as $Raw));
            let r = match op {
                "sin" => cordic::sin(x),
                "cos" => cordic::cos(x),
                "tan" => cordic::tan(x),
                "atan" => cordic::atan(x),
                "atan2" => cordic::atan2(x, y),
                "asin" => cordic::asin(x),
                _ => cordic::acos(x),
            };
            r.to_bits() as i128
        }};
    }
    if bits == 32 {
        call!(I16F16, i32)
    } else {
        call!(I32F32, i64)
    }
}

/// The float result: `f32` for 32-bit formats, `f64` for 64-bit ones.
fn float(op: &str, x: f64, y: f64, std: bool, bits: u32) -> f64 {
    if bits == 32 {
        let (x, y) = (x as f32, y as f32);
        let tau = TAU as f32;
        (match (op, std) {
            ("sin_turns", true) => (x * tau).sin(),
            ("sin_turns", false) => libm::sinf(x * tau),
            ("cos_turns", true) => (x * tau).cos(),
            ("cos_turns", false) => libm::cosf(x * tau),
            ("sin", true) => x.sin(),
            ("sin", false) => libm::sinf(x),
            ("cos", true) => x.cos(),
            ("cos", false) => libm::cosf(x),
            ("tan", true) => x.tan(),
            ("tan", false) => libm::tanf(x),
            ("atan", true) => x.atan(),
            ("atan", false) => libm::atanf(x),
            ("atan2", true) => x.atan2(y),
            ("atan2", false) => libm::atan2f(x, y),
            ("asin", true) => x.asin(),
            ("asin", false) => libm::asinf(x),
            (_, true) => x.acos(),
            (_, false) => libm::acosf(x),
        }) as f64
    } else {
        match (op, std) {
            ("sin_turns", true) => (x * TAU).sin(),
            ("sin_turns", false) => libm::sin(x * TAU),
            ("cos_turns", true) => (x * TAU).cos(),
            ("cos_turns", false) => libm::cos(x * TAU),
            ("sin", true) => x.sin(),
            ("sin", false) => libm::sin(x),
            ("cos", true) => x.cos(),
            ("cos", false) => libm::cos(x),
            ("tan", true) => x.tan(),
            ("tan", false) => libm::tan(x),
            ("atan", true) => x.atan(),
            ("atan", false) => libm::atan(x),
            ("atan2", true) => x.atan2(y),
            ("atan2", false) => libm::atan2(x, y),
            ("asin", true) => x.asin(),
            ("asin", false) => libm::asin(x),
            (_, true) => x.acos(),
            (_, false) => libm::acos(x),
        }
    }
}

/// The table: every function of [`OPS`] on `Q16.16` (against `f32`) and
/// `Q32.32` (against `f64`), on `samples` operands each, one thread per row.
pub fn table(samples: usize) -> Vec<Row> {
    let formats = [("Q16.16", 16, 32), ("Q32.32", 32, 64)];
    std::thread::scope(|s| {
        let handles: Vec<_> = formats
            .iter()
            .flat_map(|&(format, frac, bits)| OPS.iter().map(move |&op| (op, format, frac, bits)))
            .map(|(op, format, frac, bits)| s.spawn(move || row(samples, op, format, frac, bits)))
            .collect();
        handles.into_iter().map(|h| h.join().unwrap()).collect()
    })
}

#[cfg(test)]
mod tests {
    /// fulcrum is within 1 ulp on every sample and correctly rounded on every
    /// sample of `Q16.16`, as the exhaustive tests show; every other
    /// implementation is measured.
    #[test]
    fn fulcrum_within_one_ulp() {
        for row in super::table(2_000) {
            let a = row.cells[0].unwrap();
            assert!(a.max < 1.0, "{} {}", row.op, row.format);
            if row.format == "Q16.16" {
                assert_eq!(a.correct, 1.0, "{} {}", row.op, row.format);
            }
            assert!(row.cells[1..].iter().flatten().all(|c| c.max.is_finite()));
        }
    }
}
