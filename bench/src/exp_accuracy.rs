//! Accuracy of the exponentials, logarithms and powers: fulcrum, the `std`
//! and `libm` floats rounded into the same fixed-point format, and the `exp`
//! of the `cordic` crate on the `fixed` type of the same format, measured
//! against the interval oracle of `fulcrum_oracle` (256 bits), as in
//! [`crate::trig_accuracy`].
//!
//! Operands: `(0, 256)` for `log2` and `ln`, `[-8, 8)` for `exp2` and
//! `exp`, a base in `(0, 4)` and an exponent in `[-4, 4)` for `pow`, a base
//! in `[-2, 2)` and an integer in `[-16, 16]` for `powi`. For `powi` the
//! `std` floats call their `powi` with the integer, `libm`, which has none,
//! its `pow` with the integer as a float.

use crate::inputs;
use crate::trig_accuracy::{operands, round_float, Exact, Tally};
use fixed::types::{I16F16, I32F32};
use fulcrum::{FixedFloat32, FixedFloat64};
use fulcrum_oracle as oracle;
use num_bigint::BigInt;
use num_traits::One;

pub use crate::trig_accuracy::Row;

/// The functions of the table, in order.
pub const OPS: [&str; 6] = ["log2", "exp2", "ln", "exp", "pow", "powi"];

/// The implementations of the table, in order; `cordic` has only `exp`.
const IMPS: [&str; 4] = ["fulcrum", "std", "libm", "cordic"];

/// An interval far above the range of a format with `bits` bits, clamped
/// to `MAX` by [`Exact`].
fn huge(bits: u32) -> (BigInt, BigInt) {
    let big = BigInt::one() << (oracle::TRIG_SCALE + bits);
    (big.clone(), big)
}

/// The exact value of `op` at raw operands `a` and `b` (the integer of
/// `powi`).
fn exact(op: &str, a: i128, b: i128, frac: u32, bits: u32) -> Exact {
    let v = match op {
        "log2" => oracle::log2(a, frac),
        "exp2" => oracle::exp2(a, frac),
        "ln" => oracle::ln(a, frac),
        "exp" => oracle::exp(a, frac),
        "pow" => oracle::pow(a, frac, b, frac).unwrap_or_else(|| huge(bits)),
        _ => {
            let one = BigInt::one() << oracle::TRIG_SCALE;
            if b == 0 {
                (one.clone(), one)
            } else if a == 0 {
                if b > 0 {
                    (BigInt::from(0), BigInt::from(0))
                } else {
                    huge(bits)
                }
            } else {
                let (lo, hi) = oracle::pow(a.abs(), frac, b, 0).unwrap_or_else(|| huge(bits));
                if a < 0 && b % 2 != 0 {
                    (-hi, -lo)
                } else {
                    (lo, hi)
                }
            }
        }
    };
    Exact::new(v, frac, bits)
}

/// The row of one function on one format.
fn row(samples: usize, op: &'static str, format: &'static str, frac: u32, bits: u32) -> Row {
    let positive = |seed, k| -> Vec<i128> {
        operands(samples, seed, frac, k)
            .into_iter()
            .map(|a| (a & ((1 << (frac + k)) - 1)) | 1)
            .collect()
    };
    let args: Vec<(i128, i128)> = match op {
        "log2" | "ln" => positive(51, 8).into_iter().map(|a| (a, 0)).collect(),
        "exp2" | "exp" => operands(samples, 52, frac, 3)
            .into_iter()
            .map(|a| (a, 0))
            .collect(),
        "pow" => positive(53, 2)
            .into_iter()
            .zip(operands(samples, 54, frac, 2))
            .collect(),
        _ => operands(samples, 55, frac, 1)
            .into_iter()
            .zip(
                inputs(samples, 56)
                    .into_iter()
                    .map(|x| (x % 33) as i128 - 16),
            )
            .collect(),
    };
    let exact: Vec<Exact> = args
        .iter()
        .map(|&(a, b)| exact(op, a, b, frac, bits))
        .collect();
    let scale = (1u64 << frac) as f64;
    let f = |raw: i128| raw as f64 / scale;
    let mut cells = [None, None, None, None];
    for (k, imp) in IMPS.iter().enumerate() {
        if *imp == "cordic" && op != "exp" {
            continue;
        }
        let mut t = Tally::new();
        for (&(a, b), e) in args.iter().zip(&exact) {
            let r = match *imp {
                "fulcrum" => fulcrum(op, a, b, bits),
                "cordic" => cordic(a, bits),
                _ => {
                    let y = if op == "powi" {
                        float(op, f(a), b as f64, *imp == "std", bits)
                    } else {
                        float(op, f(a), f(b), *imp == "std", bits)
                    };
                    round_float(y, frac, bits)
                }
            };
            t.add(r, e);
        }
        cells[k] = Some(t.done());
    }
    Row { op, format, cells }
}

fn fulcrum(op: &str, a: i128, b: i128, bits: u32) -> i128 {
    macro_rules! call {
        ($T:ident, $Raw:ty) => {{
            let (x, y) = ($T::from_bits(a as $Raw), $T::from_bits(b as $Raw));
            let r = match op {
                "log2" => x.log2(),
                "exp2" => x.exp2(),
                "ln" => x.ln(),
                "exp" => x.exp(),
                "pow" => x.pow(y),
                _ => x.powi(b as i32),
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

fn cordic(a: i128, bits: u32) -> i128 {
    if bits == 32 {
        cordic::exp(I16F16::from_bits(a as i32)).to_bits() as i128
    } else {
        cordic::exp(I32F32::from_bits(a as i64)).to_bits() as i128
    }
}

/// The float result: `f32` for 32-bit formats, `f64` for 64-bit ones; `y`
/// is the exponent of `pow` and the integer of `powi`.
fn float(op: &str, x: f64, y: f64, std: bool, bits: u32) -> f64 {
    if bits == 32 {
        let (x, y) = (x as f32, y as f32);
        (match (op, std) {
            ("log2", true) => x.log2(),
            ("log2", false) => libm::log2f(x),
            ("exp2", true) => x.exp2(),
            ("exp2", false) => libm::exp2f(x),
            ("ln", true) => x.ln(),
            ("ln", false) => libm::logf(x),
            ("exp", true) => x.exp(),
            ("exp", false) => libm::expf(x),
            ("pow", true) => x.powf(y),
            ("powi", true) => x.powi(y as i32),
            (_, _) => libm::powf(x, y),
        }) as f64
    } else {
        match (op, std) {
            ("log2", true) => x.log2(),
            ("log2", false) => libm::log2(x),
            ("exp2", true) => x.exp2(),
            ("exp2", false) => libm::exp2(x),
            ("ln", true) => x.ln(),
            ("ln", false) => libm::log(x),
            ("exp", true) => x.exp(),
            ("exp", false) => libm::exp(x),
            ("pow", true) => x.powf(y),
            ("powi", true) => x.powi(y as i32),
            (_, _) => libm::pow(x, y),
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
    /// sample of `Q16.16` (an exact halfway power counts with either
    /// neighbour); every other implementation is measured.
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
