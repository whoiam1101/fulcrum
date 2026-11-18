//! Accuracy of square roots: fulcrum against floats rounded into the same
//! fixed-point format, measured against the exact root.
//!
//! Every result is a raw value `r` of a format with `F` fractional bits. The
//! exact root is computed as `⌊√(num / den) · 2^K⌋` with `K` extra bits on
//! big integers, so the error of `r` in ulps is known to `2^-K`, and `r` is
//! correctly rounded when it equals that floor rounded to nearest at `K`.
//! Floats take the input converted to the nearest float, compute the root,
//! and are rounded to nearest into the format: what a program gets when it
//! computes in floats and stores fixed-point.

use crate::inputs;
use fulcrum::{FixedFloat32, FixedFloat64};
use num_bigint::BigUint;

const K: u32 = 24;

/// Errors of one implementation of one function, in ulps of the format.
#[derive(Clone, Copy, Debug)]
pub struct Accuracy {
    /// Largest absolute error.
    pub max: f64,
    /// Mean absolute error.
    pub mean: f64,
    /// Share of correctly rounded results, `0..=1`.
    pub correct: f64,
}

/// One row of the accuracy table: function, implementation, format, errors.
pub struct Row {
    /// `sqrt`, `rsqrt` or `hypot`.
    pub op: &'static str,
    /// Who computed it, such as `fulcrum` or `f64` with `libm`.
    pub imp: &'static str,
    /// The fixed-point format of the result.
    pub format: &'static str,
    /// The measured errors.
    pub accuracy: Accuracy,
}

/// The exact root `√(num / den)` of a raw result as `⌊root · 2^K⌋`.
fn exact(num: u128, num_shift: u32, den: u128) -> BigUint {
    let n = (BigUint::from(num) << (num_shift + 2 * K)) / BigUint::from(den);
    n.sqrt()
}

/// Running errors of one implementation of one function.
pub(crate) struct Tally {
    max: f64,
    sum: f64,
    correct: usize,
    n: usize,
}

impl Tally {
    pub(crate) fn new() -> Self {
        Self {
            max: 0.0,
            sum: 0.0,
            correct: 0,
            n: 0,
        }
    }

    /// One result with error `err` in ulps, correctly rounded or not.
    pub(crate) fn record(&mut self, err: f64, correct: bool) {
        self.max = self.max.max(err);
        self.sum += err;
        self.correct += usize::from(correct);
        self.n += 1;
    }

    fn add(&mut self, r: i128, e: &BigUint) {
        let scaled = BigUint::from(r.max(0) as u128) << K;
        let diff = if scaled >= *e {
            &scaled - e
        } else {
            e - &scaled
        };
        let err = u128::try_from(&diff).map_or(f64::INFINITY, |d| d as f64) / (1u64 << K) as f64;
        let nearest = (e + (BigUint::from(1u8) << (K - 1))) >> K;
        self.record(err, r >= 0 && nearest == BigUint::from(r as u128));
    }

    pub(crate) fn done(&self) -> Accuracy {
        Accuracy {
            max: self.max,
            mean: self.sum / self.n as f64,
            correct: self.correct as f64 / self.n as f64,
        }
    }
}

/// Raw positive operands of `bits` bits: half uniform over the raw range,
/// half uniform in the exponent, so that small values are covered.
fn positives(n: usize, seed: u64, bits: u32) -> Vec<u64> {
    let max = (1u64 << (bits - 1)) - 1;
    inputs(n, seed)
        .into_iter()
        .enumerate()
        .map(|(i, x)| {
            let v = if i % 2 == 0 {
                x & max
            } else {
                (x & max) >> ((x >> 58) % (bits as u64 - 1))
            };
            v.max(1)
        })
        .collect()
}

/// A float result rounded to nearest into a format with `frac` fractional
/// bits and `bits` bits, saturated; `NaN` gives `0`.
pub(crate) fn round_float(y: f64, frac: u32, bits: u32) -> i128 {
    let r = (y * (1u64 << frac) as f64).round();
    if r.is_nan() {
        0
    } else {
        (r as i128).clamp(-(1i128 << (bits - 1)), (1i128 << (bits - 1)) - 1)
    }
}

/// The table: `sqrt`, `rsqrt`, `hypot` on `FixedFloat32` against `f32`, on
/// `FixedFloat64` against `f64`, with `std` (hardware) and `libm` (software),
/// on `samples` operands each.
pub fn table(samples: usize) -> Vec<Row> {
    let mut rows = Vec::new();
    let q16 = positives(samples, 21, 32);
    let q32 = positives(samples, 22, 64);
    let pairs16: Vec<(u64, u64)> = q16
        .iter()
        .zip(positives(samples, 23, 32))
        .map(|(&a, b)| (a >> 1, b >> 1))
        .collect();
    let pairs32: Vec<(u64, u64)> = q32
        .iter()
        .zip(positives(samples, 24, 64))
        .map(|(&a, b)| (a >> 1, b >> 1))
        .collect();

    type F32 = fn(f32) -> f32;
    type F32x2 = fn(f32, f32) -> f32;
    type F64 = fn(f64) -> f64;
    type F64x2 = fn(f64, f64) -> f64;
    let f32_impls: [(&'static str, F32, F32x2); 2] = [
        ("`f32`, `std`", |x| x.sqrt(), |x, y| x.hypot(y)),
        ("`f32`, `libm`", libm::sqrtf, libm::hypotf),
    ];
    let f64_impls: [(&'static str, F64, F64x2); 2] = [
        ("`f64`, `std`", |x| x.sqrt(), |x, y| x.hypot(y)),
        ("`f64`, `libm`", libm::sqrt, libm::hypot),
    ];

    for op in ["sqrt", "rsqrt", "hypot"] {
        let ex16: Vec<BigUint> = match op {
            "sqrt" => q16.iter().map(|&a| exact(a as u128, 16, 1)).collect(),
            "rsqrt" => q16.iter().map(|&a| exact(1, 48, a as u128)).collect(),
            _ => pairs16
                .iter()
                .map(|&(a, b)| exact((a as u128).pow(2) + (b as u128).pow(2), 0, 1))
                .collect(),
        };
        let mut t = Tally::new();
        for (i, e) in ex16.iter().enumerate() {
            let x = FixedFloat32::from_bits(q16[i] as i32);
            let r = match op {
                "sqrt" => x.sqrt(),
                "rsqrt" => x.rsqrt(),
                _ => FixedFloat32::from_bits(pairs16[i].0 as i32)
                    .hypot(FixedFloat32::from_bits(pairs16[i].1 as i32)),
            };
            t.add(r.to_bits() as i128, e);
        }
        rows.push(Row {
            op,
            imp: "fulcrum",
            format: "Q16.16",
            accuracy: t.done(),
        });
        for (imp, sqrt, hypot) in f32_impls {
            let mut t = Tally::new();
            for (i, e) in ex16.iter().enumerate() {
                let f = |raw: u64| (raw as f64 / 65536.0) as f32;
                let y = match op {
                    "sqrt" => sqrt(f(q16[i])),
                    "rsqrt" => 1.0 / sqrt(f(q16[i])),
                    _ => hypot(f(pairs16[i].0), f(pairs16[i].1)),
                };
                t.add(round_float(y as f64, 16, 32), e);
            }
            rows.push(Row {
                op,
                imp,
                format: "Q16.16",
                accuracy: t.done(),
            });
        }

        let ex32: Vec<BigUint> = match op {
            "sqrt" => q32.iter().map(|&a| exact(a as u128, 32, 1)).collect(),
            "rsqrt" => q32.iter().map(|&a| exact(1, 96, a as u128)).collect(),
            _ => pairs32
                .iter()
                .map(|&(a, b)| exact((a as u128).pow(2) + (b as u128).pow(2), 0, 1))
                .collect(),
        };
        let mut t = Tally::new();
        for (i, e) in ex32.iter().enumerate() {
            let x = FixedFloat64::from_bits(q32[i] as i64);
            let r = match op {
                "sqrt" => x.sqrt(),
                "rsqrt" => x.rsqrt(),
                _ => FixedFloat64::from_bits(pairs32[i].0 as i64)
                    .hypot(FixedFloat64::from_bits(pairs32[i].1 as i64)),
            };
            t.add(r.to_bits() as i128, e);
        }
        rows.push(Row {
            op,
            imp: "fulcrum",
            format: "Q32.32",
            accuracy: t.done(),
        });
        for (imp, sqrt, hypot) in f64_impls {
            let mut t = Tally::new();
            for (i, e) in ex32.iter().enumerate() {
                let f = |raw: u64| raw as f64 / 4_294_967_296.0;
                let y = match op {
                    "sqrt" => sqrt(f(q32[i])),
                    "rsqrt" => 1.0 / sqrt(f(q32[i])),
                    _ => hypot(f(pairs32[i].0), f(pairs32[i].1)),
                };
                t.add(round_float(y, 32, 64), e);
            }
            rows.push(Row {
                op,
                imp,
                format: "Q32.32",
                accuracy: t.done(),
            });
        }
    }
    rows
}

#[cfg(test)]
mod tests {
    /// fulcrum is correctly rounded on every sample, and the error measure
    /// sees the rounding of the floats.
    #[test]
    fn fulcrum_rows_are_correctly_rounded() {
        let rows = super::table(20_000);
        for r in rows.iter().filter(|r| r.imp == "fulcrum") {
            assert_eq!(r.accuracy.correct, 1.0, "{} {}", r.op, r.format);
            assert!(r.accuracy.max <= 0.5, "{} {}", r.op, r.format);
        }
        assert!(rows
            .iter()
            .any(|r| r.imp != "fulcrum" && r.accuracy.correct < 1.0));
    }
}
