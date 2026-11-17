//! The binary logarithm and exponential, shared by every width
//! (docs/INTERNALS.md §3.16).
//!
//! `log2` splits the argument into its exponent and a mantissa `u ∈ [1, 2)`
//! at 62 fractional bits; `log₂ u` is `log₂ c` of the table
//! `src/tables/exp.rs` at the point `c = 1 + k/256` just below `u` and
//! `2·log₂ e · atanh s` of the exact `s = (u - c)/(u + c) < 2^-9`, three terms
//! of the series, rounded once to `f` bits. The exponent is an integer, so the
//! rounding of the sum is the rounding of `log₂ u`.
//!
//! `exp2` writes `x = n + t`, `n` an integer and `t ∈ [0, 1)` the low `f`
//! bits, so the split is a mask. `2^t` is `2^(k/256)` of the table at 126
//! fractional bits, the point just below `t`, times `e^y` of the remainder
//! `y = (t - k/256) · ln 2 < 2^-8.5`, a series of seven terms at 72
//! fractional bits; the mantissa `2^t ∈ [1, 2)` is then shifted by `n` and
//! rounded once.

use crate::tables::exp::{EXP2, EXP2_FRAC, FRAC, LN_2, LN_2_FRAC, LOG2, STEPS, TWO_LOG2_E};

const ONE: u64 = 1 << FRAC;

/// `a · b / 2^FRAC`, truncated. `a · b < 2^(64 + FRAC)`.
#[inline]
const fn mul(a: u64, b: u64) -> u64 {
    ((a as u128 * b as u128) >> FRAC) as u64
}

/// `log₂(u / 2^FRAC) · 2^FRAC` for `2^FRAC ≤ u < 2^(FRAC + 1)`, with an
/// error below `8` units, `2^-59` (INTERNALS §3.16).
#[inline]
const fn log2_unit(u: u64) -> u64 {
    let k = (u >> (FRAC - STEPS)) - (1 << STEPS);
    let c = ONE + (k << (FRAC - STEPS));
    let s = (((u - c) as u128) << FRAC) / ((u + c) as u128);
    let s = s as u64;
    let z = mul(s, s);
    let series = s + mul(s, mul(z, ONE / 3 + mul(z, ONE / 5)));
    LOG2[k as usize] + mul(series, TWO_LOG2_E)
}

/// `log₂(raw / 2^f)`, rounded to `f` fractional bits. `raw > 0`,
/// `1 ≤ f ≤ 32`; the result is in `[-f, f - 1]` and always in range.
#[inline]
pub(crate) const fn log2(raw: i64, f: u32) -> i64 {
    let a = raw as u64;
    let e = 63 - a.leading_zeros();
    let l = log2_unit(a << (FRAC - e));
    let r = crate::kernel::shr_round(l as i128, FRAC - f) as i64;
    ((e as i64 - f as i64) << f) + r
}

/// `2^64`: the scale of the inner terms of [`expm1`].
const ONE_64: u128 = 1 << 64;

/// Fractional bits of `y` and `e^y - 1` in [`expm1`]: `y < 2^-8.5`, so
/// `y · 2^EXPM1_FRAC` fits `u64`.
const EXPM1_FRAC: u32 = 72;

/// `(e^y - 1) · 2^EXPM1_FRAC` for `y = y / 2^EXPM1_FRAC < 2^-8.5`, with an
/// error below `3` units: `y + y²·(1/2 + y·G)`, `G = 1/6 + y/24 + y²/120 + y³/720 +
/// y⁴/5040` at 64 fractional bits (INTERNALS §3.16).
#[inline]
const fn expm1(y: u64) -> u64 {
    let y = y as u128;
    let g = ONE_64 / 720 + ((y * (ONE_64 / 5040)) >> EXPM1_FRAC);
    let g = ONE_64 / 120 + ((y * g) >> EXPM1_FRAC);
    let g = ONE_64 / 24 + ((y * g) >> EXPM1_FRAC);
    let g = ONE_64 / 6 + ((y * g) >> EXPM1_FRAC);
    let h = ONE_64 / 2 + ((y * g) >> EXPM1_FRAC);
    let z = (y * y) >> EXPM1_FRAC;
    (y + ((z * h) >> 64)) as u64
}

/// `2^(k/2^STEPS + b/2^f) · 2^EXP2_FRAC` for `k < 2^STEPS`,
/// `b < 2^(f - STEPS)`: the table entry plus its product with
/// [`expm1`] of `y = b/2^f · ln 2`, an error below `2^-69.5` relative.
#[inline]
const fn exp2_unit(k: u64, b: u64, f: u32) -> u128 {
    let t = EXP2[k as usize];
    if b == 0 {
        return t;
    }
    let y = ((b as u128 * LN_2) >> (f + LN_2_FRAC - EXPM1_FRAC)) as u64;
    let e = expm1(y) as u128;
    t + (((t >> 64) * e) >> (EXPM1_FRAC - 64)) + (((t as u64 as u128) * e) >> EXPM1_FRAC)
}

/// `2^(raw / 2^f)`, rounded to `f` fractional bits, not yet saturated: the
/// result is below `2^(2f - 1)` plus one unit, and is `2^(2f)` when it is
/// out of range of every type with `f` fractional bits. `1 ≤ f ≤ 32`.
#[inline]
pub(crate) const fn exp2(raw: i64, f: u32) -> i128 {
    let n = raw >> f;
    if n >= f as i64 - 1 {
        return 1 << (2 * f);
    }
    let t = raw as u64 & ((1 << f) - 1);
    let m = if f <= STEPS {
        exp2_unit(t << (STEPS - f), 0, f)
    } else {
        let rest = f - STEPS;
        exp2_unit(t >> rest, t & ((1 << rest) - 1), f)
    };
    let s = EXP2_FRAC as i64 - f as i64 - n;
    let s = if s > 128 { 128 } else { s as u32 };
    crate::kernel::shr_round(m as i128, s)
}
