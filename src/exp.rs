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
//!
//! `pow` is `2^(y · log₂ x)`. The absolute error of the exponent becomes a
//! relative error of the result, so `log₂ x` comes from a wide logarithm
//! with an error below `2^-119`: the 126-bit table, `s` at 128 bits and
//! seven terms of the series; the product with `y` is exact up to `2^-120`,
//! and `2^w` is the tail of `exp2` with the remainder at 120 bits.

use crate::tables::exp::{
    EXP2, EXP2_FRAC, FRAC, LN_2, LN_2_FRAC, LOG2, LOG2_WIDE, STEPS, TWO_LOG2_E, TWO_LOG2_E_WIDE,
    WIDE_FRAC,
};

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

/// The exponent `e = ⌊log₂ raw⌋` of `raw > 0` and [`log2_unit`] of its
/// mantissa `raw / 2^e`.
#[inline]
const fn split_log2(raw: i64) -> (i64, u64) {
    let a = raw as u64;
    let e = 63 - a.leading_zeros();
    (e as i64, log2_unit(a << (FRAC - e)))
}

/// `log₂(raw / 2^f)`, rounded to `f` fractional bits. `raw > 0`,
/// `1 ≤ f ≤ 32`; the result is in `[-f, f - 1]` and always in range.
#[inline]
pub(crate) const fn log2(raw: i64, f: u32) -> i64 {
    let (e, l) = split_log2(raw);
    let r = crate::kernel::shr_round(l as i128, FRAC - f) as i64;
    ((e - f as i64) << f) + r
}

/// `ln(raw / 2^f) = (e - f) · ln 2 + log₂ u · ln 2`, rounded once to `f`
/// fractional bits from a sum at [`LN_2_FRAC`] bits: the integer part times
/// [`LN_2`], the mantissa part times `ln 2` at 64 bits. `raw > 0`,
/// `1 ≤ f ≤ 32`; `|ln x| < f` is always in range.
#[inline]
pub(crate) const fn ln(raw: i64, f: u32) -> i64 {
    let (e, l) = split_log2(raw);
    let whole = (e - f as i64) as i128 * LN_2 as i128;
    let part = ((l as u128 * (LN_2 >> (LN_2_FRAC - 64))) >> (FRAC + 64 - LN_2_FRAC)) as i128;
    crate::kernel::shr_round(whole + part, LN_2_FRAC - f) as i64
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

/// `2^(k/2^STEPS) · e^y · 2^EXP2_FRAC` for `k < 2^STEPS` and
/// `y = y / 2^EXPM1_FRAC < 2^-8.5`: the table entry plus its product with
/// [`expm1`], an error below `2^-69.5` relative.
#[inline]
const fn exp_unit(k: u64, y: u64) -> u128 {
    let t = EXP2[k as usize];
    if y == 0 {
        return t;
    }
    let e = expm1(y) as u128;
    t + (((t >> 64) * e) >> (EXPM1_FRAC - 64)) + (((t as u64 as u128) * e) >> EXPM1_FRAC)
}

/// `2^(k/2^STEPS + b/2^f) · 2^EXP2_FRAC` for `k < 2^STEPS`,
/// `b < 2^(f - STEPS)`: [`exp_unit`] of `y = b/2^f · ln 2`.
#[inline]
const fn exp2_unit(k: u64, b: u64, f: u32) -> u128 {
    let y = ((b as u128 * LN_2) >> (f + LN_2_FRAC - EXPM1_FRAC)) as u64;
    exp_unit(k, y)
}

/// `m · 2^n / 2^EXP2_FRAC` rounded to `f` fractional bits, for a mantissa
/// `m < 2^127` and `n ≤ f - 1`: one rounding shift by at least 63 bits, `0`
/// when `m` is below half a unit.
#[inline]
const fn round_mantissa(m: u128, n: i64, f: u32) -> i128 {
    let s = EXP2_FRAC as i64 - f as i64 - n;
    let s = if s > 128 { 128 } else { s as u32 };
    crate::kernel::shr_round(m as i128, s)
}

/// `2^(2f)`: the value [`exp2`], [`exp`] and [`pow`] return for a result
/// out of range of every type with `f` fractional bits (`pow` its negation
/// for a negative one), which `saturate` turns into `MAX` or `MIN` and
/// `checked` into `None`.
#[inline]
const fn overflow(f: u32) -> i128 {
    1 << (2 * f)
}

/// `2^(raw / 2^f)`, rounded to `f` fractional bits, not yet saturated: the
/// result is below `2^(2f - 1)` plus one unit, and is `2^(2f)` when it is
/// out of range of every type with `f` fractional bits. `1 ≤ f ≤ 32`.
#[inline]
pub(crate) const fn exp2(raw: i64, f: u32) -> i128 {
    let n = raw >> f;
    if n >= f as i64 - 1 {
        return overflow(f);
    }
    let t = raw as u64 & ((1 << f) - 1);
    let m = if f <= STEPS {
        exp2_unit(t << (STEPS - f), 0, f)
    } else {
        let rest = f - STEPS;
        exp2_unit(t >> rest, t & ((1 << rest) - 1), f)
    };
    round_mantissa(m, n, f)
}

/// Fractional bits of the reduced argument of [`exp`]: `ln 2 / 2^STEPS` at
/// this scale is [`LN_2`].
const REDUCED_FRAC: u32 = LN_2_FRAC + STEPS;

/// `e^(raw / 2^f)`, rounded to `f` fractional bits, not yet saturated, with
/// the [`overflow`] value of [`exp2`]. `x = j · ln 2 / 2^STEPS + y`:
/// `j` from the product with `2·log₂ e`, corrected once so that the exact
/// remainder `y = x - j · LN_2` at [`REDUCED_FRAC`] bits is in
/// `[0, ln 2 / 2^STEPS)`; then `2^(j / 2^STEPS) · e^y` as in [`exp2`].
/// `x ≥ f` overflows, `x ≤ -2f` gives `0`. `1 ≤ f ≤ 32`.
#[inline]
pub(crate) const fn exp(raw: i64, f: u32) -> i128 {
    if raw >= (f as i64) << f {
        return overflow(f);
    }
    if raw <= -((2 * f as i64) << f) {
        return 0;
    }
    let raw = raw as i128;
    let mut j = (raw * TWO_LOG2_E as i128) >> (f + FRAC + 1 - STEPS);
    let mut y = (raw << (REDUCED_FRAC - f)) - j * LN_2 as i128;
    if y < 0 {
        j -= 1;
        y += LN_2 as i128;
    } else if y >= LN_2 as i128 {
        j += 1;
        y -= LN_2 as i128;
    }
    let n = (j >> STEPS) as i64;
    if n >= f as i64 - 1 {
        return overflow(f);
    }
    let k = (j & ((1 << STEPS) - 1)) as u64;
    let m = exp_unit(k, (y >> (REDUCED_FRAC - EXPM1_FRAC)) as u64);
    round_mantissa(m, n, f)
}

/// Fractional bits of the wide logarithm and of the exponent of [`pow`].
const W_FRAC: u32 = 120;

/// `⌊a · b / 2^128⌋`.
#[inline]
const fn mul_hi(a: u128, b: u128) -> u128 {
    crate::wide::widening_mul_u128(a, b).0
}

/// `log₂(a / 2^f) · 2^W_FRAC` for `0 < a ≤ 2^63`, `1 ≤ f ≤ 32`, with an
/// error below `1.05` units (INTERNALS §3.16): `log₂ c` of [`LOG2_WIDE`]
/// and `2·log₂ e · atanh s` of `s = (u - c)/(u + c) < 2^-9` at 128
/// fractional bits, seven terms; exact `0` at `a = 2^f`.
#[inline]
const fn log2_wide(a: u64, f: u32) -> i128 {
    let e = 63 - a.leading_zeros();
    let u = if e > FRAC {
        a >> (e - FRAC)
    } else {
        a << (FRAC - e)
    };
    let k = (u >> (FRAC - STEPS)) - (1 << STEPS);
    let c = ONE + (k << (FRAC - STEPS));
    let (d, r) = ((u + c) as u128, (u - c) as u128);
    let high = (r << 64) / d;
    let low = (((r << 64) % d) << 64) / d;
    let s = (high << 64) | low;
    let z = mul_hi(s, s);
    let mut g = u128::MAX / 13;
    g = u128::MAX / 11 + mul_hi(z, g);
    g = u128::MAX / 9 + mul_hi(z, g);
    g = u128::MAX / 7 + mul_hi(z, g);
    g = u128::MAX / 5 + mul_hi(z, g);
    g = u128::MAX / 3 + mul_hi(z, g);
    let atanh = s + mul_hi(s, mul_hi(z, g));
    let l = LOG2_WIDE[k as usize] + mul_hi(atanh, TWO_LOG2_E_WIDE);
    ((e as i128 - f as i128) << W_FRAC) + (l >> (WIDE_FRAC - W_FRAC)) as i128
}

/// `2^(w / 2^W_FRAC)` rounded to `f` fractional bits, not yet saturated:
/// below `2^(2f)`, and [`overflow`] from `w ≥ f`. `|w| < 2^127`.
/// `1 ≤ f ≤ 32`.
#[inline]
const fn exp2_wide(w: i128, f: u32) -> i128 {
    let n = (w >> W_FRAC) as i64;
    if n >= f as i64 {
        return overflow(f);
    }
    let t = w as u128 & ((1 << W_FRAC) - 1);
    let rest = W_FRAC - STEPS;
    let k = (t >> rest) as u64;
    let r = t & ((1 << rest) - 1);
    let y = (((r >> (W_FRAC - EXPM1_FRAC)) * (LN_2 >> (LN_2_FRAC - 64))) >> 64) as u64;
    round_mantissa(exp_unit(k, y), n, f)
}

/// `|x|^y` for `|x| = a / 2^f > 0` and `y = y / 2^fy ≠ 0`, `fy ∈ {0, f}`,
/// `|y| < 2^31` for `fy = 0`: `w = y · log₂ |x|` from two exact products of
/// the halves of [`log2_wide`], truncated to [`W_FRAC`] bits, then
/// [`exp2_wide`]. A product that is `64` or more in magnitude overflows or
/// gives `0` without a shift.
#[inline]
const fn pow_magnitude(a: u64, f: u32, y: i64, fy: u32) -> i128 {
    let l = log2_wide(a, f);
    let negative = (l < 0) != (y < 0);
    let (lm, ym) = (l.unsigned_abs(), y.unsigned_abs() as u128);
    let high = ym * (lm >> 64);
    if high >= 1 << (62 + fy) {
        return if negative { 0 } else { overflow(f) };
    }
    let m = ((high << (64 - fy)) + ((ym * (lm as u64 as u128)) >> fy)) as i128;
    exp2_wide(if negative { -m } else { m }, f)
}

/// `x^y` for `x = raw / 2^f` and `y = y / 2^fy`, `fy ∈ {0, f}`, rounded to
/// `f` fractional bits, not yet saturated, with the [`overflow`] value and
/// its negation for a negative result; `None` for `x < 0` and a `y` that is
/// not an integer. `x^0 = 1`, `0^y` is `0` for `y > 0` and [`overflow`] for
/// `y < 0`; a negative `x` with an odd `y` negates `|x|^y`. `1 ≤ f ≤ 32`.
#[inline]
pub(crate) const fn pow(raw: i64, f: u32, y: i64, fy: u32) -> Option<i128> {
    if y == 0 {
        return Some(1 << f);
    }
    if raw == 0 {
        return Some(if y > 0 { 0 } else { overflow(f) });
    }
    let m = pow_magnitude(raw.unsigned_abs(), f, y, fy);
    if raw > 0 {
        return Some(m);
    }
    if fy > 0 && y & ((1 << fy) - 1) != 0 {
        return None;
    }
    Some(if (y >> fy) & 1 == 1 { -m } else { m })
}
