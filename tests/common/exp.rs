//! Reference binary logarithm and exponential, written independently of the
//! library: no table, the full series of the whole argument.
//!
//! [`log2`] takes the mantissa `u ∈ [1, 2)` of the argument and the full
//! series of `ln u = 2·atanh((u - 1)/(u + 1))` at 64 fractional bits on
//! `u128`, without the table of `log₂(1 + k/256)` and the three terms of
//! `src/exp.rs`. It returns `log₂ x · 2^64` within [`LOG2_ERROR`]; the
//! rational oracle checks the bound (`oracle/tests/exp.rs`).
//!
//! [`exp2`] writes `x = n + t`, `n` an integer and `t ∈ [0, 1)`, and sums
//! the full Taylor series of `e^(t·ln 2)` at 124 fractional bits, with
//! 256-bit products, instead of the table of `2^(k/256)` and the short
//! series of the remainder.

/// Fractional bits of [`log2`].
pub const SCALE: u32 = 64;

/// Bound on the error of [`log2`], in units of `2^-64`.
pub const LOG2_ERROR: i128 = 1 << 8;

/// `log₂ e · 2^64`, rounded to nearest.
const LOG2_E: u128 = 0x1_7154_7652_B82F_E177;

const ONE: u128 = 1 << 64;

/// Fractional bits of the mantissa of [`exp2`].
pub const EXP2_SCALE: u32 = 124;

/// Bound on the error of the mantissa of [`exp2`], in units of `2^-124`.
pub const EXP2_ERROR: u128 = 1 << 8;

/// `ln 2 · 2^128`, rounded to nearest.
const LN_2: u128 = 0xB172_17F7_D1CF_79AB_C9E3_B398_03F2_F6AF;

/// `⌊a · b / 2^s⌋` from the exact 256-bit product, `64 ≤ s < 192`, when it
/// fits `u128`.
fn mul_shr(a: u128, b: u128, s: u32) -> u128 {
    let (a1, a0) = (a >> 64, a & u128::from(u64::MAX));
    let (b1, b0) = (b >> 64, b & u128::from(u64::MAX));
    let low = a0 * b0;
    let mid = (low >> 64) + ((a0 * b1) & u128::from(u64::MAX)) + ((a1 * b0) & u128::from(u64::MAX));
    let high = a1 * b1 + ((a0 * b1) >> 64) + ((a1 * b0) >> 64) + (mid >> 64);
    let mid = mid & u128::from(u64::MAX);
    if s >= 128 {
        high >> (s - 128)
    } else {
        (high << (128 - s)) | (((mid << 64) | (low & u128::from(u64::MAX))) >> s)
    }
}

/// `2^(raw / 2^f)` as `m / 2^s`: the mantissa `m = 2^t · 2^124 ∈ [2^124,
/// 2^125)`, the exact `s = 124 - f - n` and the bound on the error of `m`,
/// [`EXP2_ERROR`], or `0` when `t = 0` and `m = 2^124` is exact. `f ≤ 32`.
pub fn exp2(raw: i128, f: u32) -> (u128, i128, u128) {
    let n = raw >> f;
    let t = (raw & ((1 << f) - 1)) as u128;
    let v = mul_shr(t << (EXP2_SCALE - f), LN_2, 128);
    let mut term = 1u128 << EXP2_SCALE;
    let mut sum = 0u128;
    let mut k = 1u128;
    while term != 0 {
        sum += term;
        term = mul_shr(term, v, EXP2_SCALE) / k;
        k += 1;
    }
    let error = if t == 0 { 0 } else { EXP2_ERROR };
    (sum, i128::from(EXP2_SCALE) - i128::from(f) - n, error)
}

/// `⌊m / 2^s⌋` for `s ≥ 0`.
fn shr(m: u128, s: i128) -> u128 {
    if s >= 128 {
        0
    } else {
        m >> s
    }
}

/// `m / 2^s` rounded to nearest, ties up. `s ≥ 1`.
pub fn round_scaled(m: u128, s: i128) -> u128 {
    (shr(m, s - 1) + 1) >> 1
}

/// The integer nearest to every value of `[m - error, m + error] / 2^s`, if
/// there is one. `s ≥ 1`.
pub fn exp2_correctly_rounded(m: u128, s: i128, error: u128) -> Option<u128> {
    let lo = round_scaled(m - error, s);
    if lo == round_scaled(m + error, s) {
        Some(lo)
    } else {
        None
    }
}

/// `|got - v| < 1` for every `v ∈ [m - error, m + error] / 2^s`. `s ≥ 1`.
pub fn exp2_within_ulp(got: u128, m: u128, s: i128, error: u128) -> bool {
    let floor_hi = shr(m + error, s);
    let ceil_lo = shr(m - error - 1, s) + 1;
    got >= floor_hi && got <= ceil_lo
}

fn mul(a: u128, b: u128) -> u128 {
    (a * b) >> 64
}

/// `log₂(raw / 2^f) · 2^64`, within [`LOG2_ERROR`]. `0 < raw < 2^64`,
/// `f ≤ 32`.
pub fn log2(raw: i128, f: u32) -> i128 {
    let a = raw as u128;
    let e = 127 - a.leading_zeros();
    let u = a << (64 - e);
    let s = ((u - ONE) << 64) / (u + ONE);
    let s2 = mul(s, s);
    let mut power = s;
    let mut sum = 0u128;
    let mut k = 1u128;
    while power != 0 {
        sum += power / k;
        power = mul(power, s2);
        k += 2;
    }
    let l = ((sum * LOG2_E) >> 63) as i128;
    ((i128::from(e) - i128::from(f)) << 64) + l
}

/// The value with `f` fractional bits nearest to `r / 2^64`, if every value
/// within `error` of `r` rounds to it.
pub fn correctly_rounded(r: i128, error: i128, f: u32) -> Option<i128> {
    let s = SCALE - f;
    let round = |v: i128| (v + (1 << (s - 1))) >> s;
    let lo = round(r - error);
    if lo == round(r + error) {
        Some(lo)
    } else {
        None
    }
}

/// `|got / 2^f - true value| < 2^-f` for every true value within `error`
/// of `r / 2^64`.
pub fn within_ulp(got: i128, r: i128, error: i128, f: u32) -> bool {
    let ulp = 1i128 << (SCALE - f);
    ((got << (SCALE - f)) - r).abs() + error < ulp
}
