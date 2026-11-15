//! Sine and cosine in turns, shared by every width (docs/INTERNALS.md §3.11).
//!
//! A type passes its raw value and its number of fractional bits `f`; only
//! the low `f` bits, the fraction of a turn, matter, so the range reduction is
//! a mask. The top two of them are the quadrant, the rest the position `p`
//! within the quarter. `sin(p · π/2)` comes from the quarter-circle table of
//! `src/tables/trig.rs` at the nearest point below and a short series for the
//! remainder, all on `u64` with 62 fractional bits, and is rounded once to `f`
//! bits at the end by `kernel::shr_round`, on the magnitude, before the
//! sign. Quadrants 1 and 3 read the quarter backwards, so the
//! symmetries `sin(-x) = -sin(x)`, `cos(-x) = cos(x)` and
//! `cos(x) = sin(x + ¼)` hold bit for bit (except `-MIN`, which saturates).

use crate::tables::trig::{FRAC, FRAC_PI_2, SIN_QUARTER, STEPS};

const ONE: u64 = 1 << FRAC;

/// `a · b / 2^FRAC`, truncated. `a · b < 2^(64 + FRAC)`.
#[inline]
const fn mul(a: u64, b: u64) -> u64 {
    ((a as u128 * b as u128) >> FRAC) as u64
}

/// `sin(p / 2^bits · π/2) · 2^FRAC` for `p ≤ 2^bits`, `bits ≤ FRAC - STEPS`,
/// with an error below `2^-59` (INTERNALS §3.11).
#[inline]
const fn sin_quarter(p: u64, bits: u32) -> u64 {
    if bits <= STEPS {
        return SIN_QUARTER[(p << (STEPS - bits)) as usize];
    }
    let rest = bits - STEPS;
    let k = p >> rest;
    let b = p & ((1 << rest) - 1);
    let s = SIN_QUARTER[k as usize];
    if b == 0 {
        return s;
    }
    let c = SIN_QUARTER[((1 << STEPS) - k) as usize];
    let theta = mul(b << (FRAC - bits), FRAC_PI_2);
    let z = mul(theta, theta);
    let sin_b = mul(theta, ONE - mul(z / 6, ONE - z / 20));
    let one_minus_cos_b = mul(z / 2, ONE - mul(z / 12, ONE - z / 30));
    s - mul(s, one_minus_cos_b) + mul(c, sin_b)
}

/// `sin(2π · raw / 2^f)`, rounded to `f` fractional bits. `2 ≤ f ≤ 32`.
#[inline]
pub(crate) const fn sin_turns(raw: u64, f: u32) -> i64 {
    let bits = f - 2;
    let t = raw & ((1 << f) - 1);
    let quadrant = t >> bits;
    let p = t & ((1 << bits) - 1);
    let m = if quadrant & 1 == 0 {
        sin_quarter(p, bits)
    } else {
        sin_quarter((1 << bits) - p, bits)
    };
    let r = crate::kernel::shr_round(m as i128, FRAC - f) as i64;
    if quadrant < 2 {
        r
    } else {
        -r
    }
}

/// `cos(2π · raw / 2^f) = sin(2π · (raw / 2^f + ¼))`, rounded to `f`
/// fractional bits. `2 ≤ f ≤ 32`.
#[inline]
pub(crate) const fn cos_turns(raw: u64, f: u32) -> i64 {
    sin_turns(raw.wrapping_add(1 << (f - 2)), f)
}
