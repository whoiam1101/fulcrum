//! Sine and cosine in turns, and sine, cosine and tangent in radians, shared
//! by every width (docs/INTERNALS.md §3.11, §3.12).
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
//!
//! In radians the magnitude is multiplied exactly by 192 bits of `2/π`, which
//! gives the angle in quarter turns, and the same quarter does the rest;
//! `tan` near a pole takes the cotangent of the distance to it instead.
//!
//! The inverse functions take `atan(n/d)` of two magnitudes, `n ≤ d`, from
//! the table of `atan(k/2^STEPS)` and a short series of the exact remainder
//! `(2^STEPS·n - k·d) / (2^STEPS·d + k·n)`, and set the octant, the quadrant
//! and the sign after one rounding (INTERNALS §3.13).
//!
//! The angle types keep an angle as `n` bits of a turn, `n` the width of the
//! storage; their sine is the same quarter with `n - 2` bits of position, and
//! the conversions to and from radians use the same `2/π` and a `π` of 126
//! bits (INTERNALS §3.14).

use crate::tables::trig::{ATAN, FRAC, FRAC_2_PI, FRAC_PI_2, PI, PI_126, SIN_QUARTER, STEPS};

const ONE: u64 = 1 << FRAC;

/// `a · b / 2^FRAC`, truncated. `a · b < 2^(64 + FRAC)`.
#[inline]
const fn mul(a: u64, b: u64) -> u64 {
    ((a as u128 * b as u128) >> FRAC) as u64
}

/// `sin(p / 2^bits · π/2) · 2^FRAC` for `p ≤ 2^bits`, `bits ≤ FRAC`,
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

/// `sin(t / 2^bits · π/2)` for `t < 2^(bits+2)`, rounded to `f` fractional
/// bits: the top two bits of `t` are the quadrant, the rest the position
/// within it.
#[inline]
const fn sin_position(t: u64, bits: u32, f: u32) -> i64 {
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

/// `sin(2π · raw / 2^f)`, rounded to `f` fractional bits. `2 ≤ f ≤ 32`.
#[inline]
pub(crate) const fn sin_turns(raw: u64, f: u32) -> i64 {
    sin_position(raw & ((1 << f) - 1), f - 2, f)
}

/// `cos(2π · raw / 2^f) = sin(2π · (raw / 2^f + ¼))`, rounded to `f`
/// fractional bits. `2 ≤ f ≤ 32`.
#[inline]
pub(crate) const fn cos_turns(raw: u64, f: u32) -> i64 {
    sin_turns(raw.wrapping_add(1 << (f - 2)), f)
}

/// The angle `m / 2^f` radians in quarter turns, `m · 2/π / 2^f`: the
/// quadrant (the integer part mod 4) and the fraction at 128 bits, truncated.
/// The product of `m` and the 192 bits of `2/π` is exact on 256 bits.
/// `f ≤ 32`.
#[inline]
const fn reduce(m: u64, f: u32) -> (u64, u128) {
    let m = m as u128;
    let w0 = m * FRAC_2_PI[2] as u128;
    let w1 = m * FRAC_2_PI[1] as u128;
    let w2 = m * FRAC_2_PI[0] as u128;
    let t1 = (w0 >> 64) + (w1 as u64 as u128);
    let t2 = (t1 >> 64) + (w1 >> 64) + (w2 as u64 as u128);
    let high = (((t2 >> 64) + (w2 >> 64)) << 64) | (t2 as u64 as u128);
    let mid = t1 as u64 as u128;
    let quadrant = (high >> (f + 64)) as u64 & 3;
    (quadrant, (high << (64 - f)) | (mid >> f))
}

/// The quarter turns of [`reduce`] mod 4 at `FRAC` fractional bits, rounded
/// to nearest by `kernel::shr_round` (the carry wraps mod 4): the argument
/// `t` of [`sin_position`] with `bits = FRAC`.
#[inline]
const fn position(quadrant: u64, frac: u128) -> u64 {
    let v = ((quadrant as u128) << (FRAC + 1)) | (frac >> (127 - FRAC));
    crate::kernel::shr_round(v as i128, 1) as u64
}

/// `sin(raw / 2^f)`, rounded to `f` fractional bits, on `|raw|`: odd bit for
/// bit. `2 ≤ f ≤ 32`.
#[inline]
pub(crate) const fn sin(raw: i64, f: u32) -> i64 {
    let (quadrant, frac) = reduce(raw.unsigned_abs(), f);
    let s = sin_position(position(quadrant, frac), FRAC, f);
    if raw < 0 {
        -s
    } else {
        s
    }
}

/// `cos(raw / 2^f) = sin(|raw| / 2^f + π/2)`, rounded to `f` fractional
/// bits: even bit for bit. `2 ≤ f ≤ 32`.
#[inline]
pub(crate) const fn cos(raw: i64, f: u32) -> i64 {
    let (quadrant, frac) = reduce(raw.unsigned_abs(), f);
    sin_position(position(quadrant, frac).wrapping_add(ONE), FRAC, f)
}

/// `sin(raw / 2^f)` and `cos(raw / 2^f)`, each rounded to `f` fractional
/// bits, on `|raw|`: odd and even bit for bit. `2 ≤ f ≤ 32`.
#[inline]
pub(crate) const fn sin_cos(raw: i64, f: u32) -> (i64, i64) {
    let (quadrant, frac) = reduce(raw.unsigned_abs(), f);
    let t = position(quadrant, frac);
    let s = sin_position(t, FRAC, f);
    let c = sin_position(t.wrapping_add(ONE), FRAC, f);
    (if raw < 0 { -s } else { s }, c)
}

/// The distance to the pole below which [`tan`] uses the cotangent of the
/// distance: `2^-10` quarter turns at 128 fractional bits.
const NEAR_POLE: u128 = 1 << 118;

/// `⌊2/π · 2^192 / d⌋` for `2^64 ≤ d < NEAR_POLE`: long division, the low
/// word of `2/π` one byte at a time, so the remainder shifted by 8 stays
/// below `2^126`.
#[inline]
const fn frac_2_pi_div(d: u128) -> u128 {
    let top = ((FRAC_2_PI[0] as u128) << 64) | FRAC_2_PI[1] as u128;
    let mut q = top / d;
    let mut r = top % d;
    let mut i = 0;
    while i < 8 {
        r = (r << 8) | ((FRAC_2_PI[2] >> (56 - 8 * i)) & 0xFF) as u128;
        q = (q << 8) | (r / d);
        r %= d;
        i += 1;
    }
    q
}

/// `tan(raw / 2^f)`, rounded to `f` fractional bits, not yet saturated: the
/// magnitude stays below `2^(2f + 2)`, and is `2^(2f)` when it is out of
/// range of every type with `f` fractional bits. Odd bit for bit.
/// `2 ≤ f ≤ 32`.
///
/// Away from a pole, the quotient of the sine and the cosine of the quarter,
/// rounded once. Within [`NEAR_POLE`] of it, `cot θ` of the distance `θ`,
/// `1/θ - θ/3 - θ³/45` at 64 fractional bits, where `1/θ` comes from the
/// 128-bit distance without the rounding to 62 bits (INTERNALS §3.12).
#[inline]
pub(crate) const fn tan(raw: i64, f: u32) -> i128 {
    let (quadrant, frac) = reduce(raw.unsigned_abs(), f);
    let odd = quadrant & 1 == 1;
    let d = if odd { frac } else { frac.wrapping_neg() };
    let m = if d < NEAR_POLE && (odd || frac != 0) {
        let r = if d < 1 << (126 - f) {
            1 << (2 * f)
        } else {
            let theta = ((d >> 64) * FRAC_PI_2 as u128) >> FRAC;
            let theta2 = (theta * theta) >> 64;
            let theta3 = (theta2 * theta) >> 64;
            let cot = frac_2_pi_div(d) - theta / 3 - theta3 / 45;
            crate::kernel::shr_round(cot as i128, 64 - f)
        };
        if odd {
            -r
        } else {
            r
        }
    } else {
        let t = position(quadrant, frac);
        let bits = FRAC;
        let p = t & ((1 << bits) - 1);
        let a = sin_quarter(p, bits) as u128;
        let b = sin_quarter((1 << bits) - p, bits) as u128;
        let (n, d, negative) = if (t >> bits) & 1 == 0 {
            (a, b, false)
        } else {
            (b, a, true)
        };
        let r = crate::kernel::shr_round(((n << (f + 1)) / d) as i128, 1);
        if negative {
            -r
        } else {
            r
        }
    };
    if raw < 0 {
        -m
    } else {
        m
    }
}

/// `atan(n/d) · 2^FRAC` for `n ≤ d`, `0 < d ≤ 2^64`, with an error below
/// `3` units: `atan(k/2^STEPS)` of the table plus `atan δ` of the exact
/// `δ = (2^STEPS·n - k·d) / (2^STEPS·d + k·n) < 2^-STEPS`, with
/// `k = ⌊2^STEPS·n/d⌋` (INTERNALS §3.13).
#[inline]
const fn atan_unit(n: u128, d: u128) -> u64 {
    let k = (n << STEPS) / d;
    let rest = (n << STEPS) - k * d;
    if rest == 0 {
        return ATAN[k as usize];
    }
    let delta = ((rest << FRAC) / ((d << STEPS) + k * n)) as u64;
    let z = mul(delta, delta);
    let p = ONE / 3 - mul(z, ONE / 5 - z / 7);
    ATAN[k as usize] + delta - mul(mul(delta, z), p)
}

/// `atan(n/d) · 2^FRAC ∈ [0, π/2]` for `n, d ≤ 2^64`, not both `0`.
#[inline]
const fn atan_ratio(n: u128, d: u128) -> u64 {
    if n <= d {
        atan_unit(n, d)
    } else {
        FRAC_PI_2 - atan_unit(d, n)
    }
}

/// The angle `a · 2^-FRAC` of [`atan_ratio`], or `π` minus it when
/// `x_negative`, rounded to `f` fractional bits, with the sign of `negative`.
#[inline]
const fn round_angle(a: u64, x_negative: bool, negative: bool, f: u32) -> i64 {
    let a = if x_negative { PI - a } else { a };
    let r = crate::kernel::shr_round(a as i128, FRAC - f) as i64;
    if negative {
        -r
    } else {
        r
    }
}

/// `atan2(y, x)` of two raw values with `f` fractional bits, in `(-π, π]`,
/// rounded to `f` fractional bits; `atan2(0, x) = 0` for `x ≥ 0`. Odd in `y`
/// bit for bit. `2 ≤ f ≤ 32`.
#[inline]
pub(crate) const fn atan2(y: i64, x: i64, f: u32) -> i64 {
    if y == 0 && x >= 0 {
        return 0;
    }
    let a = atan_ratio(y.unsigned_abs() as u128, x.unsigned_abs() as u128);
    round_angle(a, x < 0, y < 0, f)
}

/// `atan(raw / 2^f) = atan2(raw, 2^f)`, rounded to `f` fractional bits. Odd
/// bit for bit. `2 ≤ f ≤ 32`.
#[inline]
pub(crate) const fn atan(raw: i64, f: u32) -> i64 {
    atan2(raw, 1 << f, f)
}

/// `x = raw / 2^f` and `√(1 - x²)` at `FRAC` fractional bits, the root
/// truncated, for `|raw| ≤ 2^f`.
#[inline]
const fn cathetus(raw: i64, f: u32) -> (u128, u128) {
    let m = raw.unsigned_abs() as u128;
    let rest = ((1u128 << (2 * f)) - m * m) << (2 * (FRAC - f));
    (m << (FRAC - f), crate::kernel::k64::isqrt(rest))
}

/// `asin(raw / 2^f) = atan2(x, √(1 - x²))`, rounded to `f` fractional
/// bits. Odd bit for bit. `|raw| ≤ 2^f`, `2 ≤ f ≤ 32`.
#[inline]
pub(crate) const fn asin(raw: i64, f: u32) -> i64 {
    let (x, s) = cathetus(raw, f);
    round_angle(atan_ratio(x, s), false, raw < 0, f)
}

/// `acos(raw / 2^f) = atan2(√(1 - x²), x)`, rounded to `f` fractional
/// bits. `|raw| ≤ 2^f`, `2 ≤ f ≤ 32`.
#[inline]
pub(crate) const fn acos(raw: i64, f: u32) -> i64 {
    let (x, s) = cathetus(raw, f);
    round_angle(atan_ratio(s, x), raw < 0, false, f)
}

/// `2^n - 1`: the mask of an angle of `n ≤ 64` bits.
#[inline]
const fn angle_mask(n: u32) -> u64 {
    if n == 64 {
        u64::MAX
    } else {
        (1 << n) - 1
    }
}

/// `sin(2π · t / 2^n)` of an angle of `n` bits, rounded to `f` fractional
/// bits. `t < 2^n`, `4 ≤ n ≤ 64`, `2 ≤ f ≤ 32`.
#[inline]
pub(crate) const fn angle_sin(t: u64, n: u32, f: u32) -> i64 {
    sin_position(t, n - 2, f)
}

/// `cos(2π · t / 2^n) = sin(2π · (t / 2^n + ¼))`, rounded to `f` fractional
/// bits. `t < 2^n`, `4 ≤ n ≤ 64`, `2 ≤ f ≤ 32`.
#[inline]
pub(crate) const fn angle_cos(t: u64, n: u32, f: u32) -> i64 {
    angle_sin(t.wrapping_add(1 << (n - 2)) & angle_mask(n), n, f)
}

/// The angle `raw / 2^f` radians as `n` bits of a turn, `x / 2π mod 1`
/// rounded to nearest: the quarter turns of [`reduce`] at 128 bits, rounded to
/// `n - 2` bits of position on the magnitude, then negated for `raw < 0`, so
/// `from_radians(-x) = -from_radians(x)` bit for bit. `f ≤ 32`,
/// `4 ≤ n ≤ 64`.
#[inline]
pub(crate) const fn angle_from_radians(raw: i64, f: u32, n: u32) -> u64 {
    let (quadrant, frac) = reduce(raw.unsigned_abs(), f);
    let position = (((frac >> (129 - n)) + 1) >> 1) as u64;
    let t = (quadrant << (n - 2)).wrapping_add(position) & angle_mask(n);
    if raw < 0 {
        t.wrapping_neg() & angle_mask(n)
    } else {
        t
    }
}

/// The angle `t / 2^n` of a turn in radians, `2π · s / 2^n` for the signed
/// `s ≡ t (mod 2^n)` in `[-2^(n-1), 2^(n-1))`, so in `[-π, π)`, rounded to `f`
/// fractional bits: `|s| · π · 2^126` exactly on 192 bits, one rounding on
/// the magnitude, then the sign. `f ≤ 32`, `4 ≤ n ≤ 64`.
#[inline]
pub(crate) const fn angle_to_radians(t: u64, n: u32, f: u32) -> i64 {
    let s = ((t << (64 - n)) as i64) >> (64 - n);
    let m = s.unsigned_abs() as u128;
    let high = m * (PI_126 >> 64) + ((m * (PI_126 as u64 as u128)) >> 64);
    let k = 125 + n - f - 64;
    let r = (((high >> (k - 1)) + 1) >> 1) as i64;
    if s < 0 {
        -r
    } else {
        r
    }
}

/// `t · x mod 2^n` for an angle of `n` bits and `x = raw / 2^f`: the signed
/// angle times `raw`, rounded to nearest by `kernel::shr_round`, wrapped to
/// `n` bits. `f ≤ 32`, `4 ≤ n ≤ 64`, `|raw| ≤ 2^63`.
#[inline]
pub(crate) const fn angle_scale(t: u64, n: u32, raw: i64, f: u32) -> u64 {
    let s = ((t << (64 - n)) as i64) >> (64 - n);
    let r = crate::kernel::shr_round(s as i128 * raw as i128, f);
    r as u64 & angle_mask(n)
}
