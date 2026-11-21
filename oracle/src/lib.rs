//! Exact reference implementation of the spec (docs/ARCHITECTURE.md §6.1.1)
//! over arbitrary-precision rationals. Shares no code with fulcrum.

use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, Signed, ToPrimitive, Zero};

/// Shape of a fixed-point type: total bits and fractional bits.
#[derive(Clone, Copy, Debug)]
pub struct Format {
    /// Total number of bits.
    pub bits: u32,
    /// Number of fractional bits.
    pub frac: u32,
}

impl Format {
    /// Smallest raw value.
    pub fn min(self) -> BigInt {
        -(BigInt::one() << (self.bits - 1))
    }

    /// Largest raw value.
    pub fn max(self) -> BigInt {
        (BigInt::one() << (self.bits - 1)) - 1
    }

    /// `raw / 2^frac` as an exact rational.
    pub fn exact(self, raw: i128) -> BigRational {
        BigRational::new(BigInt::from(raw), BigInt::one() << self.frac)
    }

    /// Raw value nearest to `x`, ties toward `+∞`, without range check.
    pub fn round(self, x: &BigRational) -> BigInt {
        let scaled = x * BigRational::from_integer(BigInt::one() << self.frac);
        let shifted = scaled + BigRational::new(BigInt::one(), BigInt::from(2));
        shifted.numer().div_floor(shifted.denom())
    }

    /// Whether a raw value is representable.
    pub fn fits(self, raw: &BigInt) -> bool {
        *raw >= self.min() && *raw <= self.max()
    }

    /// A rounded raw value saturated to the range, and whether it was in range.
    pub fn settle(self, raw: BigInt) -> (i128, bool) {
        let fits = self.fits(&raw);
        (self.saturate(raw), fits)
    }

    /// The interval `[lo, hi] · 2^-TRIG_SCALE` clamped to the range of the
    /// format.
    pub fn clamp(self, (lo, hi): (BigInt, BigInt)) -> (BigInt, BigInt) {
        let shift = TRIG_SCALE - self.frac;
        let (min, max) = (self.min() << shift, self.max() << shift);
        let c = |v: BigInt| v.max(min.clone()).min(max.clone());
        (c(lo), c(hi))
    }

    /// Saturates a raw value to the representable range.
    pub fn saturate(self, raw: BigInt) -> i128 {
        let v = if raw > self.max() {
            self.max()
        } else if raw < self.min() {
            self.min()
        } else {
            raw
        };
        v.to_i128().expect("fits i128")
    }

    /// A division by zero of a dividend of the sign `sign`: `MAX`, `MIN` or
    /// `0`, with the flag `false`.
    fn by_zero(self, sign: i128) -> (i128, bool) {
        let v = match sign {
            1 => self.max(),
            -1 => self.min(),
            _ => BigInt::zero(),
        };
        (v.to_i128().unwrap(), false)
    }

    /// The rounding of `x`, `None` when it is out of range.
    fn checked(self, x: &BigRational) -> Option<i128> {
        let r = self.round(x);
        if self.fits(&r) {
            r.to_i128()
        } else {
            None
        }
    }

    /// `spec_mul`: saturating rounded product.
    pub fn mul(self, a: i128, b: i128) -> (i128, bool) {
        let r = self.round(&(self.exact(a) * self.exact(b)));
        self.settle(r)
    }

    /// `spec_div`: saturating rounded quotient; `x / 0` by the sign of `x`.
    pub fn div(self, a: i128, b: i128) -> (i128, bool) {
        if b == 0 {
            return self.by_zero(a.signum());
        }
        let r = self.round(&(self.exact(a) / self.exact(b)));
        self.settle(r)
    }

    /// `self · a + b` rounded once and saturated; the flag is whether the
    /// rounded result is in range.
    pub fn mul_add(self, x: i128, a: i128, b: i128) -> (i128, bool) {
        let r = self.round(&(self.exact(x) * self.exact(a) + self.exact(b)));
        self.settle(r)
    }

    /// `self · a / b` rounded once and saturated; `b = 0` gives `MAX`, `MIN`
    /// or `0` by the sign of `self · a`, with the flag `false`.
    pub fn mul_div(self, x: i128, a: i128, b: i128) -> (i128, bool) {
        if b == 0 {
            return self.by_zero(x.signum() * a.signum());
        }
        let r = self.round(&(self.exact(x) * self.exact(a) / self.exact(b)));
        self.settle(r)
    }

    /// `x + (y - x) · t` rounded once and saturated.
    pub fn lerp(self, x: i128, y: i128, t: i128) -> (i128, bool) {
        let r = self.round(&(self.exact(x) + (self.exact(y) - self.exact(x)) * self.exact(t)));
        self.settle(r)
    }

    /// Raw value nearest to `√x` for `x ≥ 0`, ties toward `+∞` (there are
    /// none), without range check: `s = ⌊√⌊x · 4^frac⌋⌋` is the floor of the
    /// scaled root, and the root rounds up when `(s + ½)² ≤ x · 4^frac`.
    pub fn round_sqrt(self, x: &BigRational) -> BigInt {
        let scaled = x * BigRational::from_integer(BigInt::one() << (2 * self.frac));
        let s = scaled.to_integer().sqrt();
        let half = BigRational::new(&s * 2 + 1, BigInt::from(2));
        if &half * &half <= scaled {
            s + 1
        } else {
            s
        }
    }

    /// `√x` correctly rounded; `x < 0` gives `0` with the flag `false`.
    pub fn sqrt(self, x: i128) -> (i128, bool) {
        if x < 0 {
            return (0, false);
        }
        self.settle(self.round_sqrt(&self.exact(x)))
    }

    /// `1 / √x` correctly rounded and saturated; `x ≤ 0` gives `MAX` with
    /// the flag `false`.
    pub fn rsqrt(self, x: i128) -> (i128, bool) {
        if x <= 0 {
            return (self.max().to_i128().unwrap(), false);
        }
        self.settle(self.round_sqrt(&self.exact(x).recip()))
    }

    /// `√(x² + y²)` correctly rounded and saturated.
    pub fn hypot(self, x: i128, y: i128) -> (i128, bool) {
        self.length(&[x, y])
    }

    /// `√Σ x²`, the length of a vector, correctly rounded and saturated.
    pub fn length(self, x: &[i128]) -> (i128, bool) {
        let sum = x.iter().fold(BigRational::zero(), |s, &v| {
            s + self.exact(v) * self.exact(v)
        });
        self.settle(self.round_sqrt(&sum))
    }

    /// `a·d - b·c`, the determinant of two vectors, rounded once and
    /// saturated.
    pub fn det(self, a: i128, b: i128, c: i128, d: i128) -> (i128, bool) {
        let e = self.exact(a) * self.exact(d) - self.exact(b) * self.exact(c);
        self.settle(self.round(&e))
    }

    /// `Σ a·b` rounded once and saturated.
    pub fn dot(self, a: &[i128], b: &[i128]) -> (i128, bool) {
        let sum = a.iter().zip(b).fold(BigRational::zero(), |s, (&x, &y)| {
            s + self.exact(x) * self.exact(y)
        });
        let r = self.round(&sum);
        self.settle(r)
    }

    /// Rounded `num / den` as a raw value, `None` when out of range or `den = 0`.
    pub fn ratio(self, num: i128, den: i128) -> Option<i128> {
        if den == 0 {
            return None;
        }
        self.checked(&BigRational::new(BigInt::from(num), BigInt::from(den)))
    }

    /// Exact value of a decimal string `[-]int[.frac]`.
    pub fn decimal(text: &str) -> BigRational {
        let (neg, body) = match text.strip_prefix('-') {
            Some(rest) => (true, rest),
            None => (false, text.strip_prefix('+').unwrap_or(text)),
        };
        let (int, frac) = match body.split_once('.') {
            Some((i, f)) => (i, f),
            None => (body, ""),
        };
        let digits = format!("{}{}", int, frac);
        let n: BigInt = if digits.is_empty() {
            BigInt::zero()
        } else {
            digits.parse().unwrap()
        };
        let d = num_traits::pow(BigInt::from(10), frac.len());
        let v = BigRational::new(n, d);
        if neg {
            -v
        } else {
            v
        }
    }

    /// `spec_parse`: rounded raw value of a decimal string, `None` on overflow.
    pub fn parse(self, text: &str) -> Option<i128> {
        self.checked(&Self::decimal(text))
    }

    /// Whether `text` is exactly `raw / 2^frac` written in decimal.
    pub fn displays_exactly(self, raw: i128, text: &str) -> bool {
        Self::decimal(text) == self.exact(raw)
    }

    /// Absolute error of `text` against the exact value, in units of `10^-precision`,
    /// doubled: `≤ 1` means correctly rounded.
    pub fn display_error_doubled(self, raw: i128, text: &str, precision: u32) -> BigRational {
        let unit = BigRational::new(
            BigInt::one(),
            num_traits::pow(BigInt::from(10), precision as usize),
        );
        let err = (Self::decimal(text) - self.exact(raw)).abs();
        err / unit * BigRational::from_integer(BigInt::from(2))
    }

    /// Whether `text` is `raw / 2^frac` correctly rounded to `precision` digits
    /// (error at most half a unit of the last digit).
    pub fn is_correctly_rounded(self, raw: i128, text: &str, precision: u32) -> bool {
        self.display_error_doubled(raw, text, precision) <= BigRational::from_integer(BigInt::one())
    }
}

/// Bits of the intervals of [`sin_turns`].
pub const TRIG_SCALE: u32 = 256;

/// Whether `r` is `x · k / √s` rounded to nearest, ties toward `+∞`:
/// `(2|r| - 1)² · s ≤ 4x²k² < (2|r| + 1)² · s` with the sign of `x`, the
/// ends swapped for a negative `x`.
pub fn is_scaled(r: i128, x: i128, k: i128, s: &BigInt) -> bool {
    if r != 0 && (r < 0) != (x < 0) {
        return false;
    }
    let m = BigInt::from(r.unsigned_abs());
    let n = BigInt::from(4) * BigInt::from(x) * BigInt::from(x) * BigInt::from(k) * BigInt::from(k);
    let above = (&m * 2 + 1) * (&m * 2 + 1) * s;
    let below = (&m * 2 - 1) * (&m * 2 - 1) * s;
    let low_ok = m.is_zero() || if x >= 0 { below <= n } else { below < n };
    let high_ok = if x >= 0 { n < above } else { n <= above };
    low_ok && high_ok
}

/// `got / 2^frac` is within one ulp of every value of `[lo, hi] / 2^TRIG_SCALE`.
pub fn within_ulp_of_interval(got: i128, (lo, hi): &(BigInt, BigInt), frac: u32) -> bool {
    let shift = TRIG_SCALE - frac;
    let got = BigInt::from(got) << shift;
    let ulp = BigInt::one() << shift;
    &got - lo < ulp && hi - &got < ulp
}

/// The value with `frac` fractional bits nearest to every value of the
/// interval `[lo, hi] / 2^TRIG_SCALE`, if there is one.
pub fn rounded((lo, hi): &(BigInt, BigInt), frac: u32) -> Option<BigInt> {
    let shift = TRIG_SCALE - frac;
    let half = BigInt::one() << (shift - 1);
    let (a, b) = ((lo + &half) >> shift, (hi + &half) >> shift);
    if a == b {
        Some(a)
    } else {
        None
    }
}

/// π as an interval `[lo, hi] · 2^-TRIG_SCALE`: Machin's formula
/// `π = 16·atan(1/5) - 4·atan(1/239)` with floored terms.
pub fn pi_interval() -> (BigInt, BigInt) {
    let atan_inv = |x: u64| {
        let one = BigInt::one() << (TRIG_SCALE + 8);
        let x = BigInt::from(x);
        let mut sum = BigInt::zero();
        let mut k = 0u64;
        loop {
            let term = &one / (BigInt::from(2 * k + 1) * x.pow(2 * k as u32 + 1));
            if term.is_zero() {
                return (sum, k + 1);
            }
            if k % 2 == 0 {
                sum += term;
            } else {
                sum -= term;
            }
            k += 1;
        }
    };
    let (a, na) = atan_inv(5);
    let (b, nb) = atan_inv(239);
    let mid = a * 16 - b * 4;
    let err = BigInt::from(16 * na + 4 * nb);
    ((&mid - &err) >> 8, ((&mid + &err) >> 8) + 1)
}

/// `sin(2π · raw / 2^frac)` as an interval `[lo, hi] · 2^-TRIG_SCALE`: the
/// Taylor series of `sin x` on the whole `x ∈ [0, 2π)`, without symmetry,
/// each term `⌊X^n / (n! · 2^(TRIG_SCALE·(n-1)))⌋` computed from the exact
/// power. Shares no code with fulcrum or `tests/common/trig.rs`.
pub fn sin_turns(raw: i128, frac: u32) -> (BigInt, BigInt) {
    let t = BigInt::from(raw).mod_floor(&(BigInt::one() << frac));
    let (plo, phi) = pi_interval();
    let x: BigInt = (&t * &plo * BigInt::from(2)) >> frac;
    let width: BigInt = (((&t * &phi * BigInt::from(2)) >> frac) + 1) - &x;
    sin_series(&x, width)
}

/// `sin(x · 2^-TRIG_SCALE)` for `x ≥ 0` as an interval widened by `width`:
/// `|sin a - sin b| ≤ |a - b|`.
fn sin_series(x: &BigInt, width: BigInt) -> (BigInt, BigInt) {
    let mut sum = BigInt::zero();
    let mut fact = BigInt::one();
    let mut n = 1u32;
    let mut terms = 0u64;
    loop {
        let term = x.pow(n) / (&fact << (TRIG_SCALE * (n - 1)));
        terms += 1;
        if term.is_zero() && BigInt::from(n) > x >> (TRIG_SCALE - 2) {
            break;
        }
        if n % 4 == 1 {
            sum += term;
        } else {
            sum -= term;
        }
        fact *= BigInt::from((n + 1) * (n + 2));
        n += 2;
    }
    let err = width + terms + 3;
    (&sum - &err, sum + err)
}

/// `sin(raw / 2^frac + quarters · π/2)` as an interval
/// `[lo, hi] · 2^-TRIG_SCALE`, `quarters ≥ 0`: the argument at
/// `2^-(TRIG_SCALE+1)`, reduced to about `[0, 2π]` by the interval of `2π`
/// (the floor of the quotient by its upper end), then the series of
/// [`sin_turns`] at its lower end, widened by the width of the interval.
fn sin_radians(raw: i128, frac: u32, quarters: i64) -> (BigInt, BigInt) {
    let (plo, phi) = pi_interval();
    let x: BigInt = BigInt::from(raw) << (TRIG_SCALE + 1 - frac);
    let q = BigInt::from(quarters);
    let (x_lo, x_hi) = (&x + &q * &plo, &x + &q * &phi);
    let (tau_lo, tau_hi) = (&plo * 4, &phi * 4);
    let k: BigInt = x_hi.div_floor(&tau_hi);
    let (lo, hi) = if k.is_negative() {
        (&x_lo - &k * &tau_lo, &x_hi - &k * &tau_hi)
    } else {
        (&x_lo - &k * &tau_hi, &x_hi - &k * &tau_lo)
    };
    let lo: BigInt = lo.max(BigInt::zero()) >> 1u32;
    let hi: BigInt = (hi >> 1u32) + 1;
    let width = &hi - &lo;
    sin_series(&lo, width)
}

/// `sin(raw / 2^frac)` in radians as an interval `[lo, hi] · 2^-TRIG_SCALE`.
pub fn sin(raw: i128, frac: u32) -> (BigInt, BigInt) {
    sin_radians(raw, frac, 0)
}

/// `cos(raw / 2^frac) = sin(raw / 2^frac + π/2)` as an interval
/// `[lo, hi] · 2^-TRIG_SCALE`.
pub fn cos(raw: i128, frac: u32) -> (BigInt, BigInt) {
    sin_radians(raw, frac, 1)
}

/// `tan(raw / 2^frac)` as an interval `[lo, hi] · 2^-TRIG_SCALE`: the
/// quotient of the intervals of [`sin`] and [`cos`]; `None` if the cosine
/// interval contains `0`.
pub fn tan(raw: i128, frac: u32) -> Option<(BigInt, BigInt)> {
    let (slo, shi) = sin(raw, frac);
    let (clo, chi) = cos(raw, frac);
    if !clo.is_positive() && !chi.is_negative() {
        return None;
    }
    let q = |n: &BigInt, d: &BigInt| (n << TRIG_SCALE).div_floor(d);
    let corners = [q(&slo, &clo), q(&slo, &chi), q(&shi, &clo), q(&shi, &chi)];
    let lo = corners.iter().min().unwrap() - 1;
    let hi = corners.iter().max().unwrap() + 1;
    Some((lo, hi))
}

/// `atan(n/d)` for `0 ≤ n ≤ d`, `d > 0`, as an interval
/// `[lo, hi] · 2^-TRIG_SCALE`: Euler's series
/// `Σ 4^k (k!)² / (2k+1)! · n^(2k+1) d / (n² + d²)^(k+1)`, whose ratio is at
/// most `½`, each term floored for `lo` and ceiled for `hi`, and the tail
/// bounded by twice the first term left out. Shares no code with fulcrum or
/// `tests/common/trig.rs`.
fn atan_euler(n: &BigInt, d: &BigInt) -> (BigInt, BigInt) {
    let r = n * n + d * d;
    let n2 = n * n;
    let first = (n * d) << TRIG_SCALE;
    let (mut lo, mut hi) = (first.div_floor(&r), div_ceil(&first, &r));
    let (mut sum_lo, mut sum_hi) = (BigInt::zero(), BigInt::zero());
    let mut k = 0u64;
    loop {
        sum_lo += &lo;
        sum_hi += &hi;
        let num = BigInt::from(2 * k + 2) * &n2;
        let den = BigInt::from(2 * k + 3) * &r;
        lo = (lo * &num).div_floor(&den);
        hi = div_ceil(&(hi * &num), &den);
        k += 1;
        if hi <= BigInt::one() {
            return (sum_lo, sum_hi + 2);
        }
    }
}

fn div_ceil(a: &BigInt, b: &BigInt) -> BigInt {
    -((-a).div_floor(b))
}

/// `atan2(y, x)` of two integers of the same scale as an interval
/// `[lo, hi] · 2^-TRIG_SCALE` in `[-π, π]`; `atan2(0, x ≥ 0) = 0`.
pub fn atan2_int(y: &BigInt, x: &BigInt) -> (BigInt, BigInt) {
    if y.is_zero() && !x.is_negative() {
        return (BigInt::zero(), BigInt::zero());
    }
    let (plo, phi) = pi_interval();
    let (n, d) = (y.abs(), x.abs());
    let (lo, hi) = if n <= d {
        atan_euler(&n, &d)
    } else {
        let (lo, hi) = atan_euler(&d, &n);
        ((&plo >> 1u32) - hi - 1, (&phi >> 1u32) + 1 - lo)
    };
    let (lo, hi) = if x.is_negative() {
        (plo - hi, phi - lo)
    } else {
        (lo, hi)
    };
    if y.is_negative() {
        (-hi, -lo)
    } else {
        (lo, hi)
    }
}

/// `atan2(y, x)` of two raw values as an interval `[lo, hi] · 2^-TRIG_SCALE`.
pub fn atan2(y: i128, x: i128) -> (BigInt, BigInt) {
    atan2_int(&BigInt::from(y), &BigInt::from(x))
}

/// `atan(raw / 2^frac)` as an interval `[lo, hi] · 2^-TRIG_SCALE`.
pub fn atan(raw: i128, frac: u32) -> (BigInt, BigInt) {
    atan2(raw, 1 << frac)
}

/// `asin(raw / 2^frac) = atan2(x, √(1 - x²))` for `|raw| ≤ 2^frac` as an
/// interval `[lo, hi] · 2^-TRIG_SCALE`, from the interval `[s, s + 1]` of the
/// root at `2^-TRIG_SCALE`: the angle falls as the root grows.
pub fn asin(raw: i128, frac: u32) -> (BigInt, BigInt) {
    let m = BigInt::from(raw).abs();
    let one = BigInt::one() << frac;
    let s: BigInt = ((&one * &one - &m * &m) << (2 * (TRIG_SCALE - frac))).sqrt();
    let x = m << (TRIG_SCALE - frac);
    let (lo, _) = atan2_int(&x, &(&s + 1));
    let (_, hi) = atan2_int(&x, &s);
    if raw < 0 {
        (-hi, -lo)
    } else {
        (lo, hi)
    }
}

/// `acos(raw / 2^frac) = π/2 - asin(raw / 2^frac)` for `|raw| ≤ 2^frac` as
/// an interval `[lo, hi] · 2^-TRIG_SCALE`.
pub fn acos(raw: i128, frac: u32) -> (BigInt, BigInt) {
    let (plo, phi) = pi_interval();
    let (lo, hi) = asin(raw, frac);
    ((plo >> 1u32) - hi - 1, (phi >> 1u32) + 1 - lo)
}

/// The angle `t / 2^n` of a turn in radians, `2π · s / 2^n` for the signed
/// `s ≡ t (mod 2^n)` in `[-2^(n-1), 2^(n-1))`, rounded to `frac` fractional
/// bits, or `None` when the interval of `π` cannot decide the rounding.
pub fn angle_to_radians(t: u64, n: u32, frac: u32) -> Option<BigInt> {
    let s = BigInt::from(((t as u128) << (128 - n)) as i128 >> (128 - n));
    let (plo, phi) = pi_interval();
    let scale = TRIG_SCALE + n - frac;
    let (a, b) = if s.is_negative() {
        (&s * &phi * 2, &s * &plo * 2)
    } else {
        (&s * &plo * 2, &s * &phi * 2)
    };
    let half = BigInt::one() << (scale - 1);
    let (ra, rb) = ((a + &half) >> scale, (b + &half) >> scale);
    if ra == rb {
        Some(ra)
    } else {
        None
    }
}

/// The angle `raw / 2^frac` radians as `n` bits of a turn,
/// `round(raw / 2^frac / 2π · 2^n) mod 2^n`, or `None` when the interval of
/// `π` cannot decide the rounding.
pub fn angle_from_radians(raw: i128, frac: u32, n: u32) -> Option<u64> {
    let (plo, phi) = pi_interval();
    let extra = 64u32;
    let num = BigInt::from(raw) << (TRIG_SCALE + n - frac + extra);
    let (a, b) = if raw < 0 {
        (num.div_floor(&(&plo * 2)), div_ceil(&num, &(&phi * 2)))
    } else {
        (num.div_floor(&(&phi * 2)), div_ceil(&num, &(&plo * 2)))
    };
    let half = BigInt::one() << (extra - 1);
    let (ra, rb) = ((a + &half) >> extra, (b + &half) >> extra);
    if ra != rb {
        return None;
    }
    let modulus = BigInt::one() << n;
    ra.mod_floor(&modulus).to_u64()
}

/// `ln 2 = 2·atanh(1/3)` as an interval `[lo, hi] · 2^-TRIG_SCALE`.
pub fn ln2_interval() -> (BigInt, BigInt) {
    let (lo, hi) = atanh_ratio(&BigInt::one(), &BigInt::from(3));
    (lo * 2, hi * 2)
}

/// `atanh(p/q)` for `0 ≤ p ≤ q/3` as an interval `[lo, hi] · 2^-TRIG_SCALE`:
/// `Σ (p/q)^(2k+1) / (2k+1)`, every term positive and floored, so the sum
/// is a lower bound; each floored power is low by less than `9/8`, and the
/// tail after the power that floors to zero is below `2`.
fn atanh_ratio(p: &BigInt, q: &BigInt) -> (BigInt, BigInt) {
    let (p2, q2) = (p * p, q * q);
    let mut power = (p << TRIG_SCALE) / q;
    let mut sum = BigInt::zero();
    let mut k = 0u64;
    while !power.is_zero() {
        sum += &power / BigInt::from(2 * k + 1);
        power = power * &p2 / &q2;
        k += 1;
    }
    let hi = &sum + 3 * k + 2;
    (sum, hi)
}

/// `2^(raw / 2^frac)` as an interval `[lo, hi] · 2^-TRIG_SCALE`: `x = n + t`
/// with `t ∈ [0, 1)`, the Taylor series of `e^(t·ln 2)` at both ends of the
/// interval of `t·ln 2` (every term positive: floored terms give a lower
/// bound, and each is low by less than `2`, the tail below `4`), shifted by
/// `n`. `raw / 2^frac < 128`. Shares no code with fulcrum or
/// `tests/common/exp.rs`.
pub fn exp2(raw: i128, frac: u32) -> (BigInt, BigInt) {
    let raw = BigInt::from(raw);
    let n = raw.div_floor(&(BigInt::one() << frac)).to_i64().unwrap();
    assert!(n < 128, "2^{} is beyond the oracle", n);
    let t = raw.mod_floor(&(BigInt::one() << frac));
    let (llo, lhi) = ln2_interval();
    let series = |v: &BigInt| {
        let mut term = BigInt::one() << TRIG_SCALE;
        let mut sum = BigInt::zero();
        let mut k = 1u64;
        while !term.is_zero() {
            sum += &term;
            term = ((term * v) >> TRIG_SCALE) / BigInt::from(k);
            k += 1;
        }
        (sum, k)
    };
    let (lo, _) = series(&((&t * &llo) >> frac));
    let (hi, terms) = series(&(((&t * &lhi) >> frac) + 1));
    let hi = hi + 2 * terms + 4;
    if n >= 0 {
        (lo << n as usize, hi << n as usize)
    } else {
        let s = n.unsigned_abs() as usize;
        (lo >> s, (hi >> s) + 1)
    }
}

/// `log₂(raw / 2^frac)` for `raw > 0` as an interval
/// `[lo, hi] · 2^-TRIG_SCALE`: the exponent `e` of `raw`, and
/// `ln(raw / 2^e) = 2·atanh((raw - 2^e)/(raw + 2^e))` divided by the interval
/// of `ln 2`. Shares no code with fulcrum or `tests/common/exp.rs`.
pub fn log2(raw: i128, frac: u32) -> (BigInt, BigInt) {
    assert!(raw > 0);
    let a = BigInt::from(raw);
    let e = a.bits() - 1;
    let power = BigInt::one() << e as usize;
    let (slo, shi) = atanh_ratio(&(&a - &power), &(&a + &power));
    let (llo, lhi) = ln2_interval();
    let lo = ((slo * 2) << TRIG_SCALE) / lhi;
    let hi = ((shi * 2) << TRIG_SCALE) / llo + 1;
    let whole = BigInt::from(e as i64 - i64::from(frac)) << TRIG_SCALE;
    (&whole + lo, whole + hi)
}

/// `ln(raw / 2^frac)` for `raw > 0` as an interval `[lo, hi] · 2^-TRIG_SCALE`:
/// `(e - frac) · ln 2` of the interval of `ln 2` and
/// `2·atanh((raw - 2^e)/(raw + 2^e))` of the mantissa, without the binary
/// logarithm. Shares no code with fulcrum or `tests/common/exp.rs`.
pub fn ln(raw: i128, frac: u32) -> (BigInt, BigInt) {
    assert!(raw > 0);
    let a = BigInt::from(raw);
    let e = a.bits() - 1;
    let power = BigInt::one() << e as usize;
    let (slo, shi) = atanh_ratio(&(&a - &power), &(&a + &power));
    let (llo, lhi) = ln2_interval();
    let w = BigInt::from(e as i64 - i64::from(frac));
    let (wlo, whi) = if w.is_negative() {
        (&w * &lhi, &w * &llo)
    } else {
        (&w * &llo, &w * &lhi)
    };
    (wlo + slo * 2, whi + shi * 2)
}

/// `e^(raw / 2^frac)` as an interval `[lo, hi] · 2^-TRIG_SCALE`: the Taylor
/// series of `e^|x|` on the whole argument, without a reduction by `ln 2`,
/// each term `⌊|raw|^k · 2^TRIG_SCALE / (k! · 2^(frac·k))⌋` floored from the
/// exact rational, so each is low by less than `1`; summed until a term is
/// zero past `k > 2|x|`, where the ratio of the terms is below `½` and the
/// tail below `2`. A negative `x` takes the reciprocal. `|raw / 2^frac| < 64`.
/// Shares no code with fulcrum or `tests/common/exp.rs`.
pub fn exp(raw: i128, frac: u32) -> (BigInt, BigInt) {
    let magnitude = BigInt::from(raw.unsigned_abs());
    assert!(magnitude < BigInt::from(64u32) << frac as usize);
    let twice = (&magnitude * 2) >> frac as usize;
    let mut num = BigInt::one();
    let mut den = BigInt::one();
    let mut sum = BigInt::zero();
    let mut k = 0u64;
    loop {
        let term = (&num << TRIG_SCALE as usize) / &den;
        let done = term.is_zero() && BigInt::from(k) > twice;
        sum += term;
        if done {
            break;
        }
        k += 1;
        num *= &magnitude;
        den = (den * BigInt::from(k)) << frac as usize;
    }
    let (lo, hi) = (sum.clone(), sum + k + 3);
    if raw >= 0 {
        (lo, hi)
    } else {
        let one = BigInt::one() << (2 * TRIG_SCALE) as usize;
        (&one / &hi, &one / &lo + 1)
    }
}

/// A lower (`upper = false`) or upper bound of `2^(w · 2^-TRIG_SCALE)` at
/// `2^-TRIG_SCALE`, as [`exp2`] does it: `w = n + t`, the Taylor series of
/// `e^(t·ln 2)` at the lower or upper end of the interval of `t·ln 2`,
/// shifted by `n < 128`.
fn exp2_bound(w: &BigInt, upper: bool) -> BigInt {
    let scale = BigInt::one() << TRIG_SCALE;
    let n = w.div_floor(&scale).to_i64().unwrap();
    assert!(n < 128, "2^{} is beyond the oracle", n);
    let t = w.mod_floor(&scale);
    let (llo, lhi) = ln2_interval();
    let v = if upper {
        ((&t * &lhi) >> TRIG_SCALE) + 1
    } else {
        (&t * &llo) >> TRIG_SCALE
    };
    let mut term = BigInt::one() << TRIG_SCALE;
    let mut sum = BigInt::zero();
    let mut k = 1u64;
    while !term.is_zero() {
        sum += &term;
        term = ((term * &v) >> TRIG_SCALE) / BigInt::from(k);
        k += 1;
    }
    if upper {
        sum += 2 * k + 4;
    }
    if n >= 0 {
        sum << n as usize
    } else {
        let s = n.unsigned_abs() as usize;
        if upper {
            (sum >> s) + 1
        } else {
            sum >> s
        }
    }
}

/// `x^y` for `x = raw / 2^frac > 0` and `y = y / 2^frac_y` as an interval
/// `[lo, hi] · 2^-TRIG_SCALE`: the interval of `w = y · log₂ x` from
/// [`log2`], its lower end floored and its upper end ceiled, and the bounds
/// of `2^w` at its ends. `None` when `w ≥ 64`, beyond every type.
pub fn pow(raw: i128, frac: u32, y: i128, frac_y: u32) -> Option<(BigInt, BigInt)> {
    let (llo, lhi) = log2(raw, frac);
    let y = BigInt::from(y);
    let (a, b) = if y.is_negative() {
        (&y * &lhi, &y * &llo)
    } else {
        (&y * &llo, &y * &lhi)
    };
    let d = BigInt::one() << frac_y as usize;
    let (wlo, whi) = (a.div_floor(&d), div_ceil(&b, &d));
    if wlo >= BigInt::from(64) << TRIG_SCALE {
        return None;
    }
    Some((exp2_bound(&wlo, false), exp2_bound(&whi, true)))
}
