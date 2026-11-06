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

    /// `spec_mul`: saturating rounded product.
    pub fn mul(self, a: i128, b: i128) -> (i128, bool) {
        let r = self.round(&(self.exact(a) * self.exact(b)));
        let fits = self.fits(&r);
        (self.saturate(r), fits)
    }

    /// `spec_div`: saturating rounded quotient; `x / 0` by the sign of `x`.
    pub fn div(self, a: i128, b: i128) -> (i128, bool) {
        if b == 0 {
            let v = match a.signum() {
                1 => self.max(),
                -1 => self.min(),
                _ => BigInt::zero(),
            };
            return (v.to_i128().unwrap(), false);
        }
        let r = self.round(&(self.exact(a) / self.exact(b)));
        let fits = self.fits(&r);
        (self.saturate(r), fits)
    }

    /// Rounded `num / den` as a raw value, `None` when out of range or `den = 0`.
    pub fn ratio(self, num: i128, den: i128) -> Option<i128> {
        if den == 0 {
            return None;
        }
        let r = self.round(&BigRational::new(BigInt::from(num), BigInt::from(den)));
        if self.fits(&r) {
            r.to_i128()
        } else {
            None
        }
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
        let r = self.round(&Self::decimal(text));
        if self.fits(&r) {
            r.to_i128()
        } else {
            None
        }
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
