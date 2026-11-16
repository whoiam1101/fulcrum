//! Integers wider than the primitives, for internal use only.
//!
//! [`I256`] holds the exact state of `Accumulator64`, whose products of two
//! `i64` at scale `2^-64` overflow `i128` after a few terms. Only exact
//! operations live here; rounding stays in `kernel`. Where a primitive integer
//! has the same operation, the method has its name (`wrapping_add`,
//! `wrapping_sub`, `is_negative`).
//!
//! Written in the Rust subset that Aeneas understands: `const fn` over
//! primitives, no generic code, no closures.

/// Signed 256-bit integer in two's complement: `hi · 2^128 + lo`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub(crate) struct I256 {
    lo: u128,
    hi: i128,
}

impl I256 {
    /// `v`, sign-extended.
    #[inline]
    pub(crate) const fn from_i128(v: i128) -> Self {
        Self {
            lo: v as u128,
            hi: v >> 127,
        }
    }

    /// `self + rhs` modulo `2^256`.
    #[inline]
    pub(crate) const fn wrapping_add(self, rhs: Self) -> Self {
        let (lo, carry) = self.lo.overflowing_add(rhs.lo);
        Self {
            lo,
            hi: self.hi.wrapping_add(rhs.hi).wrapping_add(carry as i128),
        }
    }

    /// `self - rhs` modulo `2^256`.
    #[inline]
    pub(crate) const fn wrapping_sub(self, rhs: Self) -> Self {
        let (lo, borrow) = self.lo.overflowing_sub(rhs.lo);
        Self {
            lo,
            hi: self.hi.wrapping_sub(rhs.hi).wrapping_sub(borrow as i128),
        }
    }

    /// `self < 0`.
    #[inline]
    pub(crate) const fn is_negative(self) -> bool {
        self.hi < 0
    }

    /// `⌊self / 2^s⌋` for `0 < s < 128`: the arithmetic shift, exact.
    #[inline]
    pub(crate) const fn shr(self, s: u32) -> Self {
        Self {
            lo: (self.lo >> s) | ((self.hi as u128) << (128 - s)),
            hi: self.hi >> s,
        }
    }

    /// `self` as an `i128`, or `None` when it does not fit.
    #[inline]
    pub(crate) const fn to_i128(self) -> Option<i128> {
        let v = self.lo as i128;
        if self.hi == v >> 127 {
            Some(v)
        } else {
            None
        }
    }

    /// `self` clamped to the range of `i128`.
    #[inline]
    pub(crate) const fn saturating_to_i128(self) -> i128 {
        match self.to_i128() {
            Some(v) => v,
            None if self.is_negative() => i128::MIN,
            None => i128::MAX,
        }
    }

    /// `hi · 2^128 + lo`, for the proofs.
    #[cfg(kani)]
    pub(crate) const fn from_words(lo: u128, hi: i128) -> Self {
        Self { lo, hi }
    }

    /// `(lo, hi)`, for the proofs.
    #[cfg(kani)]
    pub(crate) const fn words(self) -> (u128, i128) {
        (self.lo, self.hi)
    }
}

/// The full product `a · b` as `(high, low)` 128-bit halves.
#[inline]
pub(crate) const fn widening_mul_u128(a: u128, b: u128) -> (u128, u128) {
    let (a1, a0) = (a >> 64, a as u64 as u128);
    let (b1, b0) = (b >> 64, b as u64 as u128);
    let p00 = a0 * b0;
    let p01 = a0 * b1;
    let p10 = a1 * b0;
    let mid = (p00 >> 64) + (p01 as u64 as u128) + (p10 as u64 as u128);
    let lo = (p00 as u64 as u128) | (mid << 64);
    let hi = a1 * b1 + (p01 >> 64) + (p10 >> 64) + (mid >> 64);
    (hi, lo)
}

/// `(u · 2^64 + v) / d` and its remainder for a normalized `d` (top bit
/// set) and `u < d`, so the quotient is below `2^64`: one step of Knuth's
/// algorithm D with a divisor of two 64-bit digits `d1`, `d0`. The estimate
/// `⌊u / d1⌋`, capped at `2^64 - 1`, is lowered while `q · d0 > r · 2^64 + v`
/// for `r = u - q · d1 < 2^64`; with a two-digit divisor this test is exact,
/// so the quotient is then exact. The remainder, below `d`, is the low 128
/// bits of `u · 2^64 + v - q · d`.
#[inline]
const fn div_rem_3by2(u: u128, v: u64, d: u128) -> (u128, u128) {
    let d1 = d >> 64;
    let d0 = d as u64 as u128;
    let mut q = if u >> 64 >= d1 {
        u64::MAX as u128
    } else {
        u / d1
    };
    let mut r = u - q * d1;
    while r >> 64 == 0 && q * d0 > ((r << 64) | v as u128) {
        q -= 1;
        r += d1;
    }
    let rem = ((u << 64) | v as u128).wrapping_sub(q.wrapping_mul(d));
    (q, rem)
}

/// The quotient and remainder of `hi · 2^128 + lo` by `d`, for `hi < d`, so
/// the quotient fits `u128`. One `u128` division when `hi = 0`; otherwise
/// `d` is shifted until its top bit is set, the dividend with it, and two
/// steps of [`div_rem_3by2`] give the two 64-bit digits of the quotient.
#[inline]
pub(crate) const fn div_rem_u256(hi: u128, lo: u128, d: u128) -> (u128, u128) {
    if hi == 0 {
        return (lo / d, lo % d);
    }
    let s = d.leading_zeros();
    let d = d << s;
    let (hi, lo) = if s == 0 {
        (hi, lo)
    } else {
        ((hi << s) | (lo >> (128 - s)), lo << s)
    };
    let (q1, r) = div_rem_3by2(hi, (lo >> 64) as u64, d);
    let (q0, r) = div_rem_3by2(r, lo as u64, d);
    ((q1 << 64) | q0, r >> s)
}
