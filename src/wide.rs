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
