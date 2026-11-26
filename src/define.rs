//! `define_fixed!` generates one fixed-point type from its storage type and its
//! kernel. Everything that does not depend on the width is written once here
//! and in the `impl_*!` macros of the sibling modules.

macro_rules! define_fixed {
    (
        $(#[$meta:meta])*
        $Name:ident {
            bits: $Bits:ty,
            ubits: $UBits:ty,
            int: $Int:ty,
            frac: $Frac:ty,
            frac_bits: $F:literal,
            bytes: $NB:literal,
            kernel: $k:ident,
            angle: $Angle:ident,
            from_ints: [$($FromInt:ty),*],
            try_from_ints: [$($TryFromInt:ty),*],
        }
    ) => {
        $(#[$meta])*
        #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
        #[repr(transparent)]
        pub struct $Name {
            raw: $Bits,
        }

        impl $Name {
            /// Number of fractional bits.
            pub const FRAC_BITS: u32 = $F;
            /// Number of integer bits, including the sign bit.
            pub const INT_BITS: u32 = <$Bits>::BITS - $F;
            /// `0`.
            pub const ZERO: Self = Self { raw: 0 };
            /// `1`.
            pub const ONE: Self = Self { raw: 1 << $F };
            /// `-1`.
            pub const NEG_ONE: Self = Self { raw: -(1 << $F) };
            /// `0.5`.
            pub const HALF: Self = Self { raw: 1 << ($F - 1) };
            /// The smallest value, `-2^(INT_BITS - 1)`.
            pub const MIN: Self = Self { raw: <$Bits>::MIN };
            /// The largest value, `2^(INT_BITS - 1) - 2^-FRAC_BITS`.
            pub const MAX: Self = Self { raw: <$Bits>::MAX };
            /// The smallest positive value (one ulp), `2^-FRAC_BITS`.
            pub const DELTA: Self = Self { raw: 1 };

            const FRAC_MASK: $Bits = (1 << $F) - 1;

            #[inline]
            const fn saturate(w: crate::kernel::$k::Wide) -> Self {
                Self { raw: crate::kernel::$k::saturate(w) }
            }

            #[inline]
            const fn checked(w: crate::kernel::$k::Wide) -> Option<Self> {
                Self::from_raw_option(crate::kernel::$k::narrow(w))
            }

            #[inline]
            const fn from_raw_option(raw: Option<$Bits>) -> Option<Self> {
                match raw {
                    Some(raw) => Some(Self { raw }),
                    None => None,
                }
            }

            #[inline]
            const fn wrapped(w: crate::kernel::$k::Wide) -> Self {
                Self { raw: crate::kernel::$k::wrap(w) }
            }

            #[inline]
            const fn div_by_zero(self) -> Self {
                if self.raw > 0 {
                    Self::MAX
                } else if self.raw < 0 {
                    Self::MIN
                } else {
                    Self::ZERO
                }
            }

            /// Creates a value from its raw representation: `bits / 2^FRAC_BITS`.
            #[inline]
            pub const fn from_bits(bits: $Bits) -> Self {
                Self { raw: bits }
            }

            /// The raw representation: `self · 2^FRAC_BITS`.
            #[inline]
            pub const fn to_bits(self) -> $Bits {
                self.raw
            }

            /// `int + frac / 2^FRAC_BITS`, saturating when out of range.
            ///
            /// `frac` is the raw fractional part in units of one ulp; the
            /// integer part rounds toward `-∞`, so `-1.25` is `(-2, 0.75)`.
            #[inline]
            pub const fn from_parts(int: $Int, frac: $Frac) -> Self {
                Self::saturate(crate::kernel::$k::from_parts(int, frac))
            }

            /// `int + frac / 2^FRAC_BITS`, or `None` when out of range.
            #[inline]
            pub const fn checked_from_parts(int: $Int, frac: $Frac) -> Option<Self> {
                Self::checked(crate::kernel::$k::from_parts(int, frac))
            }

            /// Integer part, rounded toward `-∞`: `-1.25` gives `-2`.
            #[inline]
            pub const fn int_part(self) -> $Int {
                (self.raw >> $F) as $Int
            }

            /// Fractional part in units of one ulp, always non-negative:
            /// `-1.25` gives `0.75 · 2^FRAC_BITS`.
            #[inline]
            pub const fn frac_part(self) -> $Frac {
                (self.raw & Self::FRAC_MASK) as $Frac
            }

            /// Converts an integer, saturating when out of range.
            #[inline]
            pub const fn saturating_from_int(n: i128) -> Self {
                Self::saturating_from_scaled_bits(n, 0)
            }

            /// Converts an integer, or `None` when out of range.
            #[inline]
            pub const fn checked_from_int(n: i128) -> Option<Self> {
                Self::checked_from_scaled_bits(n, 0)
            }

            /// `num / den` rounded to nearest (ties toward `+∞`).
            /// Saturates on overflow; `den = 0` gives `MAX`, `MIN` or `0` by the sign of `num`.
            #[inline]
            pub const fn saturating_from_ratio(num: $Bits, den: $Bits) -> Self {
                if den == 0 {
                    return Self { raw: num }.div_by_zero();
                }
                Self::saturate(crate::kernel::$k::div(num, den))
            }

            /// `num / den` rounded to nearest (ties toward `+∞`), or `None` on
            /// overflow or when `den = 0`.
            #[inline]
            pub const fn checked_from_ratio(num: $Bits, den: $Bits) -> Option<Self> {
                if den == 0 {
                    return None;
                }
                Self::checked(crate::kernel::$k::div(num, den))
            }

            /// Checked addition.
            #[inline]
            pub const fn checked_add(self, rhs: Self) -> Option<Self> {
                Self::from_raw_option(self.raw.checked_add(rhs.raw))
            }

            /// Saturating addition.
            #[inline]
            #[must_use]
            pub const fn saturating_add(self, rhs: Self) -> Self {
                Self { raw: self.raw.saturating_add(rhs.raw) }
            }

            /// Wrapping addition (modulo `2^BITS` of the raw value).
            #[inline]
            #[must_use]
            pub const fn wrapping_add(self, rhs: Self) -> Self {
                Self { raw: self.raw.wrapping_add(rhs.raw) }
            }

            /// Wrapping addition and whether it overflowed.
            #[inline]
            pub const fn overflowing_add(self, rhs: Self) -> (Self, bool) {
                let (raw, o) = self.raw.overflowing_add(rhs.raw);
                (Self { raw }, o)
            }

            /// Checked subtraction.
            #[inline]
            pub const fn checked_sub(self, rhs: Self) -> Option<Self> {
                Self::from_raw_option(self.raw.checked_sub(rhs.raw))
            }

            /// Saturating subtraction.
            #[inline]
            #[must_use]
            pub const fn saturating_sub(self, rhs: Self) -> Self {
                Self { raw: self.raw.saturating_sub(rhs.raw) }
            }

            /// Wrapping subtraction.
            #[inline]
            #[must_use]
            pub const fn wrapping_sub(self, rhs: Self) -> Self {
                Self { raw: self.raw.wrapping_sub(rhs.raw) }
            }

            /// Wrapping subtraction and whether it overflowed.
            #[inline]
            pub const fn overflowing_sub(self, rhs: Self) -> (Self, bool) {
                let (raw, o) = self.raw.overflowing_sub(rhs.raw);
                (Self { raw }, o)
            }

            /// Checked multiplication, rounded to nearest (ties toward `+∞`).
            #[inline]
            pub const fn checked_mul(self, rhs: Self) -> Option<Self> {
                Self::checked(crate::kernel::$k::mul(self.raw, rhs.raw))
            }

            /// Saturating multiplication, rounded to nearest (ties toward `+∞`).
            #[inline]
            #[must_use]
            pub const fn saturating_mul(self, rhs: Self) -> Self {
                Self::saturate(crate::kernel::$k::mul(self.raw, rhs.raw))
            }

            /// Wrapping multiplication, rounded to nearest (ties toward `+∞`).
            #[inline]
            #[must_use]
            pub const fn wrapping_mul(self, rhs: Self) -> Self {
                Self::wrapped(crate::kernel::$k::mul(self.raw, rhs.raw))
            }

            /// Wrapping multiplication and whether it overflowed.
            #[inline]
            pub const fn overflowing_mul(self, rhs: Self) -> (Self, bool) {
                let w = crate::kernel::$k::mul(self.raw, rhs.raw);
                (Self::wrapped(w), !crate::kernel::$k::fits(w))
            }

            /// Checked division, rounded to nearest (ties toward `+∞`).
            /// `None` on overflow or division by zero.
            #[inline]
            pub const fn checked_div(self, rhs: Self) -> Option<Self> {
                let w = crate::kernel::$k::div_total(self.raw, rhs.raw);
                if rhs.raw == 0 {
                    None
                } else {
                    Self::checked(w)
                }
            }

            /// Saturating division, rounded to nearest (ties toward `+∞`).
            /// Division by zero gives `MAX`, `MIN` or `0` by the sign of `self`.
            #[inline]
            #[must_use]
            pub const fn saturating_div(self, rhs: Self) -> Self {
                let w = crate::kernel::$k::div_total(self.raw, rhs.raw);
                if rhs.raw == 0 {
                    self.div_by_zero()
                } else {
                    Self::saturate(w)
                }
            }

            /// Wrapping division, rounded to nearest (ties toward `+∞`).
            /// Division by zero gives the same result as [`Self::saturating_div`].
            #[inline]
            #[must_use]
            pub const fn wrapping_div(self, rhs: Self) -> Self {
                let w = crate::kernel::$k::div_total(self.raw, rhs.raw);
                if rhs.raw == 0 {
                    self.div_by_zero()
                } else {
                    Self::wrapped(w)
                }
            }

            /// Wrapping division and whether it overflowed. Division by zero
            /// gives the result of [`Self::saturating_div`] and `true`.
            #[inline]
            pub const fn overflowing_div(self, rhs: Self) -> (Self, bool) {
                let w = crate::kernel::$k::div_total(self.raw, rhs.raw);
                if rhs.raw == 0 {
                    (self.div_by_zero(), true)
                } else {
                    (Self::wrapped(w), !crate::kernel::$k::fits(w))
                }
            }

            /// Checked remainder `self - rhs · trunc(self / rhs)` (exact, sign of `self`).
            /// `None` when `rhs = 0`.
            #[inline]
            pub const fn checked_rem(self, rhs: Self) -> Option<Self> {
                if rhs.raw == 0 {
                    None
                } else {
                    Some(Self { raw: self.raw.wrapping_rem(rhs.raw) })
                }
            }

            /// Remainder; `rhs = 0` gives `0`. The remainder is exact and never overflows.
            #[inline]
            #[must_use]
            pub const fn saturating_rem(self, rhs: Self) -> Self {
                if rhs.raw == 0 {
                    Self::ZERO
                } else {
                    Self { raw: self.raw.wrapping_rem(rhs.raw) }
                }
            }

            /// Same as [`Self::saturating_rem`].
            #[inline]
            #[must_use]
            pub const fn wrapping_rem(self, rhs: Self) -> Self {
                self.saturating_rem(rhs)
            }

            /// Remainder and whether `rhs` was zero.
            #[inline]
            pub const fn overflowing_rem(self, rhs: Self) -> (Self, bool) {
                (self.saturating_rem(rhs), rhs.raw == 0)
            }

            /// Checked negation; `None` for `MIN`.
            #[inline]
            pub const fn checked_neg(self) -> Option<Self> {
                Self::from_raw_option(self.raw.checked_neg())
            }

            /// Saturating negation; `-MIN` gives `MAX`.
            #[inline]
            #[must_use]
            pub const fn saturating_neg(self) -> Self {
                Self { raw: self.raw.saturating_neg() }
            }

            /// Wrapping negation; `-MIN` gives `MIN`.
            #[inline]
            #[must_use]
            pub const fn wrapping_neg(self) -> Self {
                Self { raw: self.raw.wrapping_neg() }
            }

            /// Wrapping negation and whether it overflowed.
            #[inline]
            pub const fn overflowing_neg(self) -> (Self, bool) {
                let (raw, o) = self.raw.overflowing_neg();
                (Self { raw }, o)
            }

            /// Absolute value, saturating: `abs(MIN)` gives `MAX`.
            #[inline]
            #[must_use]
            pub const fn abs(self) -> Self {
                self.saturating_abs()
            }

            /// Checked absolute value; `None` for `MIN`.
            #[inline]
            pub const fn checked_abs(self) -> Option<Self> {
                Self::from_raw_option(self.raw.checked_abs())
            }

            /// Saturating absolute value.
            #[inline]
            #[must_use]
            pub const fn saturating_abs(self) -> Self {
                Self { raw: self.raw.saturating_abs() }
            }

            /// Wrapping absolute value; `abs(MIN)` gives `MIN`.
            #[inline]
            #[must_use]
            pub const fn wrapping_abs(self) -> Self {
                Self { raw: self.raw.wrapping_abs() }
            }

            /// Wrapping absolute value and whether it overflowed.
            #[inline]
            pub const fn overflowing_abs(self) -> (Self, bool) {
                let (raw, o) = self.raw.overflowing_abs();
                (Self { raw }, o)
            }

            /// Multiplication by an integer, saturating. Exact, no rounding.
            #[inline]
            #[must_use]
            pub const fn mul_int(self, n: $Bits) -> Self {
                Self { raw: self.raw.saturating_mul(n) }
            }

            /// Multiplication by an integer, or `None` on overflow.
            #[inline]
            pub const fn checked_mul_int(self, n: $Bits) -> Option<Self> {
                Self::from_raw_option(self.raw.checked_mul(n))
            }

            /// Wrapping multiplication by an integer.
            #[inline]
            #[must_use]
            pub const fn wrapping_mul_int(self, n: $Bits) -> Self {
                Self { raw: self.raw.wrapping_mul(n) }
            }

            /// `self · 2^n`, or `None` on overflow. Exact.
            #[inline]
            pub const fn checked_shl(self, n: u32) -> Option<Self> {
                match crate::kernel::$k::shl(self.raw, n) {
                    (raw, false) => Some(Self { raw }),
                    (_, true) => None,
                }
            }

            /// `self · 2^n`, saturating; the operator `<<` does the same. Exact
            /// when in range; any `n` is accepted, `n ≥ BITS` gives `0`, `MAX` or `MIN`.
            #[inline]
            #[must_use]
            pub const fn saturating_shl(self, n: u32) -> Self {
                match crate::kernel::$k::shl(self.raw, n) {
                    (raw, false) => Self { raw },
                    (_, true) => self.div_by_zero(),
                }
            }

            /// `self · 2^n` modulo `2^BITS` of the raw value; `n ≥ BITS` gives `0`.
            /// Unlike `wrapping_shl` of the primitive integers, `n` is not masked.
            #[inline]
            #[must_use]
            pub const fn wrapping_shl(self, n: u32) -> Self {
                Self { raw: crate::kernel::$k::shl(self.raw, n).0 }
            }

            /// `self / 2^n`, rounded to nearest (ties toward `+∞`); the operator
            /// `>>` does the same, so `x >> 1 == x / 2`. Never overflows; any `n`
            /// is accepted, `n ≥ BITS` gives `0`.
            #[inline]
            #[must_use]
            pub const fn shr_round(self, n: u32) -> Self {
                Self { raw: crate::kernel::$k::shr(self.raw, n) }
            }

            /// Division by an integer, rounded to nearest (ties toward `+∞`),
            /// saturating. `n = 0` gives `MAX`, `MIN` or `0` by the sign of `self`.
            #[inline]
            #[must_use]
            pub const fn div_int(self, n: $Bits) -> Self {
                if n == 0 {
                    return self.div_by_zero();
                }
                Self::saturate(crate::kernel::$k::div_int(self.raw, n))
            }

            /// Division by an integer, rounded to nearest (ties toward `+∞`),
            /// or `None` on overflow or when `n = 0`.
            #[inline]
            pub const fn checked_div_int(self, n: $Bits) -> Option<Self> {
                if n == 0 {
                    return None;
                }
                Self::checked(crate::kernel::$k::div_int(self.raw, n))
            }

            /// `1 / self`, saturating; `1 / 0` gives `MAX`.
            #[inline]
            #[must_use]
            pub const fn recip(self) -> Self {
                Self::ONE.saturating_div(self)
            }

            /// `1 / self`, or `None` on overflow or when `self = 0`.
            #[inline]
            pub const fn checked_recip(self) -> Option<Self> {
                Self::ONE.checked_div(self)
            }

            /// `self · self`, saturating.
            #[inline]
            #[must_use]
            pub const fn sqr(self) -> Self {
                self.saturating_mul(self)
            }

            /// `√self`, correctly rounded to nearest; never overflows. A
            /// negative `self` gives `0`.
            #[inline]
            #[must_use]
            pub const fn sqrt(self) -> Self {
                match self.checked_sqrt() {
                    Some(root) => root,
                    None => Self::ZERO,
                }
            }

            /// `√self`, correctly rounded, or `None` when `self < 0`.
            #[inline]
            pub const fn checked_sqrt(self) -> Option<Self> {
                if self.raw < 0 {
                    return None;
                }
                Some(Self { raw: crate::kernel::$k::sqrt(self.raw) })
            }

            /// `1 / √self`, correctly rounded to nearest; never overflows for
            /// `self > 0`. `self ≤ 0` gives `MAX`, like `1 / 0` in [`Self::recip`].
            #[inline]
            #[must_use]
            pub const fn rsqrt(self) -> Self {
                match self.checked_rsqrt() {
                    Some(root) => root,
                    None => Self::MAX,
                }
            }

            /// `1 / √self`, correctly rounded, or `None` when `self ≤ 0`.
            #[inline]
            pub const fn checked_rsqrt(self) -> Option<Self> {
                if self.raw <= 0 {
                    return None;
                }
                Some(Self { raw: crate::kernel::$k::rsqrt(self.raw) })
            }

            /// `√(self² + other²)`, correctly rounded to nearest and
            /// saturated: the squares are exact, so nothing overflows before
            /// the root.
            #[inline]
            #[must_use]
            pub const fn hypot(self, other: Self) -> Self {
                Self::saturate(crate::kernel::$k::hypot(self.raw, other.raw))
            }

            /// `√(self² + other²)`, correctly rounded, or `None` when the
            /// result is out of range.
            #[inline]
            pub const fn checked_hypot(self, other: Self) -> Option<Self> {
                Self::checked(crate::kernel::$k::hypot(self.raw, other.raw))
            }

            /// `sin(2π · self)`: the sine of an angle of `self` turns
            /// (1 turn = 360°), within 1 ulp. Only the fraction of a turn
            /// matters, so the range reduction is exact and never overflows;
            /// the result is in `[-1, 1]`, and `sin_turns(-x) = -sin_turns(x)`
            /// bit for bit for every `x > MIN` (`-MIN` saturates to `MAX`).
            #[inline]
            #[must_use]
            pub const fn sin_turns(self) -> Self {
                Self { raw: crate::trig::sin_turns(self.raw as u64, $F) as $Bits }
            }

            /// `cos(2π · self)`: the cosine of an angle of `self` turns,
            /// within 1 ulp; `cos_turns(x) = sin_turns(x + ¼)` and
            /// `cos_turns(-x) = cos_turns(x)` bit for bit for every `x > MIN`.
            #[inline]
            #[must_use]
            pub const fn cos_turns(self) -> Self {
                Self { raw: crate::trig::cos_turns(self.raw as u64, $F) as $Bits }
            }

            /// `sin(self)` of an angle of `self` radians, within 1 ulp. The
            /// range reduction multiplies by 192 bits of `2/π` exactly, so it
            /// loses nothing on any input; the result is in `[-1, 1]`, and
            /// `sin(-x) = -sin(x)` bit for bit for every `x > MIN`.
            #[inline]
            #[must_use]
            pub const fn sin(self) -> Self {
                Self { raw: crate::trig::sin(self.raw as i64, $F) as $Bits }
            }

            /// `cos(self)` of an angle of `self` radians, within 1 ulp;
            /// `cos(-x) = cos(x)` bit for bit for every `x > MIN`.
            #[inline]
            #[must_use]
            pub const fn cos(self) -> Self {
                Self { raw: crate::trig::cos(self.raw as i64, $F) as $Bits }
            }

            /// `(self.sin(), self.cos())` with one range reduction.
            #[inline]
            pub const fn sin_cos(self) -> (Self, Self) {
                let (s, c) = crate::trig::sin_cos(self.raw as i64, $F);
                (Self { raw: s as $Bits }, Self { raw: c as $Bits })
            }

            /// `tan(self)` of an angle of `self` radians, within 1 ulp and
            /// saturated near the poles; `tan(-x) = -tan(x)` bit for bit for
            /// every `x > MIN`.
            #[inline]
            #[must_use]
            pub const fn tan(self) -> Self {
                Self::saturate(crate::trig::tan(self.raw as i64, $F) as crate::kernel::$k::Wide)
            }

            /// `tan(self)` within 1 ulp, or `None` when the rounded result
            /// is out of range.
            #[inline]
            pub const fn checked_tan(self) -> Option<Self> {
                Self::checked(crate::trig::tan(self.raw as i64, $F) as crate::kernel::$k::Wide)
            }

            /// `atan(self)` in radians, in `[-π/2, π/2]`, within 1 ulp;
            /// never overflows, and `atan(-x) = -atan(x)` bit for bit for every
            /// `x > MIN`.
            #[inline]
            #[must_use]
            pub const fn atan(self) -> Self {
                Self { raw: crate::trig::atan(self.raw as i64, $F) as $Bits }
            }

            /// The angle of the point `(other, self)` in radians, within 1 ulp;
            /// `self` is `y`, as in the `atan2` of floats. The exact angle is
            /// in `(-π, π]`, the rounded one in `[-π, π]`: just below the cut
            /// along the negative axis it rounds to `-π`. `atan2(0, 0) = 0`,
            /// `atan2(0, x < 0) = π`. Odd in `self ≠ 0` bit for bit; nothing
            /// overflows, whatever the magnitudes.
            #[inline]
            #[must_use]
            pub const fn atan2(self, other: Self) -> Self {
                Self { raw: crate::trig::atan2(self.raw as i64, other.raw as i64, $F) as $Bits }
            }

            /// `asin(self)` in radians, in `[-π/2, π/2]`, within 1 ulp;
            /// `self` outside `[-1, 1]` is clamped to it, so it gives `±π/2`.
            /// `asin(-x) = -asin(x)` bit for bit.
            #[inline]
            #[must_use]
            pub const fn asin(self) -> Self {
                Self { raw: crate::trig::asin(self.clamp_unit(), $F) as $Bits }
            }

            /// `asin(self)` within 1 ulp, or `None` when `self` is outside
            /// `[-1, 1]`.
            #[inline]
            pub const fn checked_asin(self) -> Option<Self> {
                if self.clamp_unit() != self.raw as i64 {
                    return None;
                }
                Some(Self { raw: crate::trig::asin(self.raw as i64, $F) as $Bits })
            }

            /// `acos(self)` in radians, in `[0, π]`, within 1 ulp; `self`
            /// outside `[-1, 1]` is clamped to it, so it gives `0` or `π`.
            #[inline]
            #[must_use]
            pub const fn acos(self) -> Self {
                Self { raw: crate::trig::acos(self.clamp_unit(), $F) as $Bits }
            }

            /// `acos(self)` within 1 ulp, or `None` when `self` is outside
            /// `[-1, 1]`.
            #[inline]
            pub const fn checked_acos(self) -> Option<Self> {
                if self.clamp_unit() != self.raw as i64 {
                    return None;
                }
                Some(Self { raw: crate::trig::acos(self.raw as i64, $F) as $Bits })
            }

            /// The raw value of `self` clamped to `[-1, 1]`.
            #[inline]
            const fn clamp_unit(self) -> i64 {
                self.clamp(Self::NEG_ONE, Self::ONE).raw as i64
            }

            /// `2^self`, correctly rounded to nearest on every
            /// `FixedFloat8`, `FixedFloat16` and `FixedFloat32` and within 1
            /// ulp on `FixedFloat64`, saturated to `MAX` above the range;
            /// exact on integers `≥ -FRAC_BITS`, and `0` below `-FRAC_BITS - 1`. The split
            /// into the integer and the fraction is exact, so nothing is lost
            /// on any input.
            #[inline]
            #[must_use]
            pub const fn exp2(self) -> Self {
                Self::saturate(crate::exp::exp2(self.raw as i64, $F) as crate::kernel::$k::Wide)
            }

            /// `2^self` as [`Self::exp2`], or `None` when the rounded result
            /// is out of range.
            #[inline]
            pub const fn checked_exp2(self) -> Option<Self> {
                Self::checked(crate::exp::exp2(self.raw as i64, $F) as crate::kernel::$k::Wide)
            }

            /// `e^self`, correctly rounded to nearest on every
            /// `FixedFloat8`, `FixedFloat16` and `FixedFloat32` and within 1
            /// ulp on `FixedFloat64`, saturated to `MAX` above the range and
            /// `0` far below it; exact at `0`.
            #[inline]
            #[must_use]
            pub const fn exp(self) -> Self {
                Self::saturate(crate::exp::exp(self.raw as i64, $F) as crate::kernel::$k::Wide)
            }

            /// `e^self` as [`Self::exp`], or `None` when the rounded result
            /// is out of range.
            #[inline]
            pub const fn checked_exp(self) -> Option<Self> {
                Self::checked(crate::exp::exp(self.raw as i64, $F) as crate::kernel::$k::Wide)
            }

            /// `log₂(self)`, correctly rounded to nearest on every
            /// `FixedFloat8`, `FixedFloat16` and `FixedFloat32` and within 1
            /// ulp on `FixedFloat64`; never overflows, exact on powers of
            /// two. `self ≤ 0` gives `MIN`, the saturation of `-∞`.
            #[inline]
            #[must_use]
            pub const fn log2(self) -> Self {
                match self.checked_log2() {
                    Some(v) => v,
                    None => Self::MIN,
                }
            }

            /// `log₂(self)` as [`Self::log2`], or `None` when `self ≤ 0`.
            #[inline]
            pub const fn checked_log2(self) -> Option<Self> {
                if self.raw <= 0 {
                    return None;
                }
                Some(Self { raw: crate::exp::log2(self.raw as i64, $F) as $Bits })
            }

            /// `ln(self)`, the natural logarithm, correctly rounded to
            /// nearest on every `FixedFloat8`, `FixedFloat16` and
            /// `FixedFloat32` and within 1 ulp on `FixedFloat64`; never
            /// overflows, exact at `1`. `self ≤ 0` gives `MIN`, the
            /// saturation of `-∞`.
            #[inline]
            #[must_use]
            pub const fn ln(self) -> Self {
                match self.checked_ln() {
                    Some(v) => v,
                    None => Self::MIN,
                }
            }

            /// `ln(self)` as [`Self::ln`], or `None` when `self ≤ 0`.
            #[inline]
            pub const fn checked_ln(self) -> Option<Self> {
                if self.raw <= 0 {
                    return None;
                }
                Some(Self { raw: crate::exp::ln(self.raw as i64, $F) as $Bits })
            }

            /// `self^y` as `2^(y · log₂ self)`, within 1 ulp on every width:
            /// correctly rounded on every pair of `FixedFloat8` and
            /// `FixedFloat16` except an exact power halfway between two
            /// values, which may round either way, and within
            /// `½ + 2^-5.7` ulp on `FixedFloat64`; saturated to `MAX` or `MIN`
            /// by the sign of the result. `x^0 = 1` for every `x`, `0^y` is `0` for `y > 0`
            /// and `MAX` for `y < 0`; a negative `self` takes the sign of an
            /// odd integer `y` and gives `0` for a `y` that is not an
            /// integer. Exact when `y · log₂ self` is an exact integer, as for
            /// powers of two.
            #[inline]
            #[must_use]
            pub const fn pow(self, y: Self) -> Self {
                match crate::exp::pow(self.raw as i64, $F, y.raw as i64, $F) {
                    Some(v) => Self::saturate(v as crate::kernel::$k::Wide),
                    None => Self::ZERO,
                }
            }

            /// `self^y` as [`Self::pow`], or `None` when the rounded result
            /// is out of range (also `0^y` for `y < 0`) or `self < 0` and `y`
            /// is not an integer.
            #[inline]
            pub const fn checked_pow(self, y: Self) -> Option<Self> {
                match crate::exp::pow(self.raw as i64, $F, y.raw as i64, $F) {
                    Some(v) => Self::checked(v as crate::kernel::$k::Wide),
                    None => None,
                }
            }

            /// `self^n` for an integer `n`, as [`Self::pow`] of `n` without
            /// the range of `Self` on the exponent: `x^0 = 1`, the sign of a
            /// negative `self` for odd `n`, `0^n` is `MAX` for `n < 0`.
            #[inline]
            #[must_use]
            pub const fn powi(self, n: i32) -> Self {
                match crate::exp::pow(self.raw as i64, $F, n as i64, 0) {
                    Some(v) => Self::saturate(v as crate::kernel::$k::Wide),
                    None => Self::ZERO,
                }
            }

            /// `self^n` as [`Self::powi`], or `None` when the rounded result
            /// is out of range, also for `self = 0` and `n < 0`.
            #[inline]
            pub const fn checked_powi(self, n: i32) -> Option<Self> {
                match crate::exp::pow(self.raw as i64, $F, n as i64, 0) {
                    Some(v) => Self::checked(v as crate::kernel::$k::Wide),
                    None => None,
                }
            }

            /// `-1`, `0` or `1` by the sign of `self`.
            #[inline]
            #[must_use]
            pub const fn signum(self) -> Self {
                if self.raw > 0 {
                    Self::ONE
                } else if self.raw < 0 {
                    Self::NEG_ONE
                } else {
                    Self::ZERO
                }
            }

            /// `self < 0`.
            #[inline]
            pub const fn is_negative(self) -> bool {
                self.raw < 0
            }

            /// `self > 0`.
            #[inline]
            pub const fn is_positive(self) -> bool {
                self.raw > 0
            }

            /// `self == 0`.
            #[inline]
            pub const fn is_zero(self) -> bool {
                self.raw == 0
            }

            /// The smaller of two values.
            #[inline]
            #[must_use]
            pub const fn min(self, other: Self) -> Self {
                if other.raw < self.raw {
                    other
                } else {
                    self
                }
            }

            /// The larger of two values.
            #[inline]
            #[must_use]
            pub const fn max(self, other: Self) -> Self {
                if other.raw > self.raw {
                    other
                } else {
                    self
                }
            }

            /// Restricts `self` to `[lo, hi]`. Never panics: when `lo > hi` the result is `hi`.
            #[inline]
            #[must_use]
            pub const fn clamp(self, lo: Self, hi: Self) -> Self {
                self.max(lo).min(hi)
            }

            /// `|self - other|`, saturating.
            #[inline]
            #[must_use]
            pub const fn abs_diff(self, other: Self) -> Self {
                if self.raw >= other.raw {
                    self.saturating_sub(other)
                } else {
                    other.saturating_sub(self)
                }
            }

            /// `(self + other) / 2` without overflow, rounded to nearest (ties toward `+∞`).
            #[inline]
            #[must_use]
            pub const fn midpoint(self, other: Self) -> Self {
                Self { raw: crate::kernel::$k::midpoint(self.raw, other.raw) }
            }

            /// `self · a + b`, rounded once to nearest (ties toward `+∞`) and
            /// saturated once: the product is neither rounded nor saturated
            /// before the addition.
            #[inline]
            #[must_use]
            pub const fn mul_add(self, a: Self, b: Self) -> Self {
                Self::saturate(crate::kernel::$k::mul_add(self.raw, a.raw, b.raw))
            }

            /// `self · a + b`, rounded once, or `None` when the result is out
            /// of range. An out of range product does not fail by itself.
            #[inline]
            pub const fn checked_mul_add(self, a: Self, b: Self) -> Option<Self> {
                Self::checked(crate::kernel::$k::mul_add(self.raw, a.raw, b.raw))
            }

            /// `self · a / b`, rounded once to nearest (ties toward `+∞`) and
            /// saturated: the product is exact, so it neither overflows nor
            /// loses bits before the division. `b = 0` gives `MAX`, `MIN` or `0`
            /// by the sign of `self · a`.
            #[inline]
            #[must_use]
            pub const fn mul_div(self, a: Self, b: Self) -> Self {
                if b.raw == 0 {
                    return Self { raw: self.raw.signum() * a.raw.signum() }.div_by_zero();
                }
                Self::saturate(crate::kernel::$k::mul_div(self.raw, a.raw, b.raw))
            }

            /// `self · a / b`, rounded once, or `None` when the result is out
            /// of range or `b = 0`.
            #[inline]
            pub const fn checked_mul_div(self, a: Self, b: Self) -> Option<Self> {
                if b.raw == 0 {
                    return None;
                }
                Self::checked(crate::kernel::$k::mul_div(self.raw, a.raw, b.raw))
            }

            /// Linear interpolation `self + (other - self) · t`, rounded once to
            /// nearest (ties toward `+∞`) and saturated. `t = 0` gives `self`
            /// and `t = 1` gives `other` exactly; `t` outside `[0, 1]`
            /// extrapolates. The difference is exact, so it never overflows.
            #[inline]
            #[must_use]
            pub const fn lerp(self, other: Self, t: Self) -> Self {
                Self::saturate(crate::kernel::$k::lerp(self.raw, other.raw, t.raw))
            }

            /// Linear interpolation `self + (other - self) · t`, rounded once,
            /// or `None` when the result is out of range.
            #[inline]
            pub const fn checked_lerp(self, other: Self, t: Self) -> Option<Self> {
                Self::checked(crate::kernel::$k::lerp(self.raw, other.raw, t.raw))
            }
        }

        impl crate::sealed::Sealed for $Name {}

        impl crate::sealed::Fixed for $Name {
            #[inline]
            fn __raw_i128(self, _: crate::sealed::Token) -> i128 {
                i128::from(self.raw)
            }
            #[inline]
            fn __det(a: Self, b: Self, c: Self, d: Self, _: crate::sealed::Token) -> Self {
                Self::saturate(crate::kernel::$k::det(a.raw, b.raw, c.raw, d.raw))
            }
            #[inline]
            fn __dot(a: &[Self], b: &[Self], _: crate::sealed::Token) -> Self {
                Self::dot_slices(a, b)
            }
            #[inline]
            fn __hypot3(a: Self, b: Self, c: Self, _: crate::sealed::Token) -> Self {
                Self::saturate(crate::kernel::$k::hypot3(a.raw, b.raw, c.raw))
            }
            #[inline]
            fn __scale_to(v: [Self; 3], len: Self, _: crate::sealed::Token) -> [Self; 3] {
                let r = crate::kernel::$k::scale_vec(v[0].raw, v[1].raw, v[2].raw, len.raw);
                [Self { raw: r[0] }, Self { raw: r[1] }, Self { raw: r[2] }]
            }
            #[inline]
            fn __cmp_length(v: [Self; 3], len: Self, _: crate::sealed::Token) -> core::cmp::Ordering {
                match crate::kernel::$k::cmp_length(v[0].raw, v[1].raw, v[2].raw, len.raw) {
                    -1 => core::cmp::Ordering::Less,
                    0 => core::cmp::Ordering::Equal,
                    _ => core::cmp::Ordering::Greater,
                }
            }
            #[inline]
            fn __rotate(x: Self, y: Self, angle: crate::$Angle, _: crate::sealed::Token) -> (Self, Self) {
                let (rx, ry) = crate::trig::rotate(
                    i64::from(x.raw),
                    i64::from(y.raw),
                    u64::from(angle.to_bits()),
                    <$Bits>::BITS,
                );
                (
                    Self::saturating_from_scaled_bits(rx, $F),
                    Self::saturating_from_scaled_bits(ry, $F),
                )
            }
            #[inline]
            fn __angle2(a: [Self; 2], b: [Self; 2], _: crate::sealed::Token) -> Self {
                Self::saturating_from_scaled_bits(
                    i128::from(crate::trig::angle_between2(
                        i64::from(a[0].raw),
                        i64::from(a[1].raw),
                        i64::from(b[0].raw),
                        i64::from(b[1].raw),
                        $F,
                    )),
                    $F,
                )
            }
            #[inline]
            fn __angle3(a: [Self; 3], b: [Self; 3], _: crate::sealed::Token) -> Self {
                Self::saturating_from_scaled_bits(
                    i128::from(crate::trig::angle_between3(
                        [i64::from(a[0].raw), i64::from(a[1].raw), i64::from(a[2].raw)],
                        [i64::from(b[0].raw), i64::from(b[1].raw), i64::from(b[2].raw)],
                        $F,
                    )),
                    $F,
                )
            }
        }

        impl crate::FixedFloat for $Name {
            type Angle = crate::$Angle;
            type Bits = $Bits;
            const FRAC_BITS: u32 = $F;
            const INT_BITS: u32 = <$Bits>::BITS - $F;
            const ZERO: Self = Self::ZERO;
            const ONE: Self = Self::ONE;
            const NEG_ONE: Self = Self::NEG_ONE;
            const HALF: Self = Self::HALF;
            const MIN: Self = Self::MIN;
            const MAX: Self = Self::MAX;
            const DELTA: Self = Self::DELTA;
            const PI: Self = Self::PI;
            const TAU: Self = Self::TAU;
            const FRAC_PI_2: Self = Self::FRAC_PI_2;
            const E: Self = Self::E;
            const SQRT_2: Self = Self::SQRT_2;

            #[inline]
            fn from_bits(bits: $Bits) -> Self {
                Self::from_bits(bits)
            }
            #[inline]
            fn to_bits(self) -> $Bits {
                self.raw
            }
            #[inline]
            fn saturating_from_int(n: i128) -> Self {
                Self::saturating_from_int(n)
            }
            #[inline]
            fn checked_from_int(n: i128) -> Option<Self> {
                Self::checked_from_int(n)
            }
            #[inline]
            fn checked_add(self, rhs: Self) -> Option<Self> {
                Self::checked_add(self, rhs)
            }
            #[inline]
            fn checked_sub(self, rhs: Self) -> Option<Self> {
                Self::checked_sub(self, rhs)
            }
            #[inline]
            fn checked_mul(self, rhs: Self) -> Option<Self> {
                Self::checked_mul(self, rhs)
            }
            #[inline]
            fn checked_div(self, rhs: Self) -> Option<Self> {
                Self::checked_div(self, rhs)
            }
            #[inline]
            fn wrapping_add(self, rhs: Self) -> Self {
                Self::wrapping_add(self, rhs)
            }
            #[inline]
            fn wrapping_sub(self, rhs: Self) -> Self {
                Self::wrapping_sub(self, rhs)
            }
            #[inline]
            fn wrapping_mul(self, rhs: Self) -> Self {
                Self::wrapping_mul(self, rhs)
            }
            #[inline]
            fn abs(self) -> Self {
                Self::abs(self)
            }
            #[inline]
            fn is_negative(self) -> bool {
                Self::is_negative(self)
            }
            #[inline]
            fn floor(self) -> Self {
                Self::floor(self)
            }
            #[inline]
            fn ceil(self) -> Self {
                Self::ceil(self)
            }
            #[inline]
            fn round(self) -> Self {
                Self::round(self)
            }
            #[inline]
            fn sqrt(self) -> Self {
                Self::sqrt(self)
            }
            #[inline]
            fn sin_cos(self) -> (Self, Self) {
                Self::sin_cos(self)
            }
            #[inline]
            fn atan2(self, other: Self) -> Self {
                Self::atan2(self, other)
            }
            #[inline]
            fn hypot(self, other: Self) -> Self {
                Self::hypot(self, other)
            }
            #[inline]
            fn lerp(self, other: Self, t: Self) -> Self {
                Self::lerp(self, other, t)
            }
            #[inline]
            fn log2(self) -> Self {
                Self::log2(self)
            }
            #[inline]
            fn exp2(self) -> Self {
                Self::exp2(self)
            }
            #[inline]
            fn ln(self) -> Self {
                Self::ln(self)
            }
            #[inline]
            fn exp(self) -> Self {
                Self::exp(self)
            }
            #[inline]
            fn pow(self, y: Self) -> Self {
                Self::pow(self, y)
            }
            #[inline]
            fn powi(self, n: i32) -> Self {
                Self::powi(self, n)
            }
        }

        impl_ops!($Name);
        impl_round!($Name, $Bits, $F, $k);
        impl_convert!($Name, $Bits, $F, [$($FromInt),*], [$($TryFromInt),*]);
        impl_fmt!($Name, $UBits, $NB);
        impl_parse!($Name, $F);
        impl_bytes!($Name, $Bits, $NB);
        #[cfg(feature = "float-convert")]
        impl_float!($Name, $F);
        #[cfg(feature = "serde")]
        impl_serde!($Name, $Bits);
        #[cfg(feature = "bytemuck")]
        impl_pod!($Name);
        #[cfg(feature = "num-traits")]
        impl_num_traits!($Name);
    };
}

define_fixed! {
    /// Signed fixed-point number in Q4.4 format: 8 bits, 4 of them fractional.
    ///
    /// Range `[-8, 7.9375]`, step `2^-4 = 0.0625`.
    FixedFloat8 {
        bits: i8,
        ubits: u8,
        int: i8,
        frac: u8,
        frac_bits: 4,
        bytes: 1,
        kernel: k8,
        angle: Angle8,
        from_ints: [],
        try_from_ints: [i8, i16, i32, i64, i128, u8, u16, u32, u64, u128],
    }
}

define_fixed! {
    /// Signed fixed-point number in Q8.8 format: 16 bits, 8 of them fractional.
    ///
    /// Range `[-128, 127.99609375]`, step `2^-8 ≈ 0.0039`.
    FixedFloat16 {
        bits: i16,
        ubits: u16,
        int: i8,
        frac: u8,
        frac_bits: 8,
        bytes: 2,
        kernel: k16,
        angle: Angle16,
        from_ints: [i8],
        try_from_ints: [i16, i32, i64, i128, u8, u16, u32, u64, u128],
    }
}

define_fixed! {
    /// Signed fixed-point number in Q16.16 format: 32 bits, 16 of them fractional.
    ///
    /// Range `[-32768, 32767.99998]`, step `2^-16 ≈ 1.5·10⁻⁵`.
    FixedFloat32 {
        bits: i32,
        ubits: u32,
        int: i16,
        frac: u16,
        frac_bits: 16,
        bytes: 4,
        kernel: k32,
        angle: Angle32,
        from_ints: [i8, u8, i16],
        try_from_ints: [i32, i64, i128, u16, u32, u64, u128],
    }
}

define_fixed! {
    /// Signed fixed-point number in Q32.32 format: 64 bits, 32 of them fractional.
    ///
    /// Range `±2.1·10⁹`, step `2^-32 ≈ 2.3·10⁻¹⁰`.
    FixedFloat64 {
        bits: i64,
        ubits: u64,
        int: i32,
        frac: u32,
        frac_bits: 32,
        bytes: 8,
        kernel: k64,
        angle: Angle64,
        from_ints: [i8, u8, i16, u16, i32],
        try_from_ints: [i64, i128, u32, u64, u128],
    }
}

impl_accumulator!(Accumulator8, FixedFloat8, 4, state: state128);
impl_accumulator!(Accumulator16, FixedFloat16, 8, state: state128);
impl_accumulator!(Accumulator32, FixedFloat32, 16, state: state128);
impl_accumulator!(Accumulator64, FixedFloat64, 32, state: state256);

impl_widen!(FixedFloat8 => FixedFloat16, FixedFloat32, FixedFloat64);
impl_widen!(FixedFloat16 => FixedFloat32, FixedFloat64);
impl_widen!(FixedFloat32 => FixedFloat64);
impl_narrow!(FixedFloat16 => FixedFloat8);
impl_narrow!(FixedFloat32 => FixedFloat8, FixedFloat16);
impl_narrow!(FixedFloat64 => FixedFloat8, FixedFloat16, FixedFloat32);
