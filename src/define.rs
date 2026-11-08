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
                match crate::kernel::$k::narrow(w) {
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
                match self.raw.checked_add(rhs.raw) {
                    Some(raw) => Some(Self { raw }),
                    None => None,
                }
            }

            /// Saturating addition.
            #[inline]
            pub const fn saturating_add(self, rhs: Self) -> Self {
                Self { raw: self.raw.saturating_add(rhs.raw) }
            }

            /// Wrapping addition (modulo `2^BITS` of the raw value).
            #[inline]
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
                match self.raw.checked_sub(rhs.raw) {
                    Some(raw) => Some(Self { raw }),
                    None => None,
                }
            }

            /// Saturating subtraction.
            #[inline]
            pub const fn saturating_sub(self, rhs: Self) -> Self {
                Self { raw: self.raw.saturating_sub(rhs.raw) }
            }

            /// Wrapping subtraction.
            #[inline]
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
            pub const fn saturating_mul(self, rhs: Self) -> Self {
                Self::saturate(crate::kernel::$k::mul(self.raw, rhs.raw))
            }

            /// Wrapping multiplication, rounded to nearest (ties toward `+∞`).
            #[inline]
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
            pub const fn saturating_rem(self, rhs: Self) -> Self {
                if rhs.raw == 0 {
                    Self::ZERO
                } else {
                    Self { raw: self.raw.wrapping_rem(rhs.raw) }
                }
            }

            /// Same as [`Self::saturating_rem`].
            #[inline]
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
                match self.raw.checked_neg() {
                    Some(raw) => Some(Self { raw }),
                    None => None,
                }
            }

            /// Saturating negation; `-MIN` gives `MAX`.
            #[inline]
            pub const fn saturating_neg(self) -> Self {
                Self { raw: self.raw.saturating_neg() }
            }

            /// Wrapping negation; `-MIN` gives `MIN`.
            #[inline]
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
            pub const fn abs(self) -> Self {
                self.saturating_abs()
            }

            /// Checked absolute value; `None` for `MIN`.
            #[inline]
            pub const fn checked_abs(self) -> Option<Self> {
                match self.raw.checked_abs() {
                    Some(raw) => Some(Self { raw }),
                    None => None,
                }
            }

            /// Saturating absolute value.
            #[inline]
            pub const fn saturating_abs(self) -> Self {
                Self { raw: self.raw.saturating_abs() }
            }

            /// Wrapping absolute value; `abs(MIN)` gives `MIN`.
            #[inline]
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
            pub const fn mul_int(self, n: $Bits) -> Self {
                Self { raw: self.raw.saturating_mul(n) }
            }

            /// Multiplication by an integer, or `None` on overflow.
            #[inline]
            pub const fn checked_mul_int(self, n: $Bits) -> Option<Self> {
                match self.raw.checked_mul(n) {
                    Some(raw) => Some(Self { raw }),
                    None => None,
                }
            }

            /// Wrapping multiplication by an integer.
            #[inline]
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
            pub const fn saturating_shl(self, n: u32) -> Self {
                match crate::kernel::$k::shl(self.raw, n) {
                    (raw, false) => Self { raw },
                    (_, true) => self.div_by_zero(),
                }
            }

            /// `self · 2^n` modulo `2^BITS` of the raw value; `n ≥ BITS` gives `0`.
            /// Unlike `wrapping_shl` of the primitive integers, `n` is not masked.
            #[inline]
            pub const fn wrapping_shl(self, n: u32) -> Self {
                Self { raw: crate::kernel::$k::shl(self.raw, n).0 }
            }

            /// `self / 2^n`, rounded to nearest (ties toward `+∞`); the operator
            /// `>>` does the same, so `x >> 1 == x / 2`. Never overflows; any `n`
            /// is accepted, `n ≥ BITS` gives `0`.
            #[inline]
            pub const fn shr_round(self, n: u32) -> Self {
                Self { raw: crate::kernel::$k::shr(self.raw, n) }
            }

            /// Division by an integer, rounded to nearest (ties toward `+∞`),
            /// saturating. `n = 0` gives `MAX`, `MIN` or `0` by the sign of `self`.
            #[inline]
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
            pub const fn sqr(self) -> Self {
                self.saturating_mul(self)
            }

            /// `-1`, `0` or `1` by the sign of `self`.
            #[inline]
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
            pub const fn min(self, other: Self) -> Self {
                if other.raw < self.raw {
                    other
                } else {
                    self
                }
            }

            /// The larger of two values.
            #[inline]
            pub const fn max(self, other: Self) -> Self {
                if other.raw > self.raw {
                    other
                } else {
                    self
                }
            }

            /// Restricts `self` to `[lo, hi]`. Never panics: when `lo > hi` the result is `hi`.
            #[inline]
            pub const fn clamp(self, lo: Self, hi: Self) -> Self {
                self.max(lo).min(hi)
            }

            /// `|self - other|`, saturating.
            #[inline]
            pub const fn abs_diff(self, other: Self) -> Self {
                if self.raw >= other.raw {
                    self.saturating_sub(other)
                } else {
                    other.saturating_sub(self)
                }
            }

            /// `(self + other) / 2` without overflow, rounded to nearest (ties toward `+∞`).
            #[inline]
            pub const fn midpoint(self, other: Self) -> Self {
                Self { raw: crate::kernel::$k::midpoint(self.raw, other.raw) }
            }
        }

        impl crate::sealed::Sealed for $Name {}

        impl crate::FixedFloat for $Name {
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
            fn __raw_i128(self) -> i128 {
                self.raw as i128
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
        }

        impl_ops!($Name);
        impl_round!($Name, $Bits, $F, $k);
        impl_convert!($Name, $Bits, $F, [$($FromInt),*], [$($TryFromInt),*]);
        impl_fmt!($Name, $UBits, $NB);
        impl_parse!($Name, $F);
        impl_bytes!($Name, $Bits, $NB);
        #[cfg(feature = "float-convert")]
        impl_float!($Name, $F);
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
        from_ints: [i8, u8, i16, u16, i32],
        try_from_ints: [i64, i128, u32, u64, u128],
    }
}

impl_accumulator!(Accumulator8, FixedFloat8, 4, scale: 8, product: [accumulator_product!(FixedFloat8);]);
impl_accumulator!(Accumulator16, FixedFloat16, 8, scale: 16, product: [accumulator_product!(FixedFloat16);]);
impl_accumulator!(Accumulator32, FixedFloat32, 16, scale: 32, product: [accumulator_product!(FixedFloat32);]);
impl_accumulator!(Accumulator64, FixedFloat64, 32, scale: 32, product: []);

impl_widen!(FixedFloat8 => FixedFloat16, FixedFloat32, FixedFloat64);
impl_widen!(FixedFloat16 => FixedFloat32, FixedFloat64);
impl_widen!(FixedFloat32 => FixedFloat64);
impl_narrow!(FixedFloat16 => FixedFloat8);
impl_narrow!(FixedFloat32 => FixedFloat8, FixedFloat16);
impl_narrow!(FixedFloat64 => FixedFloat8, FixedFloat16, FixedFloat32);
