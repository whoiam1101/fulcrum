//! `floor`, `ceil`, `trunc`, `fract`, `round`, `round_ties_even`, `to_int_*`.

macro_rules! impl_round {
    ($Name:ident, $Bits:ty, $F:literal, $k:ident) => {
        impl $Name {
            /// Largest integer `≤ self`. Never overflows.
            #[inline]
            pub const fn floor(self) -> Self {
                Self {
                    raw: self.raw & !Self::FRAC_MASK,
                }
            }

            /// Smallest integer `≥ self`, saturating to `MAX` when it is out of range.
            #[inline]
            pub const fn ceil(self) -> Self {
                Self::saturate(crate::kernel::$k::ceil(self.raw))
            }

            /// Smallest integer `≥ self`, or `None` when it is out of range.
            #[inline]
            pub const fn checked_ceil(self) -> Option<Self> {
                Self::checked(crate::kernel::$k::ceil(self.raw))
            }

            /// Integer part rounded toward zero. Never overflows.
            #[inline]
            pub const fn trunc(self) -> Self {
                if self.raw < 0 {
                    Self {
                        raw: (self.raw + Self::FRAC_MASK) & !Self::FRAC_MASK,
                    }
                } else {
                    self.floor()
                }
            }

            /// `self - self.trunc()`: fractional part with the sign of `self`.
            #[inline]
            pub const fn fract(self) -> Self {
                Self {
                    raw: self.raw - self.trunc().raw,
                }
            }

            /// Nearest integer, ties away from zero, saturating to `MAX` when out of range.
            #[inline]
            pub const fn round(self) -> Self {
                Self::saturate(crate::kernel::$k::round_half_away(self.raw))
            }

            /// Nearest integer, ties away from zero, or `None` when out of range.
            #[inline]
            pub const fn checked_round(self) -> Option<Self> {
                Self::checked(crate::kernel::$k::round_half_away(self.raw))
            }

            /// Nearest integer, ties to even, saturating to `MAX` when out of range.
            #[inline]
            pub const fn round_ties_even(self) -> Self {
                Self::saturate(crate::kernel::$k::round_ties_even(self.raw))
            }

            /// Nearest integer, ties to even, or `None` when out of range.
            #[inline]
            pub const fn checked_round_ties_even(self) -> Option<Self> {
                Self::checked(crate::kernel::$k::round_ties_even(self.raw))
            }

            /// `floor(self)` as an integer. Never overflows.
            #[inline]
            pub const fn to_int_floor(self) -> $Bits {
                self.raw >> $F
            }

            /// `ceil(self)` as an integer. Never overflows.
            #[inline]
            pub const fn to_int_ceil(self) -> $Bits {
                (self.raw >> $F) + ((self.raw & Self::FRAC_MASK != 0) as $Bits)
            }

            /// `trunc(self)` as an integer. Never overflows.
            #[inline]
            pub const fn to_int_trunc(self) -> $Bits {
                if self.raw < 0 {
                    self.to_int_ceil()
                } else {
                    self.to_int_floor()
                }
            }

            /// `round(self)` (ties away from zero) as an integer. Never overflows.
            #[inline]
            pub const fn to_int_round(self) -> $Bits {
                crate::kernel::$k::to_int(crate::kernel::$k::round_half_away(self.raw))
            }

            /// `round_ties_even(self)` as an integer. Never overflows.
            #[inline]
            pub const fn to_int_round_ties_even(self) -> $Bits {
                crate::kernel::$k::to_int(crate::kernel::$k::round_ties_even(self.raw))
            }
        }
    };
}
