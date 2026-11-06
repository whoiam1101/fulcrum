//! `floor`, `ceil`, `trunc`, `fract`, `round`, `round_ties_even`, `to_int_*`.

macro_rules! impl_round {
    ($Name:ident, $Bits:ty, $Wide:ty, $F:literal) => {
        impl $Name {
            const W_MASK: $Wide = (1 << $F) - 1;
            const W_HALF: $Wide = 1 << ($F - 1);

            #[inline]
            const fn wide_round_half_away(self) -> $Wide {
                let w = self.raw as $Wide;
                if w >= 0 {
                    (w + Self::W_HALF) & !Self::W_MASK
                } else {
                    -((Self::W_HALF - w) & !Self::W_MASK)
                }
            }

            #[inline]
            const fn wide_round_ties_even(self) -> $Wide {
                let w = self.raw as $Wide;
                let floor = w & !Self::W_MASK;
                let frac = w & Self::W_MASK;
                let odd = (w >> $F) & 1 == 1;
                if frac > Self::W_HALF || (frac == Self::W_HALF && odd) {
                    floor + (1 << $F)
                } else {
                    floor
                }
            }

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
                Self::saturate(((self.raw as $Wide) + Self::W_MASK) & !Self::W_MASK)
            }

            /// Smallest integer `≥ self`, or `None` when it is out of range.
            #[inline]
            pub const fn checked_ceil(self) -> Option<Self> {
                Self::checked(((self.raw as $Wide) + Self::W_MASK) & !Self::W_MASK)
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
                Self::saturate(self.wide_round_half_away())
            }

            /// Nearest integer, ties away from zero, or `None` when out of range.
            #[inline]
            pub const fn checked_round(self) -> Option<Self> {
                Self::checked(self.wide_round_half_away())
            }

            /// Nearest integer, ties to even, saturating to `MAX` when out of range.
            #[inline]
            pub const fn round_ties_even(self) -> Self {
                Self::saturate(self.wide_round_ties_even())
            }

            /// Nearest integer, ties to even, or `None` when out of range.
            #[inline]
            pub const fn checked_round_ties_even(self) -> Option<Self> {
                Self::checked(self.wide_round_ties_even())
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
                (self.wide_round_half_away() >> $F) as $Bits
            }

            /// `round_ties_even(self)` as an integer. Never overflows.
            #[inline]
            pub const fn to_int_round_ties_even(self) -> $Bits {
                (self.wide_round_ties_even() >> $F) as $Bits
            }
        }
    };
}
