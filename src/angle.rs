//! `define_angle!` generates one angle type: an angle kept as every bit of an
//! unsigned integer of `n` bits, the fraction `raw / 2^n` of a turn. Addition
//! wraps modulo a turn, so the range reduction is free and nothing saturates.
//! The functions themselves are in `src/trig.rs`, shared by every width
//! (docs/INTERNALS.md §3.14).

macro_rules! define_angle {
    (
        $(#[$meta:meta])*
        $Name:ident {
            bits: $Bits:ty,
            fixed: $Fixed:ident,
            n: $N:literal,
            frac_bits: $F:literal,
        }
    ) => {
        $(#[$meta])*
        #[derive(Clone, Copy, PartialEq, Eq, Hash, Default, Debug)]
        #[repr(transparent)]
        pub struct $Name {
            raw: $Bits,
        }

        impl $Name {
            /// Number of bits per turn: one step is `2^-BITS` of a turn.
            pub const BITS: u32 = $N;
            /// No rotation.
            pub const ZERO: Self = Self { raw: 0 };
            /// The smallest rotation, `2^-BITS` of a turn.
            pub const DELTA: Self = Self { raw: 1 };
            /// A quarter turn, 90°.
            pub const QUARTER_TURN: Self = Self { raw: 1 << ($N - 2) };
            /// Half a turn, 180°.
            pub const HALF_TURN: Self = Self { raw: 1 << ($N - 1) };

            /// The angle of `raw / 2^BITS` of a turn.
            #[inline]
            pub const fn from_bits(raw: $Bits) -> Self {
                Self { raw }
            }

            /// The raw value: the angle is `raw / 2^BITS` of a turn.
            #[inline]
            pub const fn to_bits(self) -> $Bits {
                self.raw
            }

            /// The angle of `turns` turns (1 turn = 360°), exactly: only its
            /// fraction matters, and it fits the angle bit for bit.
            #[inline]
            pub const fn from_turns(turns: $Fixed) -> Self {
                Self { raw: (turns.to_bits() as $Bits) << ($N - $F) }
            }

            /// The angle in turns, in `[0, 1)`, rounded to nearest.
            #[inline]
            pub const fn to_turns(self) -> $Fixed {
                let r = crate::kernel::shr_round(self.raw as i128, $N - $F);
                $Fixed::from_bits((r as u64 & ((1 << $F) - 1)) as <$Fixed as crate::FixedFloat>::Bits)
            }

            /// The angle of `radians` radians, `radians / 2π` modulo a turn,
            /// rounded to nearest: the range reduction multiplies by 192 bits
            /// of `2/π` exactly, so it is accurate on every input, and
            /// `from_radians(-x) = -from_radians(x)` bit for bit.
            #[inline]
            pub const fn from_radians(radians: $Fixed) -> Self {
                Self { raw: crate::trig::angle_from_radians(radians.to_bits() as i64, $F, $N) as $Bits }
            }

            /// The angle in radians, rounded to nearest: the exact value is in
            /// `[-π, π)`, the rounded one in `[-PI, PI]` (just below
            /// `HALF_TURN` it rounds up to `PI`); `HALF_TURN` gives `-PI`, and
            /// `(-a).to_radians() = -a.to_radians()` bit for bit for every
            /// `a ≠ HALF_TURN`.
            #[inline]
            pub const fn to_radians(self) -> $Fixed {
                $Fixed::from_bits(crate::trig::angle_to_radians(self.raw as u64, $N, $F) as <$Fixed as crate::FixedFloat>::Bits)
            }

            /// The sine of the angle, within 1 ulp; `(-a).sin() = -a.sin()` bit
            /// for bit.
            #[inline]
            pub const fn sin(self) -> $Fixed {
                $Fixed::from_bits(crate::trig::angle_sin(self.raw as u64, $N, $F) as <$Fixed as crate::FixedFloat>::Bits)
            }

            /// The cosine of the angle, within 1 ulp;
            /// `a.cos() = (a + QUARTER_TURN).sin()` and `(-a).cos() = a.cos()`
            /// bit for bit.
            #[inline]
            pub const fn cos(self) -> $Fixed {
                $Fixed::from_bits(crate::trig::angle_cos(self.raw as u64, $N, $F) as <$Fixed as crate::FixedFloat>::Bits)
            }

            /// `(self.sin(), self.cos())`.
            #[inline]
            pub const fn sin_cos(self) -> ($Fixed, $Fixed) {
                (self.sin(), self.cos())
            }

            /// `self + other` modulo a turn.
            #[inline]
            #[must_use]
            pub const fn wrapping_add(self, other: Self) -> Self {
                Self { raw: self.raw.wrapping_add(other.raw) }
            }

            /// `self - other` modulo a turn.
            #[inline]
            #[must_use]
            pub const fn wrapping_sub(self, other: Self) -> Self {
                Self { raw: self.raw.wrapping_sub(other.raw) }
            }

            /// `-self` modulo a turn: the same rotation the other way.
            #[inline]
            #[must_use]
            pub const fn wrapping_neg(self) -> Self {
                Self { raw: self.raw.wrapping_neg() }
            }

            /// `self · x` modulo a turn, rounded to nearest (ties toward `+∞`,
            /// as everywhere in the crate), with the angle taken in `[-½, ½)`
            /// of a turn: a rotation rate times a time step.
            #[inline]
            #[must_use]
            pub const fn scale(self, x: $Fixed) -> Self {
                Self { raw: crate::trig::angle_scale(self.raw as u64, $N, x.to_bits() as i64, $F) as $Bits }
            }
        }

        impl core::ops::Add for $Name {
            type Output = Self;
            /// Wrapping, see [`Self::wrapping_add`].
            #[inline]
            fn add(self, other: Self) -> Self {
                self.wrapping_add(other)
            }
        }

        impl core::ops::Sub for $Name {
            type Output = Self;
            /// Wrapping, see [`Self::wrapping_sub`].
            #[inline]
            fn sub(self, other: Self) -> Self {
                self.wrapping_sub(other)
            }
        }

        impl core::ops::Neg for $Name {
            type Output = Self;
            /// Wrapping, see [`Self::wrapping_neg`].
            #[inline]
            fn neg(self) -> Self {
                self.wrapping_neg()
            }
        }

        impl core::ops::AddAssign for $Name {
            #[inline]
            fn add_assign(&mut self, other: Self) {
                *self = self.wrapping_add(other);
            }
        }

        impl core::ops::SubAssign for $Name {
            #[inline]
            fn sub_assign(&mut self, other: Self) {
                *self = self.wrapping_sub(other);
            }
        }

        impl core::ops::Mul<crate::$Fixed> for $Name {
            type Output = Self;
            /// See [`Self::scale`].
            #[inline]
            fn mul(self, x: crate::$Fixed) -> Self {
                self.scale(x)
            }
        }

        impl core::ops::MulAssign<crate::$Fixed> for $Name {
            #[inline]
            fn mul_assign(&mut self, x: crate::$Fixed) {
                *self = self.scale(x);
            }
        }

        impl crate::sealed::Sealed for $Name {}

        impl crate::FixedAngle for $Name {
            type Fixed = crate::$Fixed;
            type Bits = $Bits;
            const BITS: u32 = $N;
            const ZERO: Self = Self::ZERO;
            const DELTA: Self = Self::DELTA;
            const QUARTER_TURN: Self = Self::QUARTER_TURN;
            const HALF_TURN: Self = Self::HALF_TURN;
            #[inline]
            fn from_bits(raw: $Bits) -> Self {
                Self::from_bits(raw)
            }
            #[inline]
            fn to_bits(self) -> $Bits {
                Self::to_bits(self)
            }
            #[inline]
            fn sin(self) -> crate::$Fixed {
                Self::sin(self)
            }
            #[inline]
            fn cos(self) -> crate::$Fixed {
                Self::cos(self)
            }
            #[inline]
            fn from_turns(turns: crate::$Fixed) -> Self {
                Self::from_turns(turns)
            }
            #[inline]
            fn to_turns(self) -> crate::$Fixed {
                Self::to_turns(self)
            }
            #[inline]
            fn from_radians(radians: crate::$Fixed) -> Self {
                Self::from_radians(radians)
            }
            #[inline]
            fn to_radians(self) -> crate::$Fixed {
                Self::to_radians(self)
            }
            #[inline]
            fn sin_cos(self) -> (crate::$Fixed, crate::$Fixed) {
                Self::sin_cos(self)
            }
            #[inline]
            fn scale(self, x: crate::$Fixed) -> Self {
                Self::scale(self, x)
            }
        }
    };
}

use crate::{FixedFloat16, FixedFloat32, FixedFloat64, FixedFloat8};

define_angle! {
    /// An angle as 8 bits of a turn: 256 steps of 1.40625°, the companion of
    /// [`FixedFloat8`].
    Angle8 {
        bits: u8,
        fixed: FixedFloat8,
        n: 8,
        frac_bits: 4,
    }
}

define_angle! {
    /// An angle as 16 bits of a turn: 65 536 steps of about 0.0055°, the
    /// companion of [`FixedFloat16`].
    Angle16 {
        bits: u16,
        fixed: FixedFloat16,
        n: 16,
        frac_bits: 8,
    }
}

define_angle! {
    /// An angle as 32 bits of a turn: steps of about `1.46·10⁻⁹` radians, the
    /// companion of [`FixedFloat32`].
    Angle32 {
        bits: u32,
        fixed: FixedFloat32,
        n: 32,
        frac_bits: 16,
    }
}

define_angle! {
    /// An angle as 64 bits of a turn: steps of about `3.4·10⁻¹⁹` radians, the
    /// companion of [`FixedFloat64`].
    Angle64 {
        bits: u64,
        fixed: FixedFloat64,
        n: 64,
        frac_bits: 32,
    }
}
