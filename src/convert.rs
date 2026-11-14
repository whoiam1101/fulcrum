//! Conversions from integers and between fixed-point widths.
//!
//! Widening (`From`) is always lossless: both the integer and the fractional
//! part grow. Narrowing (`TryFrom`) rounds the dropped fractional bits to
//! nearest (ties toward `+∞`) and fails when the integer part does not fit.

/// `±magnitude` as an `i128`, or `None` when it does not fit. Turns the sign
/// and magnitude produced by parsing and by float decomposition into the input
/// of `checked_from_scaled_bits`.
#[inline]
pub(crate) const fn signed(negative: bool, magnitude: u128) -> Option<i128> {
    if negative {
        if magnitude > 1 << 127 {
            None
        } else {
            Some((magnitude as i128).wrapping_neg())
        }
    } else if magnitude > i128::MAX as u128 {
        None
    } else {
        Some(magnitude as i128)
    }
}

macro_rules! impl_convert {
    ($Name:ident, $Bits:ty, $F:literal, [$($FromInt:ty),*], [$($TryFromInt:ty),*]) => {
        impl $Name {
            /// Converts `raw / 2^src_frac` to this type, rounding dropped bits to
            /// nearest (ties toward `+∞`) once; `None` when the result is out of
            /// range. Any `src_frac` is accepted: `src_frac = 0` converts an
            /// integer, `src_frac > FRAC_BITS` drops bits, `src_frac < FRAC_BITS`
            /// adds zero bits.
            ///
            #[doc = concat!(
                "```\n",
                "use fulcrum::", stringify!($Name), " as F;\n",
                "assert_eq!(F::checked_from_scaled_bits(3, 1), Some(F::ONE + F::HALF));\n",
                "assert_eq!(F::checked_from_scaled_bits(-1, 200), Some(F::ZERO));\n",
                "assert_eq!(F::checked_from_scaled_bits(i128::MAX, 0), None);\n",
                "```"
            )]
            ///
            /// Every checked or saturating conversion into this type from an
            /// `i128` with a scale goes through here: integers, narrowing,
            /// parsing, floats and accumulators. The wrapping one,
            /// `wrapping_from_scaled_bits`, shares the rescaling and keeps the
            /// low bits instead.
            #[inline]
            pub const fn checked_from_scaled_bits(raw: i128, src_frac: u32) -> Option<Self> {
                let (w, overflow) = crate::kernel::rescale(raw, src_frac, $F);
                if !overflow && w >= <$Bits>::MIN as i128 && w <= <$Bits>::MAX as i128 {
                    Some(Self { raw: w as $Bits })
                } else {
                    None
                }
            }

            /// Converts `raw / 2^src_frac` to this type, rounding dropped bits to
            /// nearest (ties toward `+∞`) once and saturating by the sign of `raw`.
            #[inline]
            pub const fn saturating_from_scaled_bits(raw: i128, src_frac: u32) -> Self {
                match Self::checked_from_scaled_bits(raw, src_frac) {
                    Some(v) => v,
                    None if raw < 0 => Self::MIN,
                    None => Self::MAX,
                }
            }

            /// Converts `raw / 2^src_frac`, rounding dropped bits to nearest
            /// (ties toward `+∞`) once and keeping the low `BITS` bits of the
            /// exact raw result.
            #[inline]
            pub const fn wrapping_from_scaled_bits(raw: i128, src_frac: u32) -> Self {
                Self { raw: crate::kernel::rescale(raw, src_frac, $F).0 as $Bits }
            }

            /// Converts any fixed-point value to this type, rounding dropped
            /// fractional bits to nearest (ties toward `+∞`) and saturating when
            /// the result is out of range. Widening is exact.
            #[inline]
            pub fn saturating_from<T: crate::FixedFloat>(x: T) -> Self {
                Self::saturating_from_scaled_bits(x.__raw_i128(), T::FRAC_BITS)
            }

            /// Converts any fixed-point value to this type, rounding dropped
            /// fractional bits to nearest (ties toward `+∞`) and wrapping the raw
            /// result modulo `2^BITS` when it is out of range. Widening is exact.
            #[inline]
            pub fn wrapping_from<T: crate::FixedFloat>(x: T) -> Self {
                Self::wrapping_from_scaled_bits(x.__raw_i128(), T::FRAC_BITS)
            }

            #[inline]
            const fn checked_from_sign_magnitude(negative: bool, magnitude: u128) -> Option<Self> {
                match crate::convert::signed(negative, magnitude) {
                    Some(raw) => Self::checked_from_scaled_bits(raw, $F),
                    None => None,
                }
            }
        }

        $(
            impl From<$FromInt> for $Name {
                #[inline]
                fn from(n: $FromInt) -> Self {
                    Self { raw: (n as $Bits) << $F }
                }
            }
        )*

        $(
            impl core::convert::TryFrom<$TryFromInt> for $Name {
                type Error = crate::OverflowError;
                /// Converts an integer exactly, or fails when it is out of range.
                #[inline]
                fn try_from(n: $TryFromInt) -> Result<Self, Self::Error> {
                    match i128::try_from(n) {
                        Ok(n) => match Self::checked_from_int(n) {
                            Some(v) => Ok(v),
                            None => Err(crate::OverflowError),
                        },
                        Err(_) => Err(crate::OverflowError),
                    }
                }
            }
        )*
    };
}

macro_rules! impl_widen {
    ($Small:ident => $($Big:ident),+) => {
        $(
            impl From<$Small> for $Big {
                #[inline]
                fn from(v: $Small) -> Self {
                    Self::from_bits((v.to_bits() as <$Big as crate::FixedFloat>::Bits) << ($Big::FRAC_BITS - $Small::FRAC_BITS))
                }
            }
        )+
    };
}

macro_rules! impl_narrow {
    ($Big:ident => $($Small:ident),+) => {
        $(
            impl core::convert::TryFrom<$Big> for $Small {
                type Error = crate::OverflowError;
                #[inline]
                fn try_from(v: $Big) -> Result<Self, Self::Error> {
                    match Self::checked_from_scaled_bits(v.to_bits() as i128, $Big::FRAC_BITS) {
                        Some(x) => Ok(x),
                        None => Err(crate::OverflowError),
                    }
                }
            }
        )+
    };
}
