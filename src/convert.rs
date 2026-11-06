//! Conversions from integers and between fixed-point widths.
//!
//! Widening (`From`) is always lossless: both the integer and the fractional
//! part grow. Narrowing (`TryFrom`) rounds the dropped fractional bits to
//! nearest (ties toward `+∞`) and fails when the integer part does not fit.

macro_rules! impl_convert {
    ($Name:ident, $Bits:ty, $F:literal, [$($FromInt:ty),*]) => {
        impl $Name {
            /// Converts `raw / 2^src_frac` to this type, rounding dropped bits to
            /// nearest (ties toward `+∞`); `None` when the result is out of range.
            #[inline]
            pub const fn checked_from_scaled_bits(raw: i128, src_frac: u32) -> Option<Self> {
                let w = if src_frac >= $F {
                    let s = src_frac - $F;
                    if s == 0 {
                        raw
                    } else if s >= 128 {
                        0
                    } else {
                        (raw >> s) + ((raw >> (s - 1)) & 1)
                    }
                } else {
                    let s = $F - src_frac;
                    if raw > (i128::MAX >> s) || raw < (i128::MIN >> s) {
                        return None;
                    }
                    raw << s
                };
                if w >= <$Bits>::MIN as i128 && w <= <$Bits>::MAX as i128 {
                    Some(Self { raw: w as $Bits })
                } else {
                    None
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
