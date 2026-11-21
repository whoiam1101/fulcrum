//! `f64` conversions behind the `float-convert` feature: for debugging, tests
//! and rendering only. Both directions work on the IEEE 754 bit pattern with
//! integer operations, so they are exact and deterministic. No floating point
//! arithmetic is performed; the only float operations are the exact
//! `i128 → f64` cast of an integer and `f64::from_bits`/`to_bits`.

#![allow(clippy::disallowed_types)]

pub(crate) enum FromF64 {
    Nan,
    Value(bool, u128, bool),
}

pub(crate) fn decompose(x: f64, frac_bits: u32) -> FromF64 {
    let bits = x.to_bits();
    let negative = bits >> 63 == 1;
    let exp = ((bits >> 52) & 0x7ff) as i32;
    let man = bits & ((1u64 << 52) - 1);
    if exp == 0x7ff {
        return if man != 0 {
            FromF64::Nan
        } else {
            FromF64::Value(negative, 0, true)
        };
    }
    let (m, e) = if exp == 0 {
        (u128::from(man), -1074)
    } else {
        (u128::from(man | (1u64 << 52)), exp - 1075)
    };
    if m == 0 {
        return FromF64::Value(negative, 0, false);
    }
    let s = e + frac_bits as i32;
    if s >= 0 {
        if s >= 75 {
            return FromF64::Value(negative, 0, true);
        }
        return FromF64::Value(negative, m << s, false);
    }
    let r = (-s) as u32;
    if r > 64 {
        return FromF64::Value(negative, 0, false);
    }
    let q = m >> r;
    let rem = m & ((1u128 << r) - 1);
    let half = 1u128 << (r - 1);
    let up = crate::kernel::magnitude_rounds_up(negative, rem >= half, rem & (half - 1) != 0);
    FromF64::Value(negative, q + u128::from(up), false)
}

#[allow(clippy::cast_precision_loss)]
pub(crate) fn compose(raw: i128, frac_bits: u32) -> f64 {
    if raw == 0 {
        return 0.0;
    }
    let v = raw as f64;
    f64::from_bits(v.to_bits() - (u64::from(frac_bits) << 52))
}

macro_rules! impl_float {
    ($Name:ident, $F:literal) => {
        #[allow(clippy::disallowed_types)]
        impl $Name {
            /// Converts from `f64`, rounding to nearest (ties toward `+∞`).
            /// `None` for NaN and for values out of range.
            #[inline]
            pub fn checked_from_f64(x: f64) -> Option<Self> {
                match crate::float::decompose(x, $F) {
                    crate::float::FromF64::Nan => None,
                    crate::float::FromF64::Value(_, _, true) => None,
                    crate::float::FromF64::Value(negative, magnitude, false) => {
                        Self::checked_from_sign_magnitude(negative, magnitude)
                    }
                }
            }

            /// Converts from `f64`, rounding to nearest (ties toward `+∞`).
            /// Saturates out of range values; NaN gives `0`.
            #[inline]
            pub fn saturating_from_f64(x: f64) -> Self {
                match crate::float::decompose(x, $F) {
                    crate::float::FromF64::Nan => Self::ZERO,
                    crate::float::FromF64::Value(negative, magnitude, false) => {
                        match Self::checked_from_sign_magnitude(negative, magnitude) {
                            Some(v) => v,
                            None if negative => Self::MIN,
                            None => Self::MAX,
                        }
                    }
                    crate::float::FromF64::Value(true, _, true) => Self::MIN,
                    crate::float::FromF64::Value(false, _, true) => Self::MAX,
                }
            }

            /// Converts to the nearest `f64` (ties to even). Exact when the raw
            /// value has at most 53 significant bits.
            #[inline]
            pub fn to_f64(self) -> f64 {
                crate::float::compose(i128::from(self.raw), $F)
            }
        }
    };
}

/// The floating-point method of the `serde` visitor of `src/serialize.rs`,
/// here because floating point lives only in this file.
#[cfg(feature = "serde")]
macro_rules! serde_visit_float {
    ($Name:ident) => {
        #[allow(clippy::disallowed_types)]
        fn visit_f64<E: serde::de::Error>(self, v: f64) -> Result<$Name, E> {
            $Name::checked_from_f64(v).ok_or_else(|| E::custom(crate::OverflowError))
        }
    };
}
