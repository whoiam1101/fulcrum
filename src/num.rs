//! `num-traits` support, behind the `num-traits` feature: `Zero`, `One`,
//! `Bounded`, `Num` and `Signed`, with the semantics of the operators
//! (saturating, rounded to nearest).
//!
//! `Num::from_str_radix` accepts only radix 10, the radix of `FromStr`; any
//! other radix is an error of kind [`ParseErrorKind::InvalidDigit`](crate::ParseErrorKind::InvalidDigit).
//! `Signed::abs_sub` is `max(self - other, 0)`, saturating.

macro_rules! impl_num_traits {
    ($Name:ident) => {
        impl num_traits::Zero for $Name {
            #[inline]
            fn zero() -> Self {
                Self::ZERO
            }
            #[inline]
            fn is_zero(&self) -> bool {
                self.raw == 0
            }
        }

        impl num_traits::One for $Name {
            #[inline]
            fn one() -> Self {
                Self::ONE
            }
        }

        impl num_traits::Bounded for $Name {
            #[inline]
            fn min_value() -> Self {
                Self::MIN
            }
            #[inline]
            fn max_value() -> Self {
                Self::MAX
            }
        }

        impl num_traits::Num for $Name {
            type FromStrRadixErr = crate::ParseError;

            #[inline]
            fn from_str_radix(text: &str, radix: u32) -> Result<Self, crate::ParseError> {
                if radix == 10 {
                    text.parse()
                } else {
                    Err(crate::ParseError::new(crate::ParseErrorKind::InvalidDigit))
                }
            }
        }

        impl num_traits::Signed for $Name {
            #[inline]
            fn abs(&self) -> Self {
                Self::abs(*self)
            }
            #[inline]
            fn abs_sub(&self, other: &Self) -> Self {
                self.saturating_sub(*other).max(Self::ZERO)
            }
            #[inline]
            fn signum(&self) -> Self {
                Self::signum(*self)
            }
            #[inline]
            fn is_positive(&self) -> bool {
                self.raw > 0
            }
            #[inline]
            fn is_negative(&self) -> bool {
                self.raw < 0
            }
        }
    };
}
