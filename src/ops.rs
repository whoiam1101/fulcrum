//! `core::ops` impls. Operators saturate; `checked_*`, `wrapping_*`,
//! `saturating_*` and `overflowing_*` give explicit semantics.
//!
//! With the `strict-overflow` feature (for development and CI of the engine
//! only) every operator, `Neg`, `<<`, `Sum` and `Product` panics instead of
//! saturating, and division or remainder by zero panics too. The explicit methods keep their
//! documented semantics in both modes.

macro_rules! impl_ops {
    ($Name:ident) => {
        impl $Name {
            #[cfg(feature = "strict-overflow")]
            #[cold]
            #[inline(never)]
            fn strict_overflow(op: &str, a: Self, b: Self) -> ! {
                panic!("fulcrum strict-overflow: {} {} {} overflows or divides by zero", a, op, b)
            }
        }

        impl_ops!(@bin $Name, Add, add, AddAssign, add_assign, saturating_add, checked_add, "+", strict_add);
        impl_ops!(@bin $Name, Sub, sub, SubAssign, sub_assign, saturating_sub, checked_sub, "-", strict_sub);
        impl_ops!(@bin $Name, Mul, mul, MulAssign, mul_assign, saturating_mul, checked_mul, "*", strict_mul);
        impl_ops!(@bin $Name, Div, div, DivAssign, div_assign, saturating_div, checked_div, "/", strict_div);
        impl_ops!(@bin $Name, Rem, rem, RemAssign, rem_assign, saturating_rem, checked_rem, "%", strict_rem);

        impl core::ops::Neg for $Name {
            type Output = Self;
            #[inline]
            fn neg(self) -> Self {
                #[cfg(feature = "strict-overflow")]
                if self == Self::MIN {
                    Self::strict_overflow("-", Self::ZERO, self);
                }
                self.saturating_neg()
            }
        }

        impl core::ops::Shl<u32> for $Name {
            type Output = Self;
            /// `self · 2^n`, saturating, see [`Self::saturating_shl`].
            #[inline]
            fn shl(self, n: u32) -> Self {
                #[cfg(feature = "strict-overflow")]
                {
                    match self.checked_shl(n) {
                        Some(v) => v,
                        None => panic!("fulcrum strict-overflow: {} << {} overflows", self, n),
                    }
                }
                #[cfg(not(feature = "strict-overflow"))]
                {
                    self.saturating_shl(n)
                }
            }
        }

        impl core::ops::Shr<u32> for $Name {
            type Output = Self;
            /// `self / 2^n`, rounded to nearest, see [`Self::shr_round`].
            #[inline]
            fn shr(self, n: u32) -> Self {
                self.shr_round(n)
            }
        }

        impl core::ops::ShlAssign<u32> for $Name {
            #[inline]
            fn shl_assign(&mut self, n: u32) {
                *self = *self << n;
            }
        }

        impl core::ops::ShrAssign<u32> for $Name {
            #[inline]
            fn shr_assign(&mut self, n: u32) {
                *self = *self >> n;
            }
        }

        impl core::iter::Sum for $Name {
            /// Exact and order-independent: the terms are accumulated without
            /// saturation and the total is saturated once.
            fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
                let mut acc = Self::accumulator();
                acc.extend(iter);
                Self::finish_sum(acc)
            }
        }

        impl<'a> core::iter::Sum<&'a $Name> for $Name {
            /// Exact and order-independent, see `Sum<Self>`.
            fn sum<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
                let mut acc = Self::accumulator();
                acc.extend(iter);
                Self::finish_sum(acc)
            }
        }

        impl core::iter::Product for $Name {
            /// The `*` operator in iteration order: saturating, or panicking
            /// with `strict-overflow`. Rounded multiplication is not
            /// associative, so the order matters.
            fn product<I: Iterator<Item = Self>>(iter: I) -> Self {
                iter.fold(Self::ONE, |a, b| a * b)
            }
        }

        impl<'a> core::iter::Product<&'a $Name> for $Name {
            /// The `*` operator in iteration order, see `Product<Self>`.
            fn product<I: Iterator<Item = &'a Self>>(iter: I) -> Self {
                iter.fold(Self::ONE, |a, b| a * *b)
            }
        }
    };

    (@bin $Name:ident, $Trait:ident, $method:ident, $AssignTrait:ident, $assign:ident, $op:ident, $checked:ident, $sym:literal, $helper:ident) => {
        impl $Name {
            #[inline]
            fn $helper(self, rhs: Self) -> Self {
                #[cfg(feature = "strict-overflow")]
                {
                    match self.$checked(rhs) {
                        Some(v) => v,
                        None => Self::strict_overflow($sym, self, rhs),
                    }
                }
                #[cfg(not(feature = "strict-overflow"))]
                {
                    self.$op(rhs)
                }
            }
        }

        impl core::ops::$Trait for $Name {
            type Output = Self;
            #[inline]
            fn $method(self, rhs: Self) -> Self {
                $Name::$helper(self, rhs)
            }
        }

        impl<'a> core::ops::$Trait<&'a $Name> for $Name {
            type Output = Self;
            #[inline]
            fn $method(self, rhs: &'a Self) -> Self {
                $Name::$helper(self, *rhs)
            }
        }

        impl<'a> core::ops::$Trait<$Name> for &'a $Name {
            type Output = $Name;
            #[inline]
            fn $method(self, rhs: $Name) -> $Name {
                $Name::$helper(*self, rhs)
            }
        }

        impl<'a, 'b> core::ops::$Trait<&'b $Name> for &'a $Name {
            type Output = $Name;
            #[inline]
            fn $method(self, rhs: &'b $Name) -> $Name {
                $Name::$helper(*self, *rhs)
            }
        }

        impl core::ops::$AssignTrait for $Name {
            #[inline]
            fn $assign(&mut self, rhs: Self) {
                *self = $Name::$helper(*self, rhs);
            }
        }

        impl<'a> core::ops::$AssignTrait<&'a $Name> for $Name {
            #[inline]
            fn $assign(&mut self, rhs: &'a Self) {
                *self = $Name::$helper(*self, *rhs);
            }
        }
    };
}
