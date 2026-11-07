//! Exact accumulators: order-independent sums and dot products.
//!
//! Values (and, for widths up to 32 bits, exact unrounded products) are added
//! into an `i128` without saturation or rounding. Integer addition is
//! associative and commutative, so any order of `add` calls and any tree of
//! `merge` calls gives a bit-identical state. Saturation and rounding happen
//! once, in `finish`. This makes parallel reductions independent of the number
//! of threads and of how work is split between them.
//!
//! The `i128` state uses wrapping addition, which is also associative; it can
//! only lose information after more than 2^63 terms.

macro_rules! impl_accumulator {
    (
        $Acc:ident, $Name:ident, $F:literal, scale: $S:literal,
        product: [$($product:tt)*]
    ) => {
        #[doc = concat!(
            "Exact, order-independent accumulator for [`", stringify!($Name), "`].\n\n",
            "`add` and `merge` are exact and associative, so the result of `finish` does not ",
            "depend on the order of terms or on how they were split between threads. ",
            "Saturation (and rounding, for products) happens once, in `finish`."
        )]
        #[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
        pub struct $Acc {
            sum: i128,
        }

        impl $Acc {
            /// An empty accumulator (sum `0`).
            pub const ZERO: Self = Self { sum: 0 };

            /// An empty accumulator (sum `0`).
            #[inline]
            pub const fn new() -> Self {
                Self::ZERO
            }

            /// Adds `x` exactly.
            #[inline]
            pub fn add(&mut self, x: $Name) {
                self.sum = self.sum.wrapping_add((x.to_bits() as i128) << ($S - $F));
            }

            /// Subtracts `x` exactly.
            #[inline]
            pub fn sub(&mut self, x: $Name) {
                self.sum = self.sum.wrapping_sub((x.to_bits() as i128) << ($S - $F));
            }

            $($product)*

            /// Combines two partial accumulators. Associative and commutative.
            #[inline]
            pub const fn merge(self, other: Self) -> Self {
                Self { sum: self.sum.wrapping_add(other.sum) }
            }

            /// The total, rounded once to nearest (ties toward `+∞`) and saturated.
            #[inline]
            pub const fn finish(self) -> $Name {
                $Name::saturating_from_scaled_bits(self.sum, $S)
            }

            /// The total, rounded once, or `None` when it is out of range.
            #[inline]
            pub const fn checked_finish(self) -> Option<$Name> {
                $Name::checked_from_scaled_bits(self.sum, $S)
            }
        }

        impl $Name {
            #[inline]
            fn finish_sum(acc: $Acc) -> Self {
                #[cfg(feature = "strict-overflow")]
                {
                    match acc.checked_finish() {
                        Some(v) => v,
                        None => panic!("fulcrum strict-overflow: sum is out of range"),
                    }
                }
                #[cfg(not(feature = "strict-overflow"))]
                {
                    acc.finish()
                }
            }

            #[doc = concat!("A new empty [`", stringify!($Acc), "`].")]
            #[inline]
            pub const fn accumulator() -> $Acc {
                $Acc::ZERO
            }
        }

        impl Extend<$Name> for $Acc {
            fn extend<I: IntoIterator<Item = $Name>>(&mut self, iter: I) {
                for x in iter {
                    self.add(x);
                }
            }
        }

        impl<'a> Extend<&'a $Name> for $Acc {
            fn extend<I: IntoIterator<Item = &'a $Name>>(&mut self, iter: I) {
                for x in iter {
                    self.add(*x);
                }
            }
        }

        impl core::iter::FromIterator<$Name> for $Acc {
            fn from_iter<I: IntoIterator<Item = $Name>>(iter: I) -> Self {
                let mut acc = Self::ZERO;
                acc.extend(iter);
                acc
            }
        }

        impl core::iter::Sum<$Acc> for $Acc {
            fn sum<I: Iterator<Item = $Acc>>(iter: I) -> Self {
                iter.fold(Self::ZERO, Self::merge)
            }
        }
    };
}

macro_rules! accumulator_product {
    ($Name:ident, $F:literal) => {
        /// Adds the exact, unrounded product `a · b`. A dot product built with
        /// this method is rounded only once, in `finish`.
        #[inline]
        pub fn add_product(&mut self, a: $Name, b: $Name) {
            self.sum = self
                .sum
                .wrapping_add(a.to_bits() as i128 * b.to_bits() as i128);
        }
    };
}
