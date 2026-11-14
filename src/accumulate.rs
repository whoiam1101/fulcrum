//! Exact accumulators: order-independent sums and dot products.
//!
//! Values and exact unrounded products are added into the state without
//! saturation or rounding: an `i128` for widths up to 32 bits, an internal
//! 256-bit integer for `Accumulator64`, whose products at scale `2^-64`
//! overflow an `i128` after a few terms. Integer addition is
//! associative and commutative, so any order of `add` calls and any tree of
//! `merge` calls gives a bit-identical state. Saturation and rounding happen
//! once, in `finish`. This makes parallel reductions independent of the number
//! of threads and of how work is split between them.
//!
//! The state uses wrapping addition, which is also associative; it can only
//! lose information after more than 2^63 terms.

/// Generates the state module `$m` of an accumulator over the integer type
/// `$State`. The state is the exact sum at scale `2^-2F` for a type with `F`
/// fractional bits: a value `raw / 2^F` enters as `raw · 2^F`, a product of
/// two raw values as it is, so both are exact. Only `round` leaves the state.
macro_rules! accumulator_state {
    ($m:ident, $State:ty, $doc:literal, from: $from:path, round: $round:path) => {
        #[doc = $doc]
        pub(crate) mod $m {
            pub(crate) type State = $State;

            pub(crate) const ZERO: State = $from(0);

            /// `sum + raw · 2^f`; `|raw| < 2^64`, `f ≤ 32`.
            #[inline]
            pub(crate) const fn add_value(sum: State, raw: i128, f: u32) -> State {
                sum.wrapping_add($from(raw << f))
            }

            /// `sum - raw · 2^f`; `|raw| < 2^64`, `f ≤ 32`.
            #[inline]
            pub(crate) const fn sub_value(sum: State, raw: i128, f: u32) -> State {
                sum.wrapping_sub($from(raw << f))
            }

            /// `sum + a · b`; `|a|, |b| ≤ 2^63`.
            #[inline]
            pub(crate) const fn add_product(sum: State, a: i128, b: i128) -> State {
                sum.wrapping_add($from(a * b))
            }

            /// `a + b`, associative and commutative.
            #[inline]
            pub(crate) const fn merge(a: State, b: State) -> State {
                a.wrapping_add(b)
            }

            /// `round(sum / 2^f)` for `0 < f < 128`, to nearest with ties toward
            /// `+∞`, clamped to `i128`: the raw total at scale `2^-f`.
            #[inline]
            pub(crate) const fn round(sum: State, f: u32) -> i128 {
                $round(sum, f)
            }
        }
    };
}

/// The `i128` state holds a value as it is.
const fn i128_from(v: i128) -> i128 {
    v
}

/// `round(sum / 2^f)` on the `I256` state. The exact `⌊sum / 2^(f-1)⌋` is
/// clamped first and then rounded by `kernel::shr_round(·, 1)`, which adds the
/// first dropped bit. A clamped value is out of range of every type, and stays
/// so after the shift.
const fn i256_round(sum: crate::wide::I256, f: u32) -> i128 {
    crate::kernel::shr_round(sum.shr(f - 1).saturating_to_i128(), 1)
}

accumulator_state!(
    state128, i128,
    "State of an accumulator for widths up to 32 bits: an `i128`.",
    from: crate::accumulate::i128_from, round: crate::kernel::shr_round
);

accumulator_state!(
    state256, crate::wide::I256,
    "State of `Accumulator64`, whose products at scale `2^-64` overflow an `i128` after a few terms: an `I256`.",
    from: crate::wide::I256::from_i128, round: crate::accumulate::i256_round
);

macro_rules! impl_accumulator {
    ($Acc:ident, $Name:ident, $F:literal, state: $st:ident) => {
        #[doc = concat!(
            "Exact, order-independent accumulator for [`", stringify!($Name), "`].\n\n",
            "`add` and `merge` are exact and associative, so the result of `finish` does not ",
            "depend on the order of terms or on how they were split between threads. ",
            "Saturation (and rounding, for products) happens once, in `finish`."
        )]
        #[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
        pub struct $Acc {
            sum: crate::accumulate::$st::State,
        }

        impl $Acc {
            /// An empty accumulator (sum `0`).
            pub const ZERO: Self = Self { sum: crate::accumulate::$st::ZERO };

            /// An empty accumulator (sum `0`).
            #[inline]
            pub const fn new() -> Self {
                Self::ZERO
            }

            /// Adds `x` exactly.
            #[inline]
            pub fn add(&mut self, x: $Name) {
                self.sum = crate::accumulate::$st::add_value(self.sum, x.to_bits() as i128, $F);
            }

            /// Subtracts `x` exactly.
            #[inline]
            pub fn sub(&mut self, x: $Name) {
                self.sum = crate::accumulate::$st::sub_value(self.sum, x.to_bits() as i128, $F);
            }

            /// Adds the exact, unrounded product `a · b`. A dot product built with
            /// this method is rounded only once, in `finish`.
            #[inline]
            pub fn add_product(&mut self, a: $Name, b: $Name) {
                self.sum = crate::accumulate::$st::add_product(
                    self.sum,
                    a.to_bits() as i128,
                    b.to_bits() as i128,
                );
            }

            /// Combines two partial accumulators. Associative and commutative.
            #[inline]
            pub const fn merge(self, other: Self) -> Self {
                Self { sum: crate::accumulate::$st::merge(self.sum, other.sum) }
            }

            /// The total, rounded once to nearest (ties toward `+∞`) and saturated.
            #[inline]
            pub const fn finish(self) -> $Name {
                $Name::saturating_from_scaled_bits(crate::accumulate::$st::round(self.sum, $F), $F)
            }

            /// The total, rounded once, or `None` when it is out of range.
            #[inline]
            pub const fn checked_finish(self) -> Option<$Name> {
                $Name::checked_from_scaled_bits(crate::accumulate::$st::round(self.sum, $F), $F)
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
