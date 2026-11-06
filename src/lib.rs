//! # fulcrum
//!
//! Deterministic fixed-point math. Every operation gives bit-identical results
//! on every platform (x86-64, ARM64, 32-bit targets); no floating point is used
//! internally. Overflow is explicit and never panics.
//!
//! | Type | Format | Range | Step |
//! |---|---|---|---|
//! | [`FixedFloat8`] | Q4.4 | `[-8, 7.9375]` | `2^-4` |
//! | [`FixedFloat16`] | Q8.8 | `[-128, 127.996]` | `2^-8` |
//! | [`FixedFloat32`] | Q16.16 | `[-32768, 32767.99998]` | `2^-16` |
//! | [`FixedFloat64`] | Q32.32 | `±2.1·10⁹` | `2^-32` |
//!
//! Semantics shared by all types:
//!
//! - operators `+ - * / %` and unary `-` saturate; `checked_*`, `wrapping_*`,
//!   `saturating_*` and `overflowing_*` methods give explicit control;
//! - `*` and `/` round to nearest, ties toward `+∞`; `+`, `-` and `%` are exact;
//! - division by zero gives `MAX`, `MIN` or `0` by the sign of the dividend,
//!   `x % 0` gives `0`, and the `checked_*` variants return `None`;
//! - nothing panics;
//! - [`Iterator::sum`] and the `Accumulator*` types are exact and do not depend
//!   on the order of terms, so parallel reductions give the same bits for any
//!   number of threads. Rounded multiplication is not associative:
//!   [`Iterator::product`] and chains of `*` depend on the order, which the
//!   caller must fix.
//!
//! The `strict-overflow` feature turns every saturation of an operator into a
//! panic. It is meant for tests and CI of an engine, never for a shipped build.
//!
//! ```
//! use fulcrum::{ff64, FixedFloat64};
//!
//! const SPEED: FixedFloat64 = ff64!(12.6);
//! let dt = ff64!(0.05);
//! let step = SPEED * dt;
//! assert_eq!(step.to_string(), "0.63000000058673322200775146484375");
//! assert_eq!(format!("{:.4}", step), "0.6300");
//! assert_eq!(FixedFloat64::MAX.saturating_add(FixedFloat64::ONE), FixedFloat64::MAX);
//! assert_eq!(ff64!(-1.25).int_part(), -2);
//! ```

#![no_std]
#![forbid(unsafe_code)]
#![cfg_attr(docsrs, feature(doc_cfg))]

#[cfg(feature = "alloc")]
extern crate alloc;
#[cfg(any(feature = "std", test))]
extern crate std;

mod kernel;
mod wide;

#[macro_use]
mod bytes;
#[macro_use]
mod convert;
#[macro_use]
mod fmt;
#[macro_use]
mod ops;
#[macro_use]
mod parse;
#[macro_use]
mod round;
#[macro_use]
mod accumulate;
#[cfg(feature = "float-convert")]
#[macro_use]
mod float;
#[macro_use]
mod define;

mod error;
mod math;
mod tables;
mod vec;

#[cfg(kani)]
mod proofs;

pub use define::{
    Accumulator16, Accumulator32, Accumulator64, Accumulator8, FixedFloat16, FixedFloat32,
    FixedFloat64, FixedFloat8,
};
pub use error::{OverflowError, ParseError, ParseErrorKind};

mod sealed {
    pub trait Sealed {}
}

/// Interface shared by all fixed-point types, for generic code.
///
/// Sealed: implemented only by the types of this crate. Every method is also
/// available as an inherent `const fn` on each type.
pub trait FixedFloat:
    Copy
    + Default
    + Ord
    + core::hash::Hash
    + core::fmt::Debug
    + core::fmt::Display
    + core::str::FromStr<Err = ParseError>
    + core::ops::Add<Output = Self>
    + core::ops::Sub<Output = Self>
    + core::ops::Mul<Output = Self>
    + core::ops::Div<Output = Self>
    + core::ops::Rem<Output = Self>
    + core::ops::Neg<Output = Self>
    + core::ops::AddAssign
    + core::ops::SubAssign
    + core::ops::MulAssign
    + core::ops::DivAssign
    + core::ops::RemAssign
    + sealed::Sealed
{
    /// The raw storage integer.
    type Bits: Copy;
    /// Number of fractional bits.
    const FRAC_BITS: u32;
    /// Number of integer bits, including the sign bit.
    const INT_BITS: u32;
    /// `0`.
    const ZERO: Self;
    /// `1`.
    const ONE: Self;
    /// `-1`.
    const NEG_ONE: Self;
    /// `0.5`.
    const HALF: Self;
    /// The smallest value.
    const MIN: Self;
    /// The largest value.
    const MAX: Self;
    /// One ulp.
    const DELTA: Self;
    /// π, correctly rounded.
    const PI: Self;
    /// τ = 2π, correctly rounded.
    const TAU: Self;
    /// π/2, correctly rounded.
    const FRAC_PI_2: Self;
    /// e, correctly rounded.
    const E: Self;
    /// √2, correctly rounded.
    const SQRT_2: Self;

    /// Creates a value from its raw representation.
    fn from_bits(bits: Self::Bits) -> Self;
    /// The raw representation.
    fn to_bits(self) -> Self::Bits;
    /// Converts an integer, saturating.
    fn saturating_from_int(n: i128) -> Self;
    /// Converts an integer, or `None` when out of range.
    fn checked_from_int(n: i128) -> Option<Self>;
    /// Checked addition.
    fn checked_add(self, rhs: Self) -> Option<Self>;
    /// Checked subtraction.
    fn checked_sub(self, rhs: Self) -> Option<Self>;
    /// Checked multiplication.
    fn checked_mul(self, rhs: Self) -> Option<Self>;
    /// Checked division.
    fn checked_div(self, rhs: Self) -> Option<Self>;
    /// Wrapping addition.
    fn wrapping_add(self, rhs: Self) -> Self;
    /// Wrapping subtraction.
    fn wrapping_sub(self, rhs: Self) -> Self;
    /// Wrapping multiplication.
    fn wrapping_mul(self, rhs: Self) -> Self;
    /// Absolute value, saturating.
    fn abs(self) -> Self;
    /// `self < 0`.
    fn is_negative(self) -> bool;
    /// Largest integer `≤ self`.
    fn floor(self) -> Self;
    /// Smallest integer `≥ self`, saturating.
    fn ceil(self) -> Self;
    /// Nearest integer, ties away from zero, saturating.
    fn round(self) -> Self;
}

macro_rules! literal_macro {
    ($d:tt $name:ident, $Type:ident) => {
        #[doc = concat!(
            "Compile-time [`", stringify!($Type), "`] literal: `", stringify!($name), "!(12.6)`, `",
            stringify!($name), "!(-0.25)`, `", stringify!($name), "!(1_000)`.\n\n",
            "The literal is parsed exactly at compile time, without floating point; ",
            "an invalid or out of range literal is a compile error."
        )]
        #[macro_export]
        macro_rules! $name {
            (- $d lit:literal) => {{
                const VALUE: $d crate::$Type = $d crate::$Type::__lit(stringify!($d lit), true);
                VALUE
            }};
            ($d lit:literal) => {{
                const VALUE: $d crate::$Type = $d crate::$Type::__lit(stringify!($d lit), false);
                VALUE
            }};
        }
    };
}

literal_macro!($ ff8, FixedFloat8);
literal_macro!($ ff16, FixedFloat16);
literal_macro!($ ff32, FixedFloat32);
literal_macro!($ ff64, FixedFloat64);
