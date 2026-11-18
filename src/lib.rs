//! # fulcrum
//!
//! Deterministic fixed-point math. Every operation gives bit-identical results
//! on every platform (x86-64, ARM64, 32-bit targets); no floating point is used
//! internally. Overflow is explicit: operators saturate and never panic.
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
//! - `sqrt`, `rsqrt` and `hypot` are correctly rounded; `hypot` squares
//!   exactly and never overflows before the root;
//! - `sin_turns` and `cos_turns` take the angle in turns (1.0 = 360°), reduce
//!   it exactly with a bit mask and are within 1 ulp;
//! - `log2`, `exp2`, `ln`, `exp`, `pow` and `powi` are within 1 ulp, `log2`
//!   exact on powers of two and `exp2` on integers `≥ -FRAC_BITS`;
//! - [`Vec2`] and [`Vec3`] over any of these types: operators per component,
//!   `dot`, `cross` and the squared lengths rounded once from exact products,
//!   `length` and every component of `normalize` correctly rounded;
//! - division by zero gives `MAX`, `MIN` or `0` by the sign of the dividend,
//!   `x % 0` gives `0`, and the `checked_*` variants return `None`;
//! - nothing panics, unless the `strict-overflow` feature below is enabled;
//! - [`Iterator::sum`] and the `Accumulator*` types are exact and do not depend
//!   on the order of terms, so parallel reductions give the same bits for any
//!   number of threads. Rounded multiplication is not associative:
//!   [`Iterator::product`] and chains of `*` depend on the order, which the
//!   caller must fix.
//!
//! The `strict-overflow` feature turns every saturation of an operator, `<<`,
//! [`Iterator::sum`] and [`Iterator::product`] into a panic; the explicit
//! methods and `Accumulator*::finish` keep their semantics. It is meant for tests and CI of an engine, never for a shipped build.
//!
//! Optional features, off by default: `serde` (a decimal string in
//! human-readable formats, the raw integer in binary ones), `bytemuck` (`Pod`
//! and `Zeroable`, the only `unsafe` of the crate) and `num-traits`.
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
#![deny(unsafe_code)]
#![deny(
    clippy::panic,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::print_stdout,
    clippy::print_stderr,
    clippy::exit,
    clippy::std_instead_of_core,
    clippy::std_instead_of_alloc,
    clippy::alloc_instead_of_core
)]
#![warn(clippy::missing_inline_in_public_items)]
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
#[cfg(feature = "serde")]
#[macro_use]
mod serialize;
#[cfg(feature = "bytemuck")]
#[macro_use]
mod pod;
#[cfg(feature = "num-traits")]
#[macro_use]
mod num;
#[macro_use]
mod define;

mod angle;
mod error;
mod exp;
mod tables;
mod trig;
mod vec;

#[cfg(kani)]
mod proofs;

#[cfg(kani)]
#[path = "proofs/geometry.rs"]
mod proofs_geometry;

/// The README example, compiled and run as a doctest.
#[cfg(doctest)]
#[doc = include_str!("../README.md")]
struct ReadmeDoctest;

pub use angle::{Angle16, Angle32, Angle64, Angle8};
pub use define::{
    Accumulator16, Accumulator32, Accumulator64, Accumulator8, FixedFloat16, FixedFloat32,
    FixedFloat64, FixedFloat8,
};
pub use error::{OverflowError, ParseError, ParseErrorKind};
pub use vec::{Vec2, Vec2f16, Vec2f32, Vec2f64, Vec2f8, Vec3, Vec3f16, Vec3f32, Vec3f64, Vec3f8};

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
    /// The angle type of the same width.
    type Angle: FixedAngle<Fixed = Self>;
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
    #[doc(hidden)]
    fn __raw_i128(self) -> i128;
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
    #[must_use]
    fn wrapping_add(self, rhs: Self) -> Self;
    /// Wrapping subtraction.
    #[must_use]
    fn wrapping_sub(self, rhs: Self) -> Self;
    /// Wrapping multiplication.
    #[must_use]
    fn wrapping_mul(self, rhs: Self) -> Self;
    /// Absolute value, saturating.
    #[must_use]
    fn abs(self) -> Self;
    /// `self < 0`.
    fn is_negative(self) -> bool;
    /// Largest integer `≤ self`.
    #[must_use]
    fn floor(self) -> Self;
    /// Smallest integer `≥ self`, saturating.
    #[must_use]
    fn ceil(self) -> Self;
    /// Nearest integer, ties away from zero, saturating.
    #[must_use]
    fn round(self) -> Self;
    /// `√self`, correctly rounded; a negative `self` gives `0`.
    #[must_use]
    fn sqrt(self) -> Self;
    /// Sine and cosine of an angle in radians, each within 1 ulp.
    fn sin_cos(self) -> (Self, Self);
    /// The angle of the point `(other, self)` in radians, within 1 ulp.
    #[must_use]
    fn atan2(self, other: Self) -> Self;
    /// `√(self² + other²)`, correctly rounded and saturated.
    #[must_use]
    fn hypot(self, other: Self) -> Self;
    /// `self + (other - self) · t`, rounded once and saturated.
    #[must_use]
    fn lerp(self, other: Self, t: Self) -> Self;
    #[doc(hidden)]
    fn __dot(a: &[Self], b: &[Self]) -> Self;
    #[doc(hidden)]
    fn __det(a: Self, b: Self, c: Self, d: Self) -> Self;
    #[doc(hidden)]
    fn __hypot3(a: Self, b: Self, c: Self) -> Self;
    #[doc(hidden)]
    fn __scale_to(v: [Self; 3], len: Self) -> [Self; 3];
    #[doc(hidden)]
    fn __cmp_length(v: [Self; 3], len: Self) -> core::cmp::Ordering;
    #[doc(hidden)]
    fn __rotate(x: Self, y: Self, angle: Self::Angle) -> (Self, Self);
    #[doc(hidden)]
    fn __angle2(a: [Self; 2], b: [Self; 2]) -> Self;
    #[doc(hidden)]
    fn __angle3(a: [Self; 3], b: [Self; 3]) -> Self;
}

/// Interface shared by the angle types [`Angle8`] … [`Angle64`], for generic
/// code: an angle as every bit of an unsigned integer, the fraction of a turn,
/// with wrapping arithmetic. Each angle type has the fixed-point type of its
/// width as [`FixedAngle::Fixed`], and that type names it back as
/// [`FixedFloat::Angle`].
///
/// Sealed: implemented only by the types of this crate. Every method is also
/// available as an inherent `const fn` on each type.
pub trait FixedAngle:
    Copy
    + Default
    + Eq
    + core::hash::Hash
    + core::fmt::Debug
    + core::ops::Add<Output = Self>
    + core::ops::Sub<Output = Self>
    + core::ops::Neg<Output = Self>
    + core::ops::AddAssign
    + core::ops::SubAssign
    + core::ops::Mul<<Self as FixedAngle>::Fixed, Output = Self>
    + core::ops::MulAssign<<Self as FixedAngle>::Fixed>
    + sealed::Sealed
{
    /// The fixed-point type of the same width.
    type Fixed: FixedFloat;
    /// The raw storage integer, unsigned.
    type Bits: Copy;
    /// Number of bits per turn.
    const BITS: u32;
    /// No rotation.
    const ZERO: Self;
    /// The smallest rotation, `2^-BITS` of a turn.
    const DELTA: Self;
    /// A quarter turn.
    const QUARTER_TURN: Self;
    /// Half a turn.
    const HALF_TURN: Self;
    /// The angle of `raw / 2^BITS` of a turn.
    fn from_bits(raw: Self::Bits) -> Self;
    /// The raw fraction of a turn.
    fn to_bits(self) -> Self::Bits;
    /// Sine, within 1 ulp.
    fn sin(self) -> Self::Fixed;
    /// Cosine, within 1 ulp.
    fn cos(self) -> Self::Fixed;
    /// The angle of `turns` turns, exactly.
    fn from_turns(turns: Self::Fixed) -> Self;
    /// The angle in turns, in `[0, 1)`, rounded to nearest.
    fn to_turns(self) -> Self::Fixed;
    /// The angle of `radians` radians modulo a turn, rounded to nearest.
    fn from_radians(radians: Self::Fixed) -> Self;
    /// The angle in radians, rounded to nearest, in `[-PI, PI]`.
    fn to_radians(self) -> Self::Fixed;
    /// Sine and cosine, each within 1 ulp.
    fn sin_cos(self) -> (Self::Fixed, Self::Fixed);
    /// `self · x` modulo a turn, rounded to nearest.
    #[must_use]
    fn scale(self, x: Self::Fixed) -> Self;
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
