//! Wide integers built from little-endian `u64` limbs.
//!
//! Method names mirror the primitive integers (`wrapping_add`, `overflowing_mul`,
//! `leading_zeros`, …) so one macro can generate code for both `i64` and `I256`.

mod i256;
mod u256;
mod u512;
