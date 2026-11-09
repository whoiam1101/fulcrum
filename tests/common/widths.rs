//! The one list of widths for tests, oracle tests and fuzz targets. A new
//! width is one row here; every suite that runs on all widths picks it up.
//! Beyond 64 bits the generators and references must first hold the width:
//! `Pcg32::edge_bits` returns `i64`, and `Widest` in `tests/consts.rs` names
//! the widest type.
//!
//! Each row calls the given macro with the arguments it was passed first,
//! then the fields of the width:
//!
//! ```text
//! $m!(args..., module, Type, literal, Accumulator, Raw, bits, frac_bits)
//! ```
//!
//! `module` is a lowercase name for a per-width `mod` (`fixed8`), `literal`
//! is the literal macro (`ff8`), `Raw` is the raw integer type, `bits` and
//! `frac_bits` are integer literals, so they work in constant contexts.
//!
//! Crates outside the root package include this file with
//! `#[macro_use] #[path = "…/tests/common/widths.rs"] mod widths;`.

#![allow(unused_macros)]

/// Calls `$m!` once per width: every fixed-point type of the crate.
macro_rules! for_each_width {
    ($m:ident!($($arg:tt)*)) => {
        for_each_i128_width!($m!($($arg)*));
    };
}

/// Calls `$m!` once per width whose product of two raw values fits `i128`,
/// so the `i128` reference of `tests/common` computes it exactly. Wider types
/// are checked against the rational oracle instead.
macro_rules! for_each_i128_width {
    ($m:ident!($($arg:tt)*)) => {
        $m!($($arg)* fixed8, FixedFloat8, ff8, Accumulator8, i8, 8, 4);
        $m!($($arg)* fixed16, FixedFloat16, ff16, Accumulator16, i16, 16, 8);
        $m!($($arg)* fixed32, FixedFloat32, ff32, Accumulator32, i32, 32, 16);
        $m!($($arg)* fixed64, FixedFloat64, ff64, Accumulator64, i64, 64, 32);
    };
}
