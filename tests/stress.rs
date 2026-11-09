//! Long randomized stress test for the widths that cannot be enumerated
//! (`FixedFloat32`, `FixedFloat64`), on every core, against the independent
//! `i128` reference of `tests/common`. Inputs are biased toward edge cases.
//!
//! Ignored by default. Settings come from `FULCRUM_STRESS_*` (see
//! `common::run_streams`):
//!
//! ```text
//! FULCRUM_STRESS_SECS=600 FULCRUM_STRESS_SEED=42 cargo test --release --test stress -- --ignored --nocapture
//! ```
//!
//! Without `FULCRUM_STRESS_SEED` the seed is taken from the clock and printed;
//! a failure prints the seed, stream and batch to replay it exactly.

#![cfg(not(feature = "strict-overflow"))]

#[macro_use]
mod common;

use common::*;
use fulcrum::*;

/// One in this many pairs also runs the unary checks.
const UNARY_EVERY: u32 = 64;

/// Most digits after the point the `i128` reference of `rounded_decimal`
/// formats without overflow for a 64-bit raw value.
const MAX_REF_PRECISION: u32 = 19;

/// One pair, and sometimes the unary checks, on every width that
/// `tests/exhaustive.rs` does not enumerate.
macro_rules! stress_width {
    ($rng:ident, fixed8, $($rest:tt)*) => {};
    ($rng:ident, fixed16, $($rest:tt)*) => {};
    ($rng:ident, $module:ident, $T:ident, $lit:ident, $Acc:ident, $Raw:ident, $bits:tt, $f:tt) => {{
        let a = $rng.edge_bits($bits, $f) as $Raw;
        let b = $rng.edge_bits($bits, $f) as $Raw;
        check_pair!($T, $bits, $f, a, b);
        if $rng.below(UNARY_EVERY) == 0 {
            check_unary!($T, $bits, $f, a, core::cmp::min($f + 1, MAX_REF_PRECISION));
        }
    }};
}

#[test]
#[ignore = "long running: set FULCRUM_STRESS_* and run with --ignored --release"]
fn stress_fixed32_fixed64() {
    let t = run_streams("stress", "FULCRUM_STRESS", 60, |rng| {
        for_each_i128_width!(stress_width!(rng,));
        0
    });
    eprintln!(
        "stress: {} pairs per width checked, seed {}",
        t.items, t.seed
    );
}
