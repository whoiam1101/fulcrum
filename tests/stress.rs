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
use fulcrum::{FixedFloat32, FixedFloat64};

/// One in this many pairs also runs the unary checks.
const UNARY_EVERY: u32 = 64;

#[test]
#[ignore = "long running: set FULCRUM_STRESS_* and run with --ignored --release"]
fn stress_fixed32_fixed64() {
    let t = run_streams("stress", "FULCRUM_STRESS", 60, |rng| {
        let a = rng.edge_bits(32, 16) as i32;
        let b = rng.edge_bits(32, 16) as i32;
        check_pair!(FixedFloat32, 32, 16, a, b);
        let c = rng.edge_bits(64, 32);
        let d = rng.edge_bits(64, 32);
        check_pair!(FixedFloat64, 64, 32, c, d);
        if rng.below(UNARY_EVERY) == 0 {
            check_unary!(FixedFloat32, 32, 16, a);
            check_unary!(FixedFloat64, 64, 32, c, 19);
        }
        0
    });
    eprintln!(
        "stress: {} pairs per width checked, seed {}",
        t.items, t.seed
    );
}
