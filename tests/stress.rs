//! Long randomized stress test for the widths that cannot be enumerated
//! (`FixedFloat32`, `FixedFloat64`), on every core, against the independent
//! `i128` reference of `tests/common`. Inputs are biased toward edge cases.
//!
//! Ignored by default. Duration and seed come from the environment:
//!
//! ```text
//! FULCRUM_STRESS_SECS=600 FULCRUM_STRESS_SEED=42 cargo test --release --test stress -- --ignored --nocapture
//! ```
//!
//! Without `FULCRUM_STRESS_SEED` the seed is taken from the clock and printed,
//! so any failure can be replayed exactly.

#![cfg(not(feature = "strict-overflow"))]

#[macro_use]
mod common;

use common::*;
use fulcrum::{FixedFloat32, FixedFloat64};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};

const BATCH: u64 = 4096;
const UNARY_EVERY: u64 = 64;

#[test]
#[ignore = "long running: set FULCRUM_STRESS_SECS and run with --ignored --release"]
fn stress_fixed32_fixed64() {
    let secs = env_u64("FULCRUM_STRESS_SECS").unwrap_or(60);
    let seed = seed_from_env("FULCRUM_STRESS_SEED");
    let threads = std::thread::available_parallelism().map_or(4, |n| n.get());
    eprintln!(
        "stress: seed {} ({} s, {} threads); replay with FULCRUM_STRESS_SEED={}",
        seed, secs, threads, seed
    );

    let deadline = Instant::now() + Duration::from_secs(secs);
    let pairs = Arc::new(AtomicU64::new(0));
    let handles: Vec<_> = (0..threads as u64)
        .map(|stream| {
            let pairs = Arc::clone(&pairs);
            std::thread::spawn(move || {
                let mut rng = Pcg32::new(seed, stream);
                let mut done = 0u64;
                while Instant::now() < deadline {
                    for i in 0..BATCH {
                        let a = rng.edge_bits(32, 16) as i32;
                        let b = rng.edge_bits(32, 16) as i32;
                        check_pair!(FixedFloat32, 32, 16, a, b);
                        let c = rng.edge_bits(64, 32);
                        let d = rng.edge_bits(64, 32);
                        check_pair!(FixedFloat64, 64, 32, c, d);
                        if i % UNARY_EVERY == 0 {
                            check_unary!(FixedFloat32, 32, 16, a);
                            check_unary!(FixedFloat64, 64, 32, c, 19);
                        }
                    }
                    done += BATCH;
                }
                pairs.fetch_add(done, Ordering::Relaxed);
            })
        })
        .collect();
    for h in handles {
        h.join().expect("stress thread failed, see the seed above");
    }
    eprintln!(
        "stress: {} pairs per width checked, seed {}",
        pairs.load(Ordering::Relaxed),
        seed
    );
}
