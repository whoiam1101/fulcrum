//! Algebraic properties of `+` and `*` (ARCHITECTURE §5.1).
//!
//! Commutativity holds everywhere. Associativity holds only where §5.1
//! promises it:
//!
//! * `+`: whenever no partial sum saturates, and always when all terms have
//!   the same sign; `wrapping_add` always.
//! * `*`: bit for bit when the second and third factors are integers and
//!   nothing saturates; otherwise, without saturation,
//!   `|(a·b)·c − a·(b·c)| ≤ ½(|a| + |c|) + 1` ulp.
//!
//! `documented_counterexamples` runs with the normal test suite. The other
//! tests are ignored by default; duration and seed come from the environment:
//!
//! ```text
//! FULCRUM_ALGEBRA_SECS=60 FULCRUM_ALGEBRA_SEED=1 cargo test --release --test algebra -- --include-ignored --nocapture
//! ```
//!
//! Without `FULCRUM_ALGEBRA_SEED` the seed is taken from the clock and
//! printed, so any failure can be replayed exactly.

#![cfg(not(feature = "strict-overflow"))]

mod common;

use common::*;
use fulcrum::{FixedFloat16, FixedFloat32, FixedFloat64, FixedFloat8};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};

const BATCH: u64 = 4096;

/// Raw value of a random integer that fits the integer part of a
/// `bits`-bit format with `frac_bits` fractional bits.
fn int_bits(rng: &mut Pcg32, bits: u32, frac_bits: u32) -> i64 {
    let width = 1 + rng.below(bits - frac_bits);
    let k = (rng.next_u64() as i64) >> (64 - width);
    k << frac_bits
}

/// Upper bound in ulp on `|(a·b)·c − a·(b·c)|` when nothing saturates.
///
/// Each rounding adds at most ½ ulp, and the rounding error of the first
/// product is scaled by the third factor: the left side is within
/// `½|c| + ½` ulp of the exact `abc`, the right side within `½|a| + ½`.
/// The difference is an integer, so it is at most
/// `floor(½(|a| + |c|)) + 1` ulp.
fn mul_assoc_bound(ra: i128, rc: i128, frac_bits: u32) -> i128 {
    ((ra.abs() + rc.abs()) >> (frac_bits + 1)) + 1
}

macro_rules! check_commutative {
    ($T:ident, $x:expr, $y:expr) => {{
        let (x, y): ($T, $T) = ($x, $y);
        let ctx = || format!("{} ({:?}, {:?})", stringify!($T), x, y);
        assert_eq!(x + y, y + x, "+ commutes {}", ctx());
        assert_eq!(
            x.wrapping_add(y),
            y.wrapping_add(x),
            "wrapping_add {}",
            ctx()
        );
        assert_eq!(x.checked_add(y), y.checked_add(x), "checked_add {}", ctx());
        assert_eq!(
            x.overflowing_add(y),
            y.overflowing_add(x),
            "overflowing_add {}",
            ctx()
        );
        assert_eq!(x * y, y * x, "* commutes {}", ctx());
        assert_eq!(
            x.wrapping_mul(y),
            y.wrapping_mul(x),
            "wrapping_mul {}",
            ctx()
        );
        assert_eq!(x.checked_mul(y), y.checked_mul(x), "checked_mul {}", ctx());
        assert_eq!(
            x.overflowing_mul(y),
            y.overflowing_mul(x),
            "overflowing_mul {}",
            ctx()
        );
    }};
}

macro_rules! check_triple {
    ($T:ident, $bits:expr, $f:expr, $a:expr, $b:expr, $c:expr) => {{
        let (ra, rb, rc): (i128, i128, i128) = ($a as i128, $b as i128, $c as i128);
        let x = $T::from_bits($a);
        let y = $T::from_bits($b);
        let z = $T::from_bits($c);
        let ctx = || format!("{} ({:?}, {:?}, {:?})", stringify!($T), x, y, z);

        check_commutative!($T, x, y);
        check_commutative!($T, y, z);

        let sum = ra + rb + rc;
        assert_eq!(
            x.wrapping_add(y).wrapping_add(z),
            x.wrapping_add(y.wrapping_add(z)),
            "wrapping_add associates {}",
            ctx()
        );
        assert_eq!(
            x.wrapping_add(y).wrapping_add(z).to_bits() as i128,
            wrap(sum, $bits),
            "wrapping_add sum {}",
            ctx()
        );

        let left = x.checked_add(y).and_then(|s| s.checked_add(z));
        let right = y.checked_add(z).and_then(|s| x.checked_add(s));
        if fits(ra + rb, $bits) && fits(rb + rc, $bits) && fits(sum, $bits) {
            assert_eq!(left, right, "checked_add associates {}", ctx());
            assert_eq!(
                left.map(|v| v.to_bits() as i128),
                Some(sum),
                "checked_add exact sum {}",
                ctx()
            );
            assert_eq!((x + y) + z, x + (y + z), "+ associates {}", ctx());
        }

        if (ra >= 0 && rb >= 0 && rc >= 0) || (ra <= 0 && rb <= 0 && rc <= 0) {
            assert_eq!(
                ((x + y) + z).to_bits() as i128,
                clamp(sum, $bits),
                "+ same sign, left {}",
                ctx()
            );
            assert_eq!(
                (x + (y + z)).to_bits() as i128,
                clamp(sum, $bits),
                "+ same sign, right {}",
                ctx()
            );
        }

        let products = (
            x.checked_mul(y).and_then(|p| p.checked_mul(z)),
            y.checked_mul(z).and_then(|p| x.checked_mul(p)),
        );
        if let (Some(l), Some(r)) = products {
            assert_eq!((x * y) * z, l, "* left without saturation {}", ctx());
            assert_eq!(x * (y * z), r, "* right without saturation {}", ctx());
            let one = 1i128 << $f;
            let (rl, rr) = (l.to_bits() as i128, r.to_bits() as i128);
            if rb % one == 0 && rc % one == 0 {
                assert_eq!(rl, rr, "* associates on integers {}", ctx());
            }
            let bound = mul_assoc_bound(ra, rc, $f);
            assert!(
                (rl - rr).abs() <= bound,
                "* association error {} > {} ulp {}",
                (rl - rr).abs(),
                bound,
                ctx()
            );
        }
    }};
}

#[test]
fn documented_counterexamples() {
    type Q = FixedFloat8;
    let (max, d) = (Q::MAX, Q::DELTA);
    assert_eq!((max + d) + (-d), max - d);
    assert_eq!(max + (d + (-d)), max);

    let h = Q::HALF;
    assert_eq!((h * h) * d, Q::ZERO);
    assert_eq!(h * (h * d), d);
}

#[test]
#[ignore = "2^24 triples: run with --release --include-ignored"]
fn exhaustive_fixed8_triples() {
    for a in i8::MIN..=i8::MAX {
        for b in i8::MIN..=i8::MAX {
            for c in i8::MIN..=i8::MAX {
                check_triple!(FixedFloat8, 8, 4, a, b, c);
            }
        }
    }
}

#[test]
#[ignore = "time bounded: set FULCRUM_ALGEBRA_SECS and run with --release --ignored"]
fn algebra_stress() {
    let secs = env_u64("FULCRUM_ALGEBRA_SECS").unwrap_or(60);
    let seed = seed_from_env("FULCRUM_ALGEBRA_SEED");
    let threads = std::thread::available_parallelism().map_or(4, |n| n.get());
    eprintln!(
        "algebra: seed {} ({} s, {} threads); replay with FULCRUM_ALGEBRA_SEED={}",
        seed, secs, threads, seed
    );

    let deadline = Instant::now() + Duration::from_secs(secs);
    let triples = Arc::new(AtomicU64::new(0));
    let handles: Vec<_> = (0..threads as u64)
        .map(|stream| {
            let triples = Arc::clone(&triples);
            std::thread::spawn(move || {
                let mut rng = Pcg32::new(seed, stream);
                let mut done = 0u64;
                while Instant::now() < deadline {
                    for _ in 0..BATCH {
                        let a = rng.edge_bits(16, 8) as i16;
                        let b = rng.edge_bits(16, 8) as i16;
                        let c = rng.edge_bits(16, 8) as i16;
                        check_triple!(FixedFloat16, 16, 8, a, b, c);
                        let b = int_bits(&mut rng, 16, 8) as i16;
                        let c = int_bits(&mut rng, 16, 8) as i16;
                        check_triple!(FixedFloat16, 16, 8, a, b, c);

                        let a = rng.edge_bits(32, 16) as i32;
                        let b = rng.edge_bits(32, 16) as i32;
                        let c = rng.edge_bits(32, 16) as i32;
                        check_triple!(FixedFloat32, 32, 16, a, b, c);
                        let b = int_bits(&mut rng, 32, 16) as i32;
                        let c = int_bits(&mut rng, 32, 16) as i32;
                        check_triple!(FixedFloat32, 32, 16, a, b, c);

                        let a = rng.edge_bits(64, 32);
                        let b = rng.edge_bits(64, 32);
                        let c = rng.edge_bits(64, 32);
                        check_triple!(FixedFloat64, 64, 32, a, b, c);
                        let b = int_bits(&mut rng, 64, 32);
                        let c = int_bits(&mut rng, 64, 32);
                        check_triple!(FixedFloat64, 64, 32, a, b, c);
                    }
                    done += BATCH;
                }
                triples.fetch_add(done, Ordering::Relaxed);
            })
        })
        .collect();
    for h in handles {
        h.join().expect("algebra thread failed, see the seed above");
    }
    eprintln!(
        "algebra: {} triples per width checked (half with integer b, c), seed {}",
        triples.load(Ordering::Relaxed) * 2,
        seed
    );
}
