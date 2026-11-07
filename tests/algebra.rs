//! Algebraic properties of `+` and `*` (docs/ARCHITECTURE.md §5.1).
//!
//! Commutativity holds everywhere. Associativity holds only where it is
//! promised:
//!
//! * `+`: whenever no partial sum saturates, and always when all terms have
//!   the same sign; `wrapping_add` always.
//! * `*`: bit for bit when the second and third factors are integers and
//!   nothing saturates; otherwise, without saturation,
//!   `|(a·b)·c − a·(b·c)| ≤ ⌊½(|a| + |c|)⌋ + 1` ulp (see [`mul_assoc_bound`]).
//!
//! `documented_counterexamples` runs with the normal test suite. The other
//! tests are ignored by default; `algebra_stress` takes its settings from
//! `FULCRUM_ALGEBRA_*` (see `common::run_streams`):
//!
//! ```text
//! FULCRUM_ALGEBRA_SEED=1 FULCRUM_ALGEBRA_THREADS=4 FULCRUM_ALGEBRA_BATCHES=64 cargo test --release --test algebra -- --include-ignored --nocapture
//! ```
//!
//! Without `FULCRUM_ALGEBRA_SEED` the seed is taken from the clock and
//! printed; a failure prints the seed, stream and batch to replay it exactly.

#![cfg(not(feature = "strict-overflow"))]

mod common;

use common::*;
use fulcrum::{FixedFloat16, FixedFloat32, FixedFloat64, FixedFloat8};

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

/// Associativity checks for one triple. Evaluates to `true` when neither
/// association of `*` saturated, so the `*` checks actually ran.
macro_rules! check_triple {
    ($T:ident, $bits:expr, $f:expr, $a:expr, $b:expr, $c:expr) => {{
        let (ra, rb, rc): (i128, i128, i128) = ($a as i128, $b as i128, $c as i128);
        let x = $T::from_bits($a);
        let y = $T::from_bits($b);
        let z = $T::from_bits($c);
        let ctx = || format!("{} ({:?}, {:?}, {:?})", stringify!($T), x, y, z);

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
            true
        } else {
            false
        }
    }};
}

/// Random triple with edge-biased `a`, `b`, `c`, then the same `a` with
/// integer `b`, `c`. Checks commutativity on all three pairs of the first
/// triple; evaluates to how many of the two triples reached the `*` checks.
macro_rules! check_width {
    ($rng:expr, $T:ident, $I:ty, $bits:expr, $f:expr) => {{
        let rng: &mut Pcg32 = $rng;
        let a = rng.edge_bits($bits, $f) as $I;
        let b = rng.edge_bits($bits, $f) as $I;
        let c = rng.edge_bits($bits, $f) as $I;
        let (x, y, z) = ($T::from_bits(a), $T::from_bits(b), $T::from_bits(c));
        check_commutative!($T, x, y);
        check_commutative!($T, y, z);
        check_commutative!($T, x, z);
        let mut mul = check_triple!($T, $bits, $f, a, b, c) as u64;
        let b = int_bits(rng, $bits, $f) as $I;
        let c = int_bits(rng, $bits, $f) as $I;
        mul += check_triple!($T, $bits, $f, a, b, c) as u64;
        mul
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
#[ignore = "2^16 pairs and 2^24 triples: run with --release --include-ignored"]
fn exhaustive_fixed8() {
    for a in i8::MIN..=i8::MAX {
        for b in i8::MIN..=i8::MAX {
            check_commutative!(
                FixedFloat8,
                FixedFloat8::from_bits(a),
                FixedFloat8::from_bits(b)
            );
        }
    }
    let mut mul = 0u64;
    for a in i8::MIN..=i8::MAX {
        for b in i8::MIN..=i8::MAX {
            for c in i8::MIN..=i8::MAX {
                mul += check_triple!(FixedFloat8, 8, 4, a, b, c) as u64;
            }
        }
    }
    eprintln!("algebra: {} of 2^24 Q4.4 triples reached the * checks", mul);
    assert!(mul > 0);
}

/// Fraction of generated triples, in percent, that must reach the `*` checks.
/// Edge-biased factors saturate often; if a generator change made that the
/// rule, the `*` association checks would silently stop running.
const MIN_MUL_PERCENT: u64 = 20;

#[test]
#[ignore = "randomized: set FULCRUM_ALGEBRA_* and run with --release --ignored"]
fn algebra_stress() {
    let t = run_streams("algebra", "FULCRUM_ALGEBRA", 60, |rng| {
        check_width!(rng, FixedFloat16, i16, 16, 8)
            + check_width!(rng, FixedFloat32, i32, 32, 16)
            + check_width!(rng, FixedFloat64, i64, 64, 32)
    });
    let triples = t.items * 2 * 3;
    eprintln!(
        "algebra: {} triples per width checked (half with integer b, c); {} of {} in all reached the * checks; seed {}",
        t.items * 2,
        t.tally,
        triples,
        t.seed
    );
    assert!(
        t.tally * 100 >= triples * MIN_MUL_PERCENT,
        "only {} of {} triples reached the * checks",
        t.tally,
        triples
    );
}
