//! Square roots: `sqrt`, `rsqrt`, `hypot` and their `checked_*` variants
//! against `spec::sqrt_ratio` and `spec::is_sqrt_ratio` of
//! `tests/common/reference.rs` over `i128`, a binary search and the
//! definition of rounding to nearest, independent of the Newton iteration of
//! the kernel. All three are correctly rounded.
//!
//! `FixedFloat8`: every value and every pair. `FixedFloat16`: every value;
//! every pair of `hypot` only with `--ignored`. `FixedFloat32`: every value of
//! `sqrt` and `rsqrt` only with `--ignored`. Wider types: edge-biased random
//! values; `hypot` of `FixedFloat64` squares beyond `i128` and is checked by
//! the rational oracle (`oracle/tests/ops.rs`).

#![cfg(not(feature = "strict-overflow"))]

#[macro_use]
mod common;

use common::*;
use fulcrum::*;

macro_rules! check_roots {
    ($T:ident, $bits:expr, $f:expr, $a:expr) => {{
        let ra = $a as i128;
        let x = $T::from_bits($a);

        let (sqrt, checked_sqrt) = if ra < 0 {
            (0, None)
        } else {
            let s = spec::sqrt(ra << $f);
            (s, Some(s))
        };
        assert_eq!(x.sqrt().to_bits() as i128, sqrt, "sqrt {:?}", x);
        assert_eq!(
            x.checked_sqrt().map(|v| v.to_bits() as i128),
            checked_sqrt,
            "checked_sqrt {:?}",
            x
        );
        assert_eq!(
            generic_sqrt(x).to_bits() as i128,
            sqrt,
            "FixedFloat::sqrt {:?}",
            x
        );

        let (rsqrt, checked_rsqrt) = if ra <= 0 {
            (spec::div_by_zero(1, $bits), None)
        } else {
            let s = spec::sqrt_ratio(1 << (3 * $f), ra);
            assert!(spec::fits(s, $bits), "rsqrt {:?} out of range", x);
            (s, Some(s))
        };
        assert_eq!(x.rsqrt().to_bits() as i128, rsqrt, "rsqrt {:?}", x);
        assert_eq!(
            x.checked_rsqrt().map(|v| v.to_bits() as i128),
            checked_rsqrt,
            "checked_rsqrt {:?}",
            x
        );
    }};
}

macro_rules! check_hypot {
    ($T:ident, $bits:expr, $a:expr, $b:expr) => {{
        let (ra, rb) = ($a as i128, $b as i128);
        let (x, y) = ($T::from_bits($a), $T::from_bits($b));
        let h = spec::sqrt(ra * ra + rb * rb);
        assert_eq!(
            x.hypot(y).to_bits() as i128,
            spec::saturate(h, $bits),
            "hypot {:?} {:?}",
            x,
            y
        );
        assert_eq!(
            x.checked_hypot(y).map(|v| v.to_bits() as i128),
            Some(h).filter(|&v| spec::fits(v, $bits)),
            "checked_hypot {:?} {:?}",
            x,
            y
        );
    }};
}

fn generic_sqrt<T: FixedFloat>(x: T) -> T {
    x.sqrt()
}

#[test]
fn fixed8_all_values_and_pairs() {
    for a in i8::MIN..=i8::MAX {
        check_roots!(FixedFloat8, 8, 4, a);
        for b in i8::MIN..=i8::MAX {
            check_hypot!(FixedFloat8, 8, a, b);
        }
    }
}

#[test]
fn fixed16_all_values() {
    for a in i16::MIN..=i16::MAX {
        check_roots!(FixedFloat16, 16, 8, a);
    }
}

macro_rules! random_values {
    (fixed8, $($rest:tt)*) => {};
    ($module:ident, $T:ident, $lit:ident, $Acc:ident, $Raw:ident, $bits:tt, $f:tt) => {{
        let mut rng = Pcg32::new(31, $bits);
        for _ in 0..100_000 {
            let a = rng.edge_bits($bits, $f) as $Raw;
            check_roots!($T, $bits, $f, a);
            if $bits < 64 {
                let b = rng.edge_bits($bits, $f) as $Raw;
                check_hypot!($T, $bits, a, b);
            }
        }
    }};
}

#[test]
fn random_values_on_wider_types() {
    for_each_i128_width!(random_values!());
}

fn parallel<F: Fn(i64) + Send + Sync + 'static>(lo: i64, hi: i64, f: F) {
    let threads = std::thread::available_parallelism().map_or(4, |n| n.get()) as i64;
    let chunk = (hi - lo) / threads + 1;
    let f = std::sync::Arc::new(f);
    let handles: Vec<_> = (0..threads)
        .map(|t| {
            let f = std::sync::Arc::clone(&f);
            std::thread::spawn(move || {
                let start = lo + t * chunk;
                let end = (start + chunk).min(hi);
                for v in start..end {
                    f(v);
                }
            })
        })
        .collect();
    for h in handles {
        h.join().unwrap();
    }
}

#[test]
#[ignore = "2^32 pairs: run with --ignored --release"]
fn fixed16_hypot_all_pairs() {
    parallel(i16::MIN as i64, i16::MAX as i64 + 1, |a| {
        let x = FixedFloat16::from_bits(a as i16);
        let ra = a as i128;
        for b in i16::MIN..=i16::MAX {
            let rb = b as i128;
            let n = ra * ra + rb * rb;
            let h = x.checked_hypot(FixedFloat16::from_bits(b));
            match h {
                Some(h) => assert!(
                    spec::is_sqrt_ratio(h.to_bits() as i128, n, 1),
                    "hypot {} {}",
                    a,
                    b
                ),
                None => assert!(
                    4 * n >= (2 * i16::MAX as i128 + 1).pow(2),
                    "checked_hypot {} {} is None",
                    a,
                    b
                ),
            }
        }
    });
}

#[test]
#[ignore = "2^32 values: run with --ignored --release"]
fn fixed32_sqrt_rsqrt_all_values() {
    parallel(i32::MIN as i64, i32::MAX as i64 + 1, |a| {
        let x = FixedFloat32::from_bits(a as i32);
        let ra = a as i128;
        if ra < 0 {
            assert_eq!(x.sqrt(), FixedFloat32::ZERO, "sqrt {}", a);
            assert_eq!(x.rsqrt(), FixedFloat32::MAX, "rsqrt {}", a);
        } else {
            let s = x.sqrt().to_bits() as i128;
            assert!(spec::is_sqrt_ratio(s, ra << 16, 1), "sqrt {}", a);
            if ra > 0 {
                let r = x.rsqrt().to_bits() as i128;
                assert!(spec::is_sqrt_ratio(r, 1 << 48, ra), "rsqrt {}", a);
            }
        }
    });
}

macro_rules! known_values {
    ($module:ident, $T:ident, $lit:ident, $Acc:ident, $Raw:ident, $bits:tt, $f:tt) => {
        mod $module {
            use super::*;

            #[test]
            fn exact_squares_and_constants() {
                let two = $lit!(2);
                assert_eq!($lit!(4).sqrt(), two);
                assert_eq!($lit!(0.25).sqrt(), $T::HALF);
                assert_eq!($T::ZERO.sqrt(), $T::ZERO);
                assert_eq!($T::ONE.sqrt(), $T::ONE);
                assert_eq!(two.sqrt(), $T::SQRT_2);
                assert_eq!($lit!(3).sqrt(), $T::SQRT_3);
                assert_eq!($lit!(4).rsqrt(), $T::HALF);
                assert_eq!(two.rsqrt(), $T::FRAC_1_SQRT_2);
                assert_eq!($lit!(3).hypot($lit!(-4)), $lit!(5));
                assert_eq!($lit!(-1).hypot($lit!(1)), $T::SQRT_2);
            }

            #[test]
            fn domain_edges() {
                assert_eq!($T::NEG_ONE.sqrt(), $T::ZERO);
                assert_eq!($T::MIN.checked_sqrt(), None);
                assert_eq!($T::NEG_ONE.checked_sqrt(), None);
                assert_eq!($T::ZERO.rsqrt(), $T::MAX);
                assert_eq!($T::MIN.rsqrt(), $T::MAX);
                assert_eq!($T::ZERO.checked_rsqrt(), None);
                assert_eq!(
                    $T::DELTA.checked_rsqrt().map(|v| v.is_positive()),
                    Some(true)
                );
                assert_eq!($T::MAX.hypot($T::MAX), $T::MAX);
                assert_eq!($T::MAX.checked_hypot($T::ONE), None);
                assert_eq!($T::MIN.hypot($T::ZERO), $T::MAX);
                assert_eq!($T::MIN.checked_hypot($T::ZERO), None);
                assert_eq!($T::MAX.hypot($T::ZERO), $T::MAX);
                assert_eq!($T::MAX.checked_hypot($T::ZERO), Some($T::MAX));
            }
        }
    };
}

for_each_width!(known_values!());
