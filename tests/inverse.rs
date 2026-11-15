//! Inverse trigonometry: `atan`, `atan2`, `asin`, `acos` against the
//! independent reference of `tests/common/trig.rs` (three halvings of the
//! argument and the full Taylor series of `atan`, no table).
//!
//! Every result is within 1 ulp of the true value and `atan`, `asin` and
//! `atan2` in `y` (for `y ≠ 0`) are odd bit for bit. Every value of `FixedFloat8` and
//! `FixedFloat16` and every pair of `atan2` on `FixedFloat8`; every value of
//! `FixedFloat32` only with `--ignored`; on these types every result is also
//! correctly rounded. Every pair of `atan2` on `FixedFloat16` runs with
//! `--ignored` without the reference, for no panic and the range.
//! `FixedFloat64` and pairs on wider types: edge-biased random values here and
//! the rational oracle in `oracle/tests/inverse.rs`.

#![cfg(not(feature = "strict-overflow"))]

#[macro_use]
mod common;

use common::trig;
use common::*;
use fulcrum::*;

/// Checks `got` against the reference `r` of one function; returns whether
/// it is correctly rounded.
fn check(name: &str, x: &dyn core::fmt::Debug, got: i128, r: i128, f: u32) -> bool {
    assert!(
        trig::within_ulp(got, r, f),
        "{} {:?} = {}, reference {}",
        name,
        x,
        got,
        r
    );
    trig::correctly_rounded(r, f) == Some(got)
}

/// Checks `atan`, `asin`, `acos` and their `checked_*` of one value; returns
/// how many of the three are correctly rounded (`asin` and `acos` count as
/// rounded outside `[-1, 1]`, where they clamp).
macro_rules! check_inverse {
    ($T:ident, $f:expr, $a:expr) => {{
        let x = $T::from_bits($a);
        let a = $a as i128;
        let mut rounded = check(
            "atan",
            &x,
            x.atan().to_bits() as i128,
            trig::atan(a, $f),
            $f,
        ) as u32;
        if x != $T::MIN {
            assert_eq!((-x).atan(), -x.atan(), "atan odd {:?}", x);
        }
        let one = 1i128 << $f;
        if a.abs() <= one {
            let (s, c) = (x.asin(), x.acos());
            assert_eq!(x.checked_asin(), Some(s), "checked_asin {:?}", x);
            assert_eq!(x.checked_acos(), Some(c), "checked_acos {:?}", x);
            rounded += check("asin", &x, s.to_bits() as i128, trig::asin(a, $f), $f) as u32;
            rounded += check("acos", &x, c.to_bits() as i128, trig::acos(a, $f), $f) as u32;
            if x != $T::MIN {
                assert_eq!((-x).asin(), -s, "asin odd {:?}", x);
            }
        } else {
            let edge = $T::from_bits(if a < 0 { -one } else { one } as _);
            assert_eq!(x.checked_asin(), None, "checked_asin {:?}", x);
            assert_eq!(x.checked_acos(), None, "checked_acos {:?}", x);
            assert_eq!(x.asin(), edge.asin(), "asin clamps {:?}", x);
            assert_eq!(x.acos(), edge.acos(), "acos clamps {:?}", x);
            rounded += 2;
        }
        rounded
    }};
}

/// Checks `atan2(y, x)`; returns whether it is correctly rounded.
macro_rules! check_atan2 {
    ($T:ident, $f:expr, $y:expr, $x:expr) => {{
        let (y, x) = ($T::from_bits($y), $T::from_bits($x));
        let t = y.atan2(x);
        if y != $T::MIN && y != $T::ZERO {
            assert_eq!((-y).atan2(x), -t, "atan2 odd {:?} {:?}", y, x);
        }
        check(
            "atan2",
            &(y, x),
            t.to_bits() as i128,
            trig::atan2($y as i128, $x as i128),
            $f,
        )
    }};
}

macro_rules! exact_points {
    ($module:ident, $T:ident, $lit:ident, $Acc:ident, $Raw:ident, $bits:tt, $f:tt) => {
        #[test]
        fn $module() {
            let (zero, one) = ($T::ZERO, $T::ONE);
            assert_eq!(zero.atan(), zero);
            assert_eq!(zero.asin(), zero);
            assert_eq!(one.asin(), $T::FRAC_PI_2);
            assert_eq!(one.acos(), zero);
            assert_eq!((-one).acos(), $T::PI);
            assert_eq!(zero.acos(), $T::FRAC_PI_2);
            assert_eq!(one.atan(), $T::FRAC_PI_4);
            assert_eq!(zero.atan2(zero), zero);
            assert_eq!(zero.atan2(-one), $T::PI);
            assert_eq!(one.atan2(zero), $T::FRAC_PI_2);
            assert_eq!((-one).atan2(zero), -$T::FRAC_PI_2);
            assert_eq!(one.atan2(one), $T::FRAC_PI_4);
        }
    };
}

mod exact {
    use super::*;
    for_each_width!(exact_points!());
}

#[test]
fn fixed8_all_values_correctly_rounded() {
    let mut rounded = 0;
    for a in i8::MIN..=i8::MAX {
        rounded += check_inverse!(FixedFloat8, 4, a);
    }
    assert_eq!(rounded, 3 * 256);
}

#[test]
fn fixed8_all_pairs_of_atan2_correctly_rounded() {
    let mut rounded = 0;
    for y in i8::MIN..=i8::MAX {
        for x in i8::MIN..=i8::MAX {
            rounded += check_atan2!(FixedFloat8, 4, y, x) as u32;
        }
    }
    assert_eq!(rounded, 65536);
}

#[test]
fn fixed16_all_values_correctly_rounded() {
    let mut rounded = 0;
    for a in i16::MIN..=i16::MAX {
        rounded += check_inverse!(FixedFloat16, 8, a);
    }
    assert_eq!(rounded, 3 * 65536);
}

/// Every value of `FixedFloat32`, on every available thread.
#[test]
#[ignore]
fn fixed32_all_values_correctly_rounded() {
    let threads = std::thread::available_parallelism().map_or(1, |n| n.get()) as i64;
    let span = (1i64 << 32) / threads + 1;
    let workers: Vec<_> = (0..threads)
        .map(|k| {
            std::thread::spawn(move || {
                let start = i32::MIN as i64 + k * span;
                let end = (start + span).min(i32::MAX as i64 + 1);
                let mut rounded = 0u64;
                for a in start..end {
                    rounded += check_inverse!(FixedFloat32, 16, a as i32) as u64;
                }
                rounded
            })
        })
        .collect();
    let rounded: u64 = workers.into_iter().map(|w| w.join().unwrap()).sum();
    assert_eq!(rounded, 3 << 32);
}

/// Every pair of `atan2` on `FixedFloat16`, without the reference: no panic
/// (with overflow checks, as in the weekly run) and the result in `[-π, π]`.
#[test]
#[ignore]
fn fixed16_all_pairs_of_atan2_in_range() {
    let threads = std::thread::available_parallelism().map_or(1, |n| n.get()) as i32;
    let span = 65536 / threads + 1;
    let workers: Vec<_> = (0..threads)
        .map(|k| {
            std::thread::spawn(move || {
                let start = i16::MIN as i32 + k * span;
                let end = (start + span).min(i16::MAX as i32 + 1);
                let pi = FixedFloat16::PI;
                for y in start..end {
                    let y = FixedFloat16::from_bits(y as i16);
                    for x in i16::MIN..=i16::MAX {
                        let t = y.atan2(FixedFloat16::from_bits(x));
                        assert!(-pi <= t && t <= pi, "atan2 {:?} {}", y, x);
                    }
                }
            })
        })
        .collect();
    for w in workers {
        w.join().unwrap();
    }
}

macro_rules! random_values {
    ($module:ident, $T:ident, $lit:ident, $Acc:ident, $Raw:ident, $bits:tt, $f:tt) => {
        #[test]
        fn $module() {
            let mut rng = Pcg32::new(53, $bits);
            for _ in 0..100_000 {
                let a = rng.edge_bits($bits, $f) as $Raw;
                let b = rng.edge_bits($bits, $f) as $Raw;
                let _ = check_inverse!($T, $f, a);
                let _ = check_atan2!($T, $f, a, b);
            }
        }
    };
}

mod random {
    use super::*;
    for_each_width!(random_values!());
}

fn generic_atan2<T: FixedFloat>(y: T, x: T) -> T {
    y.atan2(x)
}

#[test]
fn trait_atan2() {
    for (y, x) in [
        (ff32!(0.5), ff32!(-3)),
        (FixedFloat32::MIN, FixedFloat32::MAX),
    ] {
        assert_eq!(generic_atan2(y, x), y.atan2(x));
    }
    let (y, x) = (ff64!(-1000000000), ff64!(0.25));
    assert_eq!(generic_atan2(y, x), y.atan2(x));
}

/// Just below the cut along the negative axis the angle rounds to `-π`.
#[test]
fn atan2_rounds_to_minus_pi_below_the_cut() {
    let y = -FixedFloat8::DELTA;
    assert_eq!(y.atan2(FixedFloat8::MIN), -FixedFloat8::PI);
}
