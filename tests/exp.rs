//! The binary logarithm and exponential against the independent reference
//! of `tests/common/exp.rs` (no table, the full series).
//!
//! `log2` is within 1 ulp, exact on powers of two, `MIN` and
//! `None` for `x ≤ 0`. `exp2` is within 1 ulp, exact on integers `≥ -FRAC_BITS`,
//! `MAX` and `None` above the range. Every value of `FixedFloat8` and `FixedFloat16`, and
//! of `FixedFloat32` only with `--ignored`; on these three types every result
//! is also correctly rounded and both are monotone. `FixedFloat64`: edge-biased random values here
//! and the rational oracle in `oracle/tests/exp.rs`.

#![cfg(not(feature = "strict-overflow"))]

#[macro_use]
mod common;

use common::exp;
use common::*;
use fulcrum::*;

/// Checks `log2` of one value; returns whether it is correctly rounded.
macro_rules! check_log2 {
    ($T:ident, $f:expr, $a:expr) => {{
        let x = $T::from_bits($a);
        if $a <= 0 {
            assert_eq!(x.log2(), $T::MIN, "log2 {:?}", x);
            assert_eq!(x.checked_log2(), None, "checked_log2 {:?}", x);
            true
        } else {
            let got = i128::from(x.log2().to_bits());
            assert_eq!(x.checked_log2(), Some(x.log2()), "checked_log2 {:?}", x);
            let r = exp::log2(i128::from($a), $f);
            assert!(
                exp::within_ulp(got, r, exp::LOG2_ERROR, $f),
                "log2 {:?} = {}",
                x,
                got
            );
            exp::correctly_rounded(r, exp::LOG2_ERROR, $f) == Some(got)
        }
    }};
}

macro_rules! log2_exact_points {
    ($module:ident, $T:ident, $lit:ident, $Acc:ident, $Raw:ident, $bits:tt, $f:tt) => {
        #[test]
        fn $module() {
            assert_eq!($T::ONE.log2(), $T::ZERO);
            assert_eq!($T::DELTA.log2(), $T::saturating_from_int(-$f));
            assert_eq!($T::ZERO.log2(), $T::MIN);
            assert_eq!($T::NEG_ONE.checked_log2(), None);
            for k in 0..($bits - 1) {
                let x = $T::from_bits(1 << k);
                assert_eq!(
                    x.log2(),
                    $T::saturating_from_int(k - $f),
                    "log2 2^{}",
                    k - $f
                );
            }
        }
    };
}

mod log2_exact {
    use super::*;
    for_each_width!(log2_exact_points!());
}

#[test]
fn log2_known_values() {
    assert_eq!(ff32!(8).log2(), ff32!(3));
    assert_eq!(ff32!(0.5).log2(), ff32!(-1));
    assert_eq!(
        ff64!(3).log2().to_string(),
        "1.5849625007249414920806884765625"
    );
    assert_eq!(
        ff64!(10).log2().to_string(),
        "3.32192809483967721462249755859375"
    );
}

#[test]
fn fixed8_log2_all_values_correctly_rounded() {
    let mut previous = FixedFloat8::MIN;
    for a in i8::MIN..=i8::MAX {
        assert!(check_log2!(FixedFloat8, 4, a), "rounding {a}");
        let y = FixedFloat8::from_bits(a).log2();
        assert!(y >= previous, "monotone {a}");
        previous = y;
    }
}

#[test]
fn fixed16_log2_all_values_correctly_rounded() {
    let mut previous = FixedFloat16::MIN;
    for a in i16::MIN..=i16::MAX {
        assert!(check_log2!(FixedFloat16, 8, a), "rounding {a}");
        let y = FixedFloat16::from_bits(a).log2();
        assert!(y >= previous, "monotone {a}");
        previous = y;
    }
}

/// Runs `check` on every value of `FixedFloat32` on every available thread
/// and returns the number of values for which it returned `true`.
fn every_fixed32(check: fn(i32) -> bool) -> u64 {
    let threads =
        std::thread::available_parallelism().map_or(1, std::num::NonZeroUsize::get) as i64;
    let span = (1i64 << 32) / threads + 1;
    let workers: Vec<_> = (0..threads)
        .map(|k| {
            std::thread::spawn(move || {
                let start = i64::from(i32::MIN) + k * span;
                let end = (start + span).min(i64::from(i32::MAX) + 1);
                (start..end).filter(|&a| check(a as i32)).count() as u64
            })
        })
        .collect();
    workers.into_iter().map(|w| w.join().unwrap()).sum()
}

#[test]
#[ignore = "exhaustive over 2^32 values, minutes on every core: the weekly run"]
fn fixed32_log2_all_values_correctly_rounded() {
    let rounded = every_fixed32(|a| {
        let x = FixedFloat32::from_bits(a);
        let next = FixedFloat32::from_bits(a.saturating_add(1));
        assert!(next.log2() >= x.log2(), "monotone {a}");
        check_log2!(FixedFloat32, 16, a)
    });
    assert_eq!(rounded, 1 << 32);
}

macro_rules! log2_random_values {
    ($module:ident, $T:ident, $lit:ident, $Acc:ident, $Raw:ident, $bits:tt, $f:tt) => {
        #[test]
        fn $module() {
            let mut rng = Pcg32::new(59, $bits);
            for _ in 0..200_000 {
                let a = rng.edge_bits($bits, $f) as $Raw;
                let _ = check_log2!($T, $f, a);
            }
        }
    };
}

mod log2_random {
    use super::*;
    for_each_width!(log2_random_values!());
}

/// Checks `exp2` of one value; returns whether it is correctly rounded or
/// saturated.
macro_rules! check_exp2 {
    ($T:ident, $f:expr, $a:expr) => {{
        let x = $T::from_bits($a);
        let got = x.exp2();
        let (m, s, error) = exp::exp2(i128::from($a), $f);
        let max = $T::MAX.to_bits() as u128;
        let n = i128::from($a) >> $f;
        if n >= $f - 1 || exp::round_scaled(m - error, s) > max {
            assert_eq!(got, $T::MAX, "exp2 {:?}", x);
            assert_eq!(x.checked_exp2(), None, "checked_exp2 {:?}", x);
            true
        } else if exp::round_scaled(m + error, s) > max {
            assert_eq!(
                x.checked_exp2().unwrap_or($T::MAX),
                got,
                "checked_exp2 {:?}",
                x
            );
            false
        } else {
            assert_eq!(x.checked_exp2(), Some(got), "checked_exp2 {:?}", x);
            let got = got.to_bits() as u128;
            assert!(
                exp::exp2_within_ulp(got, m, s, error),
                "exp2 {:?} = {}",
                x,
                got
            );
            exp::exp2_correctly_rounded(m, s, error) == Some(got)
        }
    }};
}

macro_rules! exp2_exact_points {
    ($module:ident, $T:ident, $lit:ident, $Acc:ident, $Raw:ident, $bits:tt, $f:tt) => {
        #[test]
        fn $module() {
            assert_eq!($T::ZERO.exp2(), $T::ONE);
            assert_eq!($T::MIN.exp2(), $T::ZERO);
            assert_eq!($T::MAX.exp2(), $T::MAX);
            assert_eq!($T::MAX.checked_exp2(), None);
            for k in -($f + 1)..($f - 1) {
                let x = $T::saturating_from_int(k);
                let expected = if k >= -$f {
                    $T::from_bits(1 << (k + $f))
                } else {
                    $T::DELTA
                };
                assert_eq!(x.exp2(), expected, "exp2 {}", k);
            }
            assert_eq!($T::saturating_from_int(-$f - 2).exp2(), $T::ZERO);
            assert_eq!($T::saturating_from_int($f - 1).checked_exp2(), None);
        }
    };
}

mod exp2_exact {
    use super::*;
    for_each_width!(exp2_exact_points!());
}

#[test]
fn exp2_known_values() {
    assert_eq!(ff32!(0.5).exp2(), FixedFloat32::SQRT_2);
    assert_eq!(ff64!(0.5).exp2(), FixedFloat64::SQRT_2);
    assert_eq!(ff64!(-0.5).exp2(), FixedFloat64::FRAC_1_SQRT_2);
    assert_eq!(
        ff64!(30.25).exp2().to_string(),
        "1276901416.77679948322474956512451171875"
    );
}

#[test]
fn fixed8_exp2_all_values_correctly_rounded() {
    let mut previous = FixedFloat8::ZERO;
    for a in i8::MIN..=i8::MAX {
        assert!(check_exp2!(FixedFloat8, 4, a), "rounding {a}");
        let y = FixedFloat8::from_bits(a).exp2();
        assert!(y >= previous, "monotone {a}");
        previous = y;
    }
}

#[test]
fn fixed16_exp2_all_values_correctly_rounded() {
    let mut previous = FixedFloat16::ZERO;
    for a in i16::MIN..=i16::MAX {
        assert!(check_exp2!(FixedFloat16, 8, a), "rounding {a}");
        let y = FixedFloat16::from_bits(a).exp2();
        assert!(y >= previous, "monotone {a}");
        previous = y;
    }
}

#[test]
#[ignore = "exhaustive over 2^32 values, minutes on every core: the weekly run"]
fn fixed32_exp2_all_values_correctly_rounded() {
    let rounded = every_fixed32(|a| {
        let x = FixedFloat32::from_bits(a);
        let next = FixedFloat32::from_bits(a.saturating_add(1));
        assert!(next.exp2() >= x.exp2(), "monotone {a}");
        check_exp2!(FixedFloat32, 16, a)
    });
    assert_eq!(rounded, 1 << 32);
}

macro_rules! exp2_random_values {
    ($module:ident, $T:ident, $lit:ident, $Acc:ident, $Raw:ident, $bits:tt, $f:tt) => {
        #[test]
        fn $module() {
            let mut rng = Pcg32::new(61, $bits);
            for _ in 0..200_000 {
                let a = rng.edge_bits($bits, $f) as $Raw;
                let _ = check_exp2!($T, $f, a);
            }
        }
    };
}

mod exp2_random {
    use super::*;
    for_each_width!(exp2_random_values!());
}
