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

/// Checks `ln` of one value; returns whether it is correctly rounded.
macro_rules! check_ln {
    ($T:ident, $f:expr, $a:expr) => {{
        let x = $T::from_bits($a);
        if $a <= 0 {
            assert_eq!(x.ln(), $T::MIN, "ln {:?}", x);
            assert_eq!(x.checked_ln(), None, "checked_ln {:?}", x);
            true
        } else {
            let got = i128::from(x.ln().to_bits());
            assert_eq!(x.checked_ln(), Some(x.ln()), "checked_ln {:?}", x);
            let r = exp::ln(i128::from($a), $f);
            assert!(
                exp::within_ulp(got, r, exp::LN_ERROR, $f),
                "ln {:?} = {}",
                x,
                got
            );
            exp::correctly_rounded(r, exp::LN_ERROR, $f) == Some(got)
        }
    }};
}

macro_rules! ln_exact_points {
    ($module:ident, $T:ident, $lit:ident, $Acc:ident, $Raw:ident, $bits:tt, $f:tt) => {
        #[test]
        fn $module() {
            assert_eq!($T::ONE.ln(), $T::ZERO);
            assert_eq!($T::ZERO.ln(), $T::MIN);
            assert_eq!($T::MIN.ln(), $T::MIN);
            assert_eq!($T::NEG_ONE.checked_ln(), None);
            assert_eq!($T::ZERO.checked_ln(), None);
        }
    };
}

mod ln_exact {
    use super::*;
    for_each_width!(ln_exact_points!());
}

#[test]
fn ln_known_values() {
    assert_eq!(FixedFloat64::E.ln(), FixedFloat64::ONE);
    assert_eq!(FixedFloat32::E.ln(), FixedFloat32::ONE);
    assert_eq!(ff64!(2).ln(), FixedFloat64::LN_2);
    assert_eq!(ff64!(10).ln(), FixedFloat64::LN_10);
    assert_eq!(ff64!(0.5).ln(), -FixedFloat64::LN_2);
}

#[test]
fn fixed8_ln_all_values_correctly_rounded() {
    let mut previous = FixedFloat8::MIN;
    for a in i8::MIN..=i8::MAX {
        assert!(check_ln!(FixedFloat8, 4, a), "rounding {a}");
        let y = FixedFloat8::from_bits(a).ln();
        assert!(y >= previous, "monotone {a}");
        previous = y;
    }
}

#[test]
fn fixed16_ln_all_values_correctly_rounded() {
    let mut previous = FixedFloat16::MIN;
    for a in i16::MIN..=i16::MAX {
        assert!(check_ln!(FixedFloat16, 8, a), "rounding {a}");
        let y = FixedFloat16::from_bits(a).ln();
        assert!(y >= previous, "monotone {a}");
        previous = y;
    }
}

#[test]
#[ignore = "exhaustive over 2^32 values, minutes on every core: the weekly run"]
fn fixed32_ln_all_values_correctly_rounded() {
    let rounded = every_fixed32(|a| {
        let x = FixedFloat32::from_bits(a);
        let next = FixedFloat32::from_bits(a.saturating_add(1));
        assert!(next.ln() >= x.ln(), "monotone {a}");
        check_ln!(FixedFloat32, 16, a)
    });
    assert_eq!(rounded, 1 << 32);
}

macro_rules! ln_random_values {
    ($module:ident, $T:ident, $lit:ident, $Acc:ident, $Raw:ident, $bits:tt, $f:tt) => {
        #[test]
        fn $module() {
            let mut rng = Pcg32::new(67, $bits);
            for _ in 0..200_000 {
                let a = rng.edge_bits($bits, $f) as $Raw;
                let _ = check_ln!($T, $f, a);
            }
        }
    };
}

mod ln_random {
    use super::*;
    for_each_width!(ln_random_values!());
}

/// Checks `exp` of one value; returns whether it is correctly rounded or
/// saturated.
macro_rules! check_exp {
    ($T:ident, $f:expr, $a:expr) => {{
        let x = $T::from_bits($a);
        let got = x.exp();
        let raw = i128::from($a);
        let max = $T::MAX.to_bits() as u128;
        if raw >= $f << $f {
            assert_eq!(got, $T::MAX, "exp {:?}", x);
            assert_eq!(x.checked_exp(), None, "checked_exp {:?}", x);
            true
        } else if raw <= -($f << $f) {
            assert_eq!(got, $T::ZERO, "exp {:?}", x);
            assert_eq!(x.checked_exp(), Some(got), "checked_exp {:?}", x);
            true
        } else {
            let (m, s, error) = exp::exp(raw, $f);
            if exp::round_scaled(m - error, s) > max {
                assert_eq!(got, $T::MAX, "exp {:?}", x);
                assert_eq!(x.checked_exp(), None, "checked_exp {:?}", x);
                true
            } else if exp::round_scaled(m + error, s) > max {
                assert_eq!(
                    x.checked_exp().unwrap_or($T::MAX),
                    got,
                    "checked_exp {:?}",
                    x
                );
                false
            } else {
                assert_eq!(x.checked_exp(), Some(got), "checked_exp {:?}", x);
                let got = got.to_bits() as u128;
                assert!(
                    exp::exp2_within_ulp(got, m, s, error),
                    "exp {:?} = {}",
                    x,
                    got
                );
                exp::exp2_correctly_rounded(m, s, error) == Some(got)
            }
        }
    }};
}

macro_rules! exp_exact_points {
    ($module:ident, $T:ident, $lit:ident, $Acc:ident, $Raw:ident, $bits:tt, $f:tt) => {
        #[test]
        fn $module() {
            assert_eq!($T::ZERO.exp(), $T::ONE);
            assert_eq!($T::ZERO.checked_exp(), Some($T::ONE));
            assert_eq!($T::MIN.exp(), $T::ZERO);
            assert_eq!($T::MIN.checked_exp(), Some($T::ZERO));
            assert_eq!($T::MAX.exp(), $T::MAX);
            assert_eq!($T::MAX.checked_exp(), None);
            assert_eq!($T::saturating_from_int(-$f).exp(), $T::ZERO);
            assert_eq!($T::saturating_from_int($f - 1).checked_exp(), None);
            assert_eq!($T::ONE.exp(), $T::E);
        }
    };
}

mod exp_exact {
    use super::*;
    for_each_width!(exp_exact_points!());
}

#[test]
fn exp_known_values() {
    assert_eq!(ff32!(-12).exp(), ff32!(0));
    assert_eq!(ff32!(11).exp(), FixedFloat32::MAX);
    assert_eq!(ff32!(11).checked_exp(), None);
    assert_eq!(
        FixedFloat64::LN_10.exp().to_string(),
        "10.00000000069849193096160888671875"
    );
    assert_eq!(
        ff64!(-1).exp().to_string(),
        "0.36787944124080240726470947265625"
    );
    assert_eq!(
        ff64!(21).exp().to_string(),
        "1318815734.48321469710208475589752197265625"
    );
}

#[test]
fn fixed8_exp_all_values_correctly_rounded() {
    let mut previous = FixedFloat8::ZERO;
    for a in i8::MIN..=i8::MAX {
        assert!(check_exp!(FixedFloat8, 4, a), "rounding {a}");
        let y = FixedFloat8::from_bits(a).exp();
        assert!(y >= previous, "monotone {a}");
        previous = y;
    }
}

#[test]
fn fixed16_exp_all_values_correctly_rounded() {
    let mut previous = FixedFloat16::ZERO;
    for a in i16::MIN..=i16::MAX {
        assert!(check_exp!(FixedFloat16, 8, a), "rounding {a}");
        let y = FixedFloat16::from_bits(a).exp();
        assert!(y >= previous, "monotone {a}");
        previous = y;
    }
}

#[test]
#[ignore = "exhaustive over 2^32 values, minutes on every core: the weekly run"]
fn fixed32_exp_all_values_correctly_rounded() {
    let rounded = every_fixed32(|a| {
        let x = FixedFloat32::from_bits(a);
        let next = FixedFloat32::from_bits(a.saturating_add(1));
        assert!(next.exp() >= x.exp(), "monotone {a}");
        check_exp!(FixedFloat32, 16, a)
    });
    assert_eq!(rounded, 1 << 32);
}

macro_rules! exp_random_values {
    ($module:ident, $T:ident, $lit:ident, $Acc:ident, $Raw:ident, $bits:tt, $f:tt) => {
        #[test]
        fn $module() {
            let mut rng = Pcg32::new(71, $bits);
            for _ in 0..200_000 {
                let a = rng.edge_bits($bits, $f) as $Raw;
                let _ = check_exp!($T, $f, a);
            }
        }
    };
}

mod exp_random {
    use super::*;
    for_each_width!(exp_random_values!());
}

/// The six functions of stage 6 through the `FixedFloat` trait.
fn generic_exp_log<T: FixedFloat>(x: T, y: T, n: i32) -> [T; 6] {
    [x.log2(), x.exp2(), x.ln(), x.exp(), x.pow(y), x.powi(n)]
}

macro_rules! trait_equals_inherent {
    ($module:ident, $T:ident, $lit:ident, $Acc:ident, $Raw:ident, $bits:tt, $f:tt) => {
        #[test]
        fn $module() {
            let mut rng = Pcg32::new(83, $bits);
            for _ in 0..20_000 {
                let x = $T::from_bits(rng.edge_bits($bits, $f) as $Raw);
                let y =
                    $T::from_bits((rng.edge_bits($bits, $f) as $Raw) >> (rng.next_u32() % $bits));
                let n = (rng.next_u32() % 64) as i32 - 32;
                let inherent = [x.log2(), x.exp2(), x.ln(), x.exp(), x.pow(y), x.powi(n)];
                assert_eq!(generic_exp_log(x, y, n), inherent, "{:?} {:?} {}", x, y, n);
            }
        }
    };
}

mod trait_exp_log {
    use super::*;
    for_each_width!(trait_equals_inherent!());
}
