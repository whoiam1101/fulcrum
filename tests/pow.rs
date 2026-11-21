//! `pow` and `powi` against the independent reference of
//! `tests/common/exp.rs` (`exp2` of `y · log2 x`, the full series, no table).
//!
//! Both are within 1 ulp, and equal to the correctly rounded value wherever
//! the reference decides it; a result exactly halfway between two values (an
//! exact power such as `(3/8)³` on `FixedFloat16`) may round either way.
//! `x^0 = 1` for every `x`, `0^y` is `0` for `y > 0` and `MAX` with
//! `checked_*` `None` for `y < 0`, a negative `x` takes the sign of an odd
//! integer `y` and gives `0` and `None` for a non-integer `y`. Every pair of
//! `FixedFloat8`, every pair of `FixedFloat16` only with `--ignored`,
//! edge-biased random pairs of `FixedFloat16` and `FixedFloat32`;
//! `FixedFloat64` against the rational oracle in `oracle/tests/exp.rs`.

#![cfg(not(feature = "strict-overflow"))]

#[macro_use]
mod common;

use common::exp;
use common::*;
use fulcrum::*;

/// Checks one result `got`, `checked` of `x^y` for `x = $a / 2^f` and
/// `y = $y / 2^$fy`; returns whether the reference decided the rounding.
macro_rules! check_pow {
    ($T:ident, $f:expr, $a:expr, $y:expr, $fy:expr, $got:expr, $checked:expr) => {{
        let (a, y): (i128, i128) = (i128::from($a), i128::from($y));
        let (got, checked): ($T, Option<$T>) = ($got, $checked);
        let fraction = y & ((1i128 << $fy) - 1);
        let what = || format!("{:?} ^ {} / 2^{}", $T::from_bits($a), y, $fy);
        if y == 0 {
            assert_eq!((got, checked), ($T::ONE, Some($T::ONE)), "{}", what());
            true
        } else if a == 0 {
            if y > 0 {
                assert_eq!((got, checked), ($T::ZERO, Some($T::ZERO)), "{}", what());
            } else {
                assert_eq!((got, checked), ($T::MAX, None), "{}", what());
            }
            true
        } else if a < 0 && fraction != 0 {
            assert_eq!((got, checked), ($T::ZERO, None), "{}", what());
            true
        } else {
            let negative = a < 0 && (y >> $fy) & 1 == 1;
            let (saturated, max) = if negative {
                ($T::MIN, u128::from($T::MIN.to_bits().unsigned_abs()))
            } else {
                ($T::MAX, $T::MAX.to_bits() as u128)
            };
            let (m, s, error) = exp::pow(a.abs(), $f, y, $fy);
            if s <= 1 || exp::round_scaled(m - error, s) > max {
                assert_eq!((got, checked), (saturated, None), "{}", what());
                true
            } else if exp::round_scaled(m + error, s) > max {
                assert_eq!(checked.unwrap_or(saturated), got, "{}", what());
                false
            } else {
                assert_eq!(checked, Some(got), "checked {}", what());
                if negative {
                    assert!(got <= $T::ZERO, "sign {}", what());
                } else {
                    assert!(got >= $T::ZERO, "sign {}", what());
                }
                let g = u128::from(got.to_bits().unsigned_abs());
                assert!(
                    exp::exp2_within_ulp(g, m, s, error),
                    "{} = {:?}",
                    what(),
                    got
                );
                match exp::exp2_correctly_rounded(m, s, error) {
                    Some(v) => {
                        assert_eq!(g, v, "rounding {} = {:?}", what(), got);
                        true
                    }
                    None => false,
                }
            }
        }
    }};
}

/// `check_pow!` of `x.pow(y)`.
macro_rules! check_pow_pair {
    ($T:ident, $f:expr, $a:expr, $b:expr) => {{
        let (x, y) = ($T::from_bits($a), $T::from_bits($b));
        check_pow!($T, $f, $a, $b, $f, x.pow(y), x.checked_pow(y))
    }};
}

/// `check_pow!` of `x.powi(n)`.
macro_rules! check_powi {
    ($T:ident, $f:expr, $a:expr, $n:expr) => {{
        let x = $T::from_bits($a);
        check_pow!($T, $f, $a, $n, 0, x.powi($n), x.checked_powi($n))
    }};
}

macro_rules! pow_exact_points {
    ($module:ident, $T:ident, $lit:ident, $Acc:ident, $Raw:ident, $bits:tt, $f:tt) => {
        #[test]
        fn $module() {
            let two = $T::saturating_from_int(2);
            for x in [
                $T::MIN,
                $T::NEG_ONE,
                $T::ZERO,
                $T::DELTA,
                $T::ONE,
                two,
                $T::MAX,
            ] {
                assert_eq!(x.pow($T::ZERO), $T::ONE, "{:?}^0", x);
                assert_eq!(x.powi(0), $T::ONE, "{:?}^0", x);
                assert_eq!(x.pow($T::ONE), x, "{:?}^1", x);
                assert_eq!(x.powi(1), x, "{:?}^1", x);
            }
            for y in [$T::MIN, $T::NEG_ONE, $T::HALF, $T::DELTA, $T::MAX] {
                assert_eq!($T::ONE.pow(y), $T::ONE, "1^{:?}", y);
            }
            assert_eq!($T::ONE.powi(i32::MIN), $T::ONE);
            assert_eq!($T::NEG_ONE.powi(i32::MAX), $T::NEG_ONE);
            assert_eq!($T::NEG_ONE.powi(i32::MIN), $T::ONE);
            for k in -$f..($bits - $f - 1) {
                let expected = $T::from_bits(1 << (k + $f));
                assert_eq!(
                    two.pow($T::saturating_from_int(i128::from(k))),
                    expected,
                    "2^{}",
                    k
                );
                assert_eq!(two.powi(k), expected, "2^{}", k);
                if k % 2 == 1 {
                    assert_eq!((-two).powi(k), -expected, "-2^{}", k);
                }
            }
            assert_eq!((-two).powi($bits - $f - 1), $T::MIN);
            assert_eq!((-two).checked_powi($bits - $f - 1), Some($T::MIN));
            assert_eq!((-$T::ONE).pow($T::ONE), $T::NEG_ONE);
            assert_eq!(two.checked_powi($bits - $f - 1), None);
            assert_eq!(two.powi($bits - $f - 1), $T::MAX);
            assert_eq!((-two).powi($bits - $f), $T::MAX);
            assert_eq!((-two).checked_powi($bits - $f + 1), None);
            assert_eq!((-two).powi($bits - $f + 1), $T::MIN);
            assert_eq!(two.powi(-$f - 2), $T::ZERO);
            assert_eq!($T::ZERO.pow($T::HALF), $T::ZERO);
            assert_eq!($T::ZERO.pow($T::NEG_ONE), $T::MAX);
            assert_eq!($T::ZERO.checked_powi(-1), None);
            assert_eq!($T::NEG_ONE.pow($T::HALF), $T::ZERO);
            assert_eq!($T::NEG_ONE.checked_pow($T::HALF), None);
            let four = $T::saturating_from_int(4);
            assert_eq!(four.pow($T::HALF), two);
            assert_eq!(four.pow(-$T::HALF), $T::HALF);
        }
    };
}

mod pow_exact {
    use super::*;
    for_each_width!(pow_exact_points!());
}

#[test]
fn pow_known_values() {
    assert_eq!(ff64!(2).pow(ff64!(0.5)), FixedFloat64::SQRT_2);
    assert_eq!(ff64!(10).pow(ff64!(2)), ff64!(100));
    assert_eq!(ff64!(1.5).powi(10), ff64!(57.6650390625));
    assert_eq!(ff64!(-1.5).powi(11), ff64!(-86.49755859375));
    assert_eq!(
        ff64!(0.75).pow(ff64!(-3)).to_string(),
        "2.370370370335876941680908203125"
    );
    assert_eq!(
        ff64!(1.0001).powi(100_000).to_string(),
        "22015.5946387299336493015289306640625"
    );
    assert_eq!(
        ff64!(3).pow(ff64!(19.5)).to_string(),
        "2013095912.52353802672587335109710693359375"
    );
    assert_eq!(ff64!(3).checked_pow(ff64!(20)), None);
    assert_eq!(ff32!(-2).pow(ff32!(0.5)), ff32!(0));
    assert_eq!(ff32!(-2).checked_pow(ff32!(0.5)), None);
    assert_eq!(ff32!(0).powi(-1), FixedFloat32::MAX);
    assert_eq!(ff32!(10).checked_powi(5), None);
    assert_eq!(ff32!(-2).powi(3), ff32!(-8));
}

#[test]
fn fixed8_pow_every_pair() {
    let mut decided = 0u32;
    for a in i8::MIN..=i8::MAX {
        for b in i8::MIN..=i8::MAX {
            decided += u32::from(check_pow_pair!(FixedFloat8, 4, a, b));
        }
    }
    assert!(decided > 60_000, "decided {decided}");
}

#[test]
fn fixed8_powi_every_value() {
    for a in i8::MIN..=i8::MAX {
        for n in -200..=200 {
            let _ = check_powi!(FixedFloat8, 4, a, n);
        }
        for n in [i32::MIN, i32::MIN + 1, i32::MAX - 1, i32::MAX] {
            let _ = check_powi!(FixedFloat8, 4, a, n);
        }
    }
}

#[test]
fn fixed16_powi_every_value() {
    for a in i16::MIN..=i16::MAX {
        for n in -20..=20 {
            let _ = check_powi!(FixedFloat16, 8, a, n);
        }
    }
}

/// `x^n` of `x = a / 2^f` from the exact integer power `a^n` on `i128`,
/// rounded to nearest by its magnitude, ties up; `None` when `a^n` does not
/// fit `i128` or the result is a tie, which `pow` may round either way.
fn exact_powi(a: i128, n: u32, f: u32) -> Option<i128> {
    let mut p: i128 = 1;
    for _ in 0..n {
        p = p.checked_mul(a)?;
    }
    let s = f * (n - 1);
    if s == 0 {
        return Some(p);
    }
    let m = p.unsigned_abs();
    if s >= 128 {
        return if s == 128 && m == 1 << 127 {
            None
        } else {
            Some(0)
        };
    }
    let half = 1u128 << (s - 1);
    if m & ((half << 1) - 1) == half {
        return None;
    }
    let r = exp::round_scaled(m, i128::from(s));
    Some(if p < 0 { -(r as i128) } else { r as i128 })
}

macro_rules! powi_exact_integers {
    ($module:ident, $T:ident, $Raw:ident, $bits:tt, $f:tt) => {
        #[test]
        fn $module() {
            let mut rng = Pcg32::new(79, $bits);
            let (min, max) = (i128::from($T::MIN.to_bits()), i128::from($T::MAX.to_bits()));
            let mut compared = 0u32;
            for _ in 0..200_000 {
                let a = (rng.edge_bits($bits, $f) as $Raw) >> (rng.next_u32() % $bits);
                let n = 1 + rng.next_u32() % 12;
                if let Some(r) = exact_powi(i128::from(a), n, $f) {
                    let x = $T::from_bits(a);
                    let expected = r.clamp(min, max);
                    assert_eq!(
                        i128::from(x.powi(n as i32).to_bits()),
                        expected,
                        "{:?}^{}",
                        x,
                        n
                    );
                    compared += 1;
                }
            }
            assert!(compared > 100_000, "compared {compared}");
        }
    };
}

powi_exact_integers!(fixed16_powi_exact_integers, FixedFloat16, i16, 16, 8);
powi_exact_integers!(fixed32_powi_exact_integers, FixedFloat32, i32, 32, 16);
powi_exact_integers!(fixed64_powi_exact_integers, FixedFloat64, i64, 64, 32);

#[test]
#[ignore = "exhaustive over 2^32 pairs, minutes on every core: the weekly run"]
fn fixed16_pow_every_pair() {
    let decided = parallel_sum(i64::from(i16::MIN), i64::from(i16::MAX) + 1, |a| {
        (i16::MIN..=i16::MAX)
            .map(|b| u64::from(check_pow_pair!(FixedFloat16, 8, a as i16, b)))
            .sum()
    });
    assert!(decided > 4_000_000_000, "decided {decided}");
}

macro_rules! pow_random_pairs {
    ($module:ident, $T:ident, $Raw:ident, $bits:tt, $f:tt) => {
        #[test]
        fn $module() {
            let mut rng = Pcg32::new(73, $bits);
            for _ in 0..200_000 {
                let a = rng.edge_bits($bits, $f) as $Raw;
                let b = (rng.edge_bits($bits, $f) as $Raw) >> (rng.next_u32() % $bits);
                let _ = check_pow_pair!($T, $f, a, b);
                let n = (i64::from(b) >> (rng.next_u32() % $bits)) as i32;
                let _ = check_powi!($T, $f, a, n);
            }
        }
    };
}

pow_random_pairs!(fixed16_pow_random, FixedFloat16, i16, 16, 8);
pow_random_pairs!(fixed32_pow_random, FixedFloat32, i32, 32, 16);
