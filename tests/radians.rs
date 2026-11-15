//! Sine, cosine and tangent in radians: `sin`, `cos`, `sin_cos` and `tan`
//! against the independent reference of `tests/common/trig.rs` (subtraction
//! of the nearest `k·π/2`, the full Taylor series of the remainder, no table).
//!
//! Every result is within 1 ulp of the true value (`tan` of the true value
//! saturated to the range), `sin` and `tan` are odd and `cos` even bit for
//! bit (`tan` where it does not saturate), and `sin_cos` is the pair of `sin` and `cos`. Every value of
//! `FixedFloat8` and `FixedFloat16`, and of `FixedFloat32` only with
//! `--ignored`; on these three types every result is also correctly rounded.
//! `FixedFloat64`: edge-biased random values here, where `tan` is checked
//! wherever the reference bound is narrow enough, and the rational oracle in
//! `oracle/tests/trig.rs`.

#![cfg(not(feature = "strict-overflow"))]

#[macro_use]
mod common;

use common::trig;
use common::*;
use fulcrum::*;

/// Checks one value; returns how many of its three results are correctly
/// rounded and whether the reference bound of `tan` contains a midpoint
/// (the rounding is then undecided here), or `None` for a `tan` the
/// reference cannot bound within a quarter ulp.
macro_rules! check_radians {
    ($T:ident, $bits:expr, $f:expr, $a:expr) => {{
        let x = $T::from_bits($a);
        let s = x.sin().to_bits() as i128;
        let c = x.cos().to_bits() as i128;
        let t = x.tan().to_bits() as i128;
        let (rs, rc) = (trig::sin($a as i128, $f), trig::cos($a as i128, $f));
        let e = trig::ERROR;
        assert!(trig::within_ulp(s, rs, $f), "sin {:?} = {}", x, s);
        assert!(trig::within_ulp(c, rc, $f), "cos {:?} = {}", x, c);
        assert_eq!(x.sin_cos(), (x.sin(), x.cos()), "sin_cos {:?}", x);
        assert_eq!(
            x.checked_tan().unwrap_or(x.tan()),
            x.tan(),
            "checked_tan {:?}",
            x
        );
        if x != $T::MIN {
            assert_eq!((-x).sin(), -x.sin(), "sin odd {:?}", x);
            assert_eq!((-x).cos(), x.cos(), "cos even {:?}", x);
            if x.checked_tan().is_some() {
                assert_eq!((-x).tan(), -x.tan(), "tan odd {:?}", x);
            }
        }
        let mut rounded = (trig::rounded_interval(rs - e, rs + e, $f) == Some(s)) as u32
            + (trig::rounded_interval(rc - e, rc + e, $f) == Some(c)) as u32;
        let narrow = |lo: i128, hi: i128| hi - lo < 1 << (trig::SCALE - $f - 2);
        let (min, max) = ($T::MIN.to_bits() as i128, $T::MAX.to_bits() as i128);
        let bound =
            trig::tan($a as i128, $f).map(|(lo, hi)| (lo, hi, trig::clamp(lo, hi, $bits, $f)));
        match bound {
            Some((lo, hi, (clo, chi))) if narrow(clo, chi) => {
                assert!(trig::within_ulp_of(t, clo, chi, $f), "tan {:?} = {}", x, t);
                let decided = trig::rounded_interval(clo, chi, $f);
                rounded += (decided == Some(t)) as u32;
                let fits = match trig::rounded_interval(lo, hi, $f) {
                    Some(r) if narrow(lo, hi) => Some(min <= r && r <= max),
                    _ if lo > max << (trig::SCALE - $f) || hi < min << (trig::SCALE - $f) => {
                        Some(false)
                    }
                    _ => None,
                };
                if let Some(fits) = fits {
                    assert_eq!(x.checked_tan().is_some(), fits, "checked_tan {:?}", x);
                }
                Some((rounded, decided.is_none()))
            }
            _ => None,
        }
    }};
}

macro_rules! exact_points {
    ($module:ident, $T:ident, $lit:ident, $Acc:ident, $Raw:ident, $bits:tt, $f:tt) => {
        #[test]
        fn $module() {
            let (zero, one) = ($T::ZERO, $T::ONE);
            assert_eq!(zero.sin_cos(), (zero, one));
            assert_eq!(zero.tan(), zero);
            assert_eq!(zero.checked_tan(), Some(zero));
            assert_eq!($T::FRAC_PI_2.sin(), one);
            assert_eq!($T::PI.cos(), -one);
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
        rounded += check_radians!(FixedFloat8, 8, 4, a).unwrap().0;
    }
    assert_eq!(rounded, 3 * 256);
}

#[test]
fn fixed16_all_values_correctly_rounded() {
    let mut rounded = 0;
    for a in i16::MIN..=i16::MAX {
        rounded += check_radians!(FixedFloat16, 16, 8, a).unwrap().0;
    }
    assert_eq!(rounded, 3 * 65536);
}

/// Every value of `FixedFloat32`, on every available thread. The `tan` values
/// whose reference bound contains a midpoint must be in
/// [`trig::TAN_NEAR_MIDPOINT_32`]; the oracle checks that they are
/// correctly rounded (`oracle/tests/trig.rs`).
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
                    let a = a as i32;
                    let (r, undecided) = check_radians!(FixedFloat32, 32, 16, a).unwrap();
                    if undecided {
                        assert!(
                            trig::TAN_NEAR_MIDPOINT_32.binary_search(&a).is_ok(),
                            "tan {:#x} near a midpoint",
                            a
                        );
                    }
                    rounded += (r + undecided as u32) as u64;
                }
                rounded
            })
        })
        .collect();
    let rounded: u64 = workers.into_iter().map(|w| w.join().unwrap()).sum();
    assert_eq!(rounded, 3 << 32);
}

macro_rules! random_values {
    ($module:ident, $T:ident, $lit:ident, $Acc:ident, $Raw:ident, $bits:tt, $f:tt) => {
        #[test]
        fn $module() {
            let mut rng = Pcg32::new(53, $bits);
            for _ in 0..200_000 {
                let a = rng.edge_bits($bits, $f) as $Raw;
                let _ = check_radians!($T, $bits, $f, a);
            }
        }
    };
}

mod random {
    use super::*;
    for_each_width!(random_values!());
}

fn generic_sin_cos<T: FixedFloat>(x: T) -> (T, T) {
    x.sin_cos()
}

#[test]
fn trait_sin_cos() {
    for x in [ff32!(0.5), ff32!(-3), FixedFloat32::MAX] {
        assert_eq!(generic_sin_cos(x), (x.sin(), x.cos()));
    }
    let x = ff64!(1000000000);
    assert_eq!(generic_sin_cos(x), x.sin_cos());
}
