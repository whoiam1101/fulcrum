//! Sine and cosine in turns: `sin_turns` and `cos_turns` against the
//! independent reference of `tests/common/trig.rs` (octant symmetry and the
//! full Taylor series, no table).
//!
//! Every result is within 1 ulp of the true value, odd or even as the
//! function is, periodic with period 1, and `cos_turns(x) = sin_turns(x + ¼)`.
//! Every value of `FixedFloat8` and `FixedFloat16`, and of `FixedFloat32` only
//! with `--ignored`; on these three types every result is also correctly
//! rounded.
//! `FixedFloat64`: edge-biased random values here and the rational oracle in
//! `oracle/tests/trig.rs`.

#![cfg(not(feature = "strict-overflow"))]

#[macro_use]
mod common;

use common::trig;
use common::*;
use fulcrum::*;

/// Checks one value; returns how many of its two results are correctly
/// rounded.
macro_rules! check_trig {
    ($T:ident, $f:expr, $a:expr) => {{
        let x = $T::from_bits($a);
        let s = i128::from(x.sin_turns().to_bits());
        let c = i128::from(x.cos_turns().to_bits());
        let rs = trig::sin_turns(i128::from($a), $f);
        let rc = trig::cos_turns(i128::from($a), $f);
        assert!(trig::within_ulp(s, rs, $f), "sin_turns {:?} = {}", x, s);
        assert!(trig::within_ulp(c, rc, $f), "cos_turns {:?} = {}", x, c);
        if x != $T::MIN {
            assert_eq!((-x).sin_turns(), -x.sin_turns(), "odd {:?}", x);
            assert_eq!((-x).cos_turns(), x.cos_turns(), "even {:?}", x);
        }
        let quarter = $T::from_bits(1 << ($f - 2));
        assert_eq!(
            x.wrapping_add(quarter).sin_turns(),
            x.cos_turns(),
            "shift {:?}",
            x
        );
        assert_eq!(
            x.wrapping_add($T::ONE).sin_turns(),
            x.sin_turns(),
            "period {:?}",
            x
        );
        let rounded = |got: i128, r: i128| trig::correctly_rounded(r, $f) == Some(got);
        u32::from(rounded(s, rs)) + u32::from(rounded(c, rc))
    }};
}

macro_rules! exact_points {
    ($module:ident, $T:ident, $lit:ident, $Acc:ident, $Raw:ident, $bits:tt, $f:tt) => {
        #[test]
        fn $module() {
            let q = |k: $Raw| $T::from_bits(k << ($f - 2));
            let (zero, one) = ($T::ZERO, $T::ONE);
            for (k, sin, cos) in [
                (0, zero, one),
                (1, one, zero),
                (2, zero, -one),
                (3, -one, zero),
            ] {
                assert_eq!(q(k).sin_turns(), sin, "sin_turns {}/4", k);
                assert_eq!(q(k).cos_turns(), cos, "cos_turns {}/4", k);
                assert_eq!((-q(k)).sin_turns(), -sin, "sin_turns -{}/4", k);
            }
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
        rounded += check_trig!(FixedFloat8, 4, a);
    }
    assert_eq!(rounded, 2 * 256);
}

#[test]
fn fixed16_all_values_correctly_rounded() {
    let mut rounded = 0;
    for a in i16::MIN..=i16::MAX {
        rounded += check_trig!(FixedFloat16, 8, a);
    }
    assert_eq!(rounded, 2 * 65536);
}

/// Every value of `FixedFloat32`, on every available thread.
#[test]
#[ignore = "exhaustive over 2^32 values, minutes on every core: the weekly run"]
fn fixed32_all_values_correctly_rounded() {
    let threads =
        std::thread::available_parallelism().map_or(1, std::num::NonZeroUsize::get) as i64;
    let span = (1i64 << 32) / threads + 1;
    let workers: Vec<_> = (0..threads)
        .map(|k| {
            std::thread::spawn(move || {
                let start = i64::from(i32::MIN) + k * span;
                let end = (start + span).min(i64::from(i32::MAX) + 1);
                let mut rounded = 0u64;
                for a in start..end {
                    rounded += u64::from(check_trig!(FixedFloat32, 16, a as i32));
                }
                rounded
            })
        })
        .collect();
    let rounded: u64 = workers.into_iter().map(|w| w.join().unwrap()).sum();
    assert_eq!(rounded, 2 << 32);
}

macro_rules! random_values {
    ($module:ident, $T:ident, $lit:ident, $Acc:ident, $Raw:ident, $bits:tt, $f:tt) => {
        #[test]
        fn $module() {
            let mut rng = Pcg32::new(47, $bits);
            for _ in 0..200_000 {
                let a = rng.edge_bits($bits, $f) as $Raw;
                let _ = check_trig!($T, $f, a);
            }
        }
    };
}

mod random {
    use super::*;
    for_each_width!(random_values!());
}
