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
        "{name} {x:?} = {got}, reference {r}"
    );
    trig::correctly_rounded(r, f) == Some(got)
}

/// Checks `atan`, `asin`, `acos` and their `checked_*` of one value; returns
/// how many of the three are correctly rounded (`asin` and `acos` count as
/// rounded outside `[-1, 1]`, where they clamp).
macro_rules! check_inverse {
    ($T:ident, $f:expr, $a:expr) => {{
        let x = $T::from_bits($a);
        let a = i128::from($a);
        let mut rounded = u32::from(check(
            "atan",
            &x,
            i128::from(x.atan().to_bits()),
            trig::atan(a, $f),
            $f,
        ));
        if x != $T::MIN {
            assert_eq!((-x).atan(), -x.atan(), "atan odd {:?}", x);
        }
        let one = 1i128 << $f;
        if a.abs() <= one {
            let (s, c) = (x.asin(), x.acos());
            assert_eq!(x.checked_asin(), Some(s), "checked_asin {:?}", x);
            assert_eq!(x.checked_acos(), Some(c), "checked_acos {:?}", x);
            rounded += u32::from(check(
                "asin",
                &x,
                i128::from(s.to_bits()),
                trig::asin(a, $f),
                $f,
            ));
            rounded += u32::from(check(
                "acos",
                &x,
                i128::from(c.to_bits()),
                trig::acos(a, $f),
                $f,
            ));
            if x != $T::MIN {
                assert_eq!((-x).asin(), -s, "asin odd {:?}", x);
            }
        } else {
            let edge =
                $T::from_bits(if a < 0 { -one } else { one } as <$T as fulcrum::FixedFloat>::Bits);
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
            i128::from(t.to_bits()),
            trig::atan2(i128::from($y), i128::from($x)),
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
            rounded += u32::from(check_atan2!(FixedFloat8, 4, y, x));
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
#[ignore = "exhaustive over 2^32 values, minutes on every core: the weekly run"]
fn fixed32_all_values_correctly_rounded() {
    let rounded = parallel_sum(i64::from(i32::MIN), i64::from(i32::MAX) + 1, |a| {
        u64::from(check_inverse!(FixedFloat32, 16, a as i32))
    });
    assert_eq!(rounded, 3 << 32);
}

/// Every pair of `atan2` on `FixedFloat16`, without the reference: no panic
/// (with overflow checks, as in the weekly run) and the result in `[-π, π]`.
#[test]
#[ignore = "exhaustive over 2^32 pairs, minutes on every core: the weekly run"]
fn fixed16_all_pairs_of_atan2_in_range() {
    parallel(i64::from(i16::MIN), i64::from(i16::MAX) + 1, |y| {
        let pi = FixedFloat16::PI;
        let y = FixedFloat16::from_bits(y as i16);
        for x in i16::MIN..=i16::MAX {
            let t = y.atan2(FixedFloat16::from_bits(x));
            assert!(-pi <= t && t <= pi, "atan2 {y:?} {x}");
        }
    });
}

macro_rules! random_values {
    ($module:ident, $T:ident, $lit:ident, $Acc:ident, $Raw:ident, $bits:tt, $f:tt) => {
        #[test]
        fn $module() {
            for_random_edges!(53, 100_000, $bits, $f, |a: $Raw, b: $Raw| {
                (check_inverse!($T, $f, a), check_atan2!($T, $f, a, b))
            });
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
