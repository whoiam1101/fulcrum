//! Mathematical constants: plausibility, relations between them and
//! consistency across widths. Exactness against published digits is checked
//! in `oracle/tests/consts.rs`.

#[macro_use]
mod common;

use core::convert::TryFrom;
use fulcrum::*;

/// The widest type: every narrower constant is its constant, rounded.
type Widest = FixedFloat64;

fn ulps(a: FixedFloat64, b: FixedFloat64) -> i64 {
    (a.to_bits() - b.to_bits()).abs()
}

#[test]
fn decimal_prefixes() {
    let cases = [
        (FixedFloat64::PI, "3.14159265"),
        (FixedFloat64::TAU, "6.28318530"),
        (FixedFloat64::E, "2.71828182"),
        (FixedFloat64::SQRT_2, "1.41421356"),
        (FixedFloat64::SQRT_3, "1.73205080"),
        (FixedFloat64::LN_2, "0.69314718"),
        (FixedFloat64::LN_10, "2.30258509"),
        (FixedFloat64::LOG2_E, "1.44269504"),
        (FixedFloat64::LOG2_10, "3.32192809"),
        (FixedFloat64::LOG10_2, "0.30102999"),
        (FixedFloat64::LOG10_E, "0.43429448"),
        (FixedFloat64::GOLDEN_RATIO, "1.61803398"),
        (FixedFloat64::RAD_TO_DEG, "57.2957795"),
        (FixedFloat64::DEG_TO_RAD, "0.01745329"),
        (FixedFloat64::FRAC_1_PI, "0.31830988"),
    ];
    for (c, prefix) in cases {
        assert!(c.to_string().starts_with(prefix), "{} vs {}", c, prefix);
    }
}

#[test]
fn relations_hold_within_one_ulp() {
    type F = FixedFloat64;
    assert!(ulps(F::TAU, F::PI.mul_int(2)) <= 1);
    assert!(ulps(F::FRAC_PI_2.mul_int(2), F::PI) <= 2);
    assert!(ulps(F::FRAC_PI_4.mul_int(4), F::PI) <= 4);
    assert!(ulps(F::FRAC_1_SQRT_2.mul_int(2), F::SQRT_2) <= 2);
    assert!(ulps(F::SQRT_2 * F::SQRT_2, F::from(2i8)) <= 2);
    assert!(ulps(F::SQRT_3 * F::FRAC_1_SQRT_3, F::ONE) <= 2);
    assert!(ulps(F::DEG_TO_RAD.mul_int(180), F::PI) <= 180);
    assert!(ulps(F::LN_2 * F::LOG2_E, F::ONE) <= 2);
    assert!(ulps(F::LOG2_10 * F::LOG10_2, F::ONE) <= 4);
    assert!(ulps(F::GOLDEN_RATIO * F::GOLDEN_RATIO, F::GOLDEN_RATIO + F::ONE) <= 4);
}

macro_rules! same_as_narrowed {
    ($Small:ident: $($name:ident),*) => {
        $(
            assert_eq!(
                $Small::try_from(Widest::$name).ok(),
                Some($Small::$name),
                "{} of {}",
                stringify!($name),
                stringify!($Small)
            );
        )*
    };
}

/// Calls `$m!($T: names)` with every constant that `$T` has: `FixedFloat8`
/// has no `DEG_TO_RAD` (it rounds to zero) and no `RAD_TO_DEG` (out of range).
macro_rules! with_constants {
    ($m:ident, fixed8, $T:ident, $($rest:tt)*) => {
        $m!($T: PI, TAU, FRAC_PI_2, FRAC_PI_3, FRAC_PI_4, FRAC_PI_6, FRAC_PI_8,
            FRAC_1_PI, FRAC_2_PI, SQRT_2, FRAC_1_SQRT_2, SQRT_3, FRAC_1_SQRT_3,
            E, LN_2, LN_10, LOG2_E, LOG2_10, LOG10_2, LOG10_E, GOLDEN_RATIO)
    };
    ($m:ident, $module:ident, $T:ident, $($rest:tt)*) => {
        $m!($T: PI, TAU, FRAC_PI_2, FRAC_PI_3, FRAC_PI_4, FRAC_PI_6, FRAC_PI_8,
            FRAC_1_PI, FRAC_2_PI, DEG_TO_RAD, RAD_TO_DEG, SQRT_2, FRAC_1_SQRT_2, SQRT_3,
            FRAC_1_SQRT_3, E, LN_2, LN_10, LOG2_E, LOG2_10, LOG10_2, LOG10_E, GOLDEN_RATIO)
    };
}

#[test]
fn narrower_types_agree_with_rounded_wider_values() {
    for_each_width!(with_constants!(same_as_narrowed,));
}

#[test]
fn trait_constants_match_inherent_ones() {
    fn pi<T: FixedFloat>() -> T {
        T::PI
    }
    assert_eq!(pi::<FixedFloat8>(), FixedFloat8::PI);
    assert_eq!(pi::<FixedFloat64>(), FixedFloat64::PI);
    assert_eq!(<FixedFloat32 as FixedFloat>::E, FixedFloat32::E);
}
