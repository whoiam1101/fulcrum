//! Every constant of every type is within half an ulp of the true value,
//! checked against published decimal expansions (40 digits, independent of
//! the series used by `tools/gen-tables`).

#[macro_use]
#[path = "../../tests/common/widths.rs"]
mod widths;

use fulcrum::*;
use fulcrum_oracle::Format;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::Signed;

const PI: &str = "3.1415926535897932384626433832795028841971";
const E: &str = "2.7182818284590452353602874713526624977572";
const SQRT_2: &str = "1.4142135623730950488016887242096980785696";
const SQRT_3: &str = "1.7320508075688772935274463415058723669428";
const SQRT_5: &str = "2.2360679774997896964091736687312762354406";
const LN_2: &str = "0.6931471805599453094172321214581765680755";
const LN_10: &str = "2.3025850929940456840179914546843642076011";

fn d(s: &str) -> BigRational {
    Format::decimal(s)
}

fn int(n: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(n))
}

fn truth(name: &str) -> BigRational {
    let pi = d(PI);
    let ln2 = d(LN_2);
    let ln10 = d(LN_10);
    match name {
        "PI" => pi,
        "TAU" => pi * int(2),
        "FRAC_PI_2" => pi / int(2),
        "FRAC_PI_3" => pi / int(3),
        "FRAC_PI_4" => pi / int(4),
        "FRAC_PI_6" => pi / int(6),
        "FRAC_PI_8" => pi / int(8),
        "FRAC_1_PI" => int(1) / pi,
        "FRAC_2_PI" => int(2) / pi,
        "DEG_TO_RAD" => pi / int(180),
        "RAD_TO_DEG" => int(180) / pi,
        "SQRT_2" => d(SQRT_2),
        "FRAC_1_SQRT_2" => d(SQRT_2) / int(2),
        "SQRT_3" => d(SQRT_3),
        "FRAC_1_SQRT_3" => d(SQRT_3) / int(3),
        "E" => d(E),
        "LN_2" => ln2,
        "LN_10" => ln10,
        "LOG2_E" => int(1) / ln2,
        "LOG2_10" => ln10 / ln2,
        "LOG10_2" => ln2 / ln10,
        "LOG10_E" => int(1) / ln10,
        "GOLDEN_RATIO" => (int(1) + d(SQRT_5)) / int(2),
        other => panic!("unknown constant {}", other),
    }
}

/// Asserts that every named constant of `$T` is within half an ulp of the truth.
macro_rules! check {
    ($T:ident, $bits:tt, $frac:tt; $($name:ident),*) => {
        $(
            let fmt = Format { bits: $bits, frac: $frac };
            let err = (fmt.exact($T::$name.to_bits() as i128) - truth(stringify!($name))).abs();
            let half_ulp = BigRational::new(BigInt::from(1), BigInt::from(1) << ($frac + 1));
            assert!(err < half_ulp, "{}::{} is not correctly rounded", stringify!($T), stringify!($name));
        )*
    };
}

/// [`check!`] with every constant that the type has: `FixedFloat8` has no
/// `DEG_TO_RAD` (it rounds to zero) and no `RAD_TO_DEG` (out of range).
macro_rules! check_width {
    (fixed8, $T:ident, $lit:ident, $Acc:ident, $Raw:ident, $bits:tt, $frac:tt) => {
        check!($T, $bits, $frac; PI, TAU, FRAC_PI_2, FRAC_PI_3, FRAC_PI_4, FRAC_PI_6, FRAC_PI_8,
            FRAC_1_PI, FRAC_2_PI, SQRT_2, FRAC_1_SQRT_2, SQRT_3, FRAC_1_SQRT_3,
            E, LN_2, LN_10, LOG2_E, LOG2_10, LOG10_2, LOG10_E, GOLDEN_RATIO);
    };
    ($module:ident, $T:ident, $lit:ident, $Acc:ident, $Raw:ident, $bits:tt, $frac:tt) => {
        check!($T, $bits, $frac; PI, TAU, FRAC_PI_2, FRAC_PI_3, FRAC_PI_4, FRAC_PI_6, FRAC_PI_8,
            FRAC_1_PI, FRAC_2_PI, DEG_TO_RAD, RAD_TO_DEG, SQRT_2, FRAC_1_SQRT_2, SQRT_3,
            FRAC_1_SQRT_3, E, LN_2, LN_10, LOG2_E, LOG2_10, LOG10_2, LOG10_E, GOLDEN_RATIO);
    };
}

#[test]
fn constants_are_correctly_rounded() {
    for_each_width!(check_width!());
}
