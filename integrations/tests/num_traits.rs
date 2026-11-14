//! `num-traits`: `Zero`, `One`, `Bounded`, `Num`, `Signed` agree with the
//! inherent constants and the saturating operators, also in generic code.

#![cfg(feature = "num-traits")]

use fulcrum::{ff16, ff8, FixedFloat16, FixedFloat32, FixedFloat64, FixedFloat8, ParseErrorKind};
use num_traits::{Bounded, Num, One, Signed, Zero};

fn sum_of_squares<T: Num + Copy>(xs: &[T]) -> T {
    xs.iter().fold(T::zero(), |s, &x| s + x * x)
}

#[test]
fn identities_and_bounds() {
    assert_eq!(FixedFloat8::zero(), FixedFloat8::ZERO);
    assert!(FixedFloat8::zero().is_zero());
    assert!(!FixedFloat8::DELTA.is_zero());
    assert_eq!(FixedFloat16::one(), FixedFloat16::ONE);
    assert!(FixedFloat16::one().is_one());
    assert_eq!(FixedFloat32::min_value(), FixedFloat32::MIN);
    assert_eq!(FixedFloat64::max_value(), FixedFloat64::MAX);
}

#[test]
fn generic_code_uses_the_operators() {
    assert_eq!(sum_of_squares(&[ff16!(1.5), ff16!(-2)]), ff16!(6.25));
    assert_eq!(sum_of_squares(&[ff8!(3), ff8!(-3)]), FixedFloat8::MAX);
}

#[test]
fn from_str_radix_accepts_only_decimal() {
    assert_eq!(FixedFloat16::from_str_radix("-1.25", 10), Ok(ff16!(-1.25)));
    assert_eq!(
        FixedFloat16::from_str_radix("1000", 10).map_err(|e| e.kind()),
        Err(ParseErrorKind::Overflow)
    );
    assert_eq!(
        FixedFloat16::from_str_radix("10", 16).map_err(|e| e.kind()),
        Err(ParseErrorKind::InvalidDigit)
    );
}

#[test]
fn signed_matches_the_inherent_methods() {
    for raw in i8::MIN..=i8::MAX {
        let x = FixedFloat8::from_bits(raw);
        assert_eq!(Signed::abs(&x), x.abs());
        assert_eq!(Signed::signum(&x), x.signum());
        assert_eq!(Signed::is_positive(&x), raw > 0);
        assert_eq!(Signed::is_negative(&x), raw < 0);
        for other in [i8::MIN, -16, -1, 0, 1, 16, i8::MAX] {
            let y = FixedFloat8::from_bits(other);
            let expected = (raw as i32 - other as i32).clamp(0, i8::MAX as i32);
            assert_eq!(
                x.abs_sub(&y).to_bits() as i32,
                expected,
                "{} {}",
                raw,
                other
            );
        }
    }
}
