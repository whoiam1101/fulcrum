//! The integer reference `tests/common/reference.rs` against exact rationals:
//! the oracle checks the reference, the reference checks the library. Inputs
//! stay inside the domain each reference function states.

#[macro_use]
#[path = "../../tests/common/reference.rs"]
mod reference;

reference!(spec, i128);

use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, ToPrimitive};
use proptest::prelude::*;

fn round(x: BigRational) -> i128 {
    let shifted = x + BigRational::new(BigInt::one(), BigInt::from(2));
    shifted
        .numer()
        .div_floor(shifted.denom())
        .to_i128()
        .expect("fits i128")
}

fn ratio(n: i128, d: i128) -> BigRational {
    BigRational::new(BigInt::from(n), BigInt::from(d))
}

fn scaled(n: i128, f: u32) -> BigRational {
    BigRational::new(BigInt::from(n), BigInt::one() << f)
}

fn raw() -> impl Strategy<Value = i128> {
    prop_oneof![
        1 => Just(i64::MIN as i128),
        1 => Just(i64::MAX as i128),
        1 => -4i128..=4,
        4 => any::<i64>().prop_map(|v| v as i128),
    ]
}

fn shift() -> impl Strategy<Value = u32> {
    prop_oneof![1 => Just(0u32), 1 => Just(1u32), 4 => 0u32..=32]
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(20_000))]

    #[test]
    fn round_div(n in any::<i128>().prop_filter("n > MIN", |&n| n > i128::MIN), d in any::<i128>()) {
        let d = d >> 2;
        prop_assume!(d != 0);
        prop_assert_eq!(spec::round_div(n, d), round(ratio(n, d)));
    }

    #[test]
    fn round_shift(n in any::<i128>(), f in 0u32..=126) {
        prop_assert_eq!(spec::round_shift(n, f), round(scaled(n, f)));
    }

    #[test]
    fn rescale(n in raw(), src in 0u32..=96, dst in 0u32..=32) {
        let exact = scaled(n, src) * BigRational::from_integer(BigInt::one() << dst);
        let expected = if src >= dst { Some(round(exact)) } else { exact.to_integer().to_i128() };
        prop_assert_eq!(spec::rescale(n, src, dst), expected);
    }

    #[test]
    fn operations(a in raw(), b in raw(), c in raw(), f in shift()) {
        let (x, y, z) = (scaled(a, f), scaled(b, f), scaled(c, f));
        let unit = BigRational::from_integer(BigInt::one() << f);
        prop_assert_eq!(spec::mul(a, b, f), round(&x * &y * &unit));
        prop_assert_eq!(spec::mul_add(a, b, c, f), round((&x * &y + &z) * &unit));
        prop_assert_eq!(spec::lerp(a, b, c, f), round((&x + (&y - &x) * &z) * &unit));
        if b != 0 {
            prop_assert_eq!(spec::div(a, b, f), round(&x / &y * &unit));
        }
        if c != 0 {
            prop_assert_eq!(spec::mul_div(a, b, c), round(&x * &y / &z * &unit));
        }
    }

    #[test]
    fn range(v in any::<i128>(), bits in 2u32..=127) {
        let min = -(BigInt::one() << (bits - 1));
        let max = (BigInt::one() << (bits - 1)) - 1;
        let big = BigInt::from(v);
        let clamped = if big < min { min.clone() } else if big > max { max.clone() } else { big.clone() };
        prop_assert_eq!(spec::saturate(v, bits), clamped.to_i128().unwrap());
        prop_assert_eq!(spec::fits(v, bits), big >= min && big <= max);
        let modulus = BigInt::one() << bits;
        let low = (big - &min).mod_floor(&modulus) + &min;
        prop_assert_eq!(spec::wrap(v, bits), low.to_i128().unwrap());
        let expected = match v.signum() { 1 => max, -1 => min, _ => BigInt::from(0) };
        prop_assert_eq!(spec::div_by_zero(v, bits), expected.to_i128().unwrap());
    }
}
