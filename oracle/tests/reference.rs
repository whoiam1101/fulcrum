//! The integer reference `tests/common/reference.rs` against exact rationals:
//! the oracle checks the reference, the reference checks the library. Inputs
//! stay inside the domain each reference function states.

#[macro_use]
#[path = "../../tests/common/reference.rs"]
mod reference;

reference!(spec, i128);

use fulcrum_oracle::Format;
use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, ToPrimitive};
use proptest::prelude::*;

/// Integers of `i128`: the format of the arguments of `spec`.
const INT: Format = Format { bits: 128, frac: 0 };

fn round(x: BigRational) -> i128 {
    INT.round(&x).to_i128().expect("fits i128")
}

fn ratio(n: i128, d: i128) -> BigRational {
    BigRational::new(BigInt::from(n), BigInt::from(d))
}

fn scaled(n: i128, f: u32) -> BigRational {
    Format { frac: f, ..INT }.exact(n)
}

fn round_sqrt(num: i128, den: i128) -> i128 {
    INT.round_sqrt(&ratio(num, den))
        .to_i128()
        .expect("fits i128")
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
    fn sqrt_ratio(num in prop_oneof![1 => 0i128..=64, 4 => 0i128..=1 << 98], den in prop_oneof![1 => 1i128..=8, 4 => 1i128..=i64::MAX as i128]) {
        prop_assume!((num as u128) < 1u128 << 98);
        let s = spec::sqrt_ratio(num, den);
        prop_assert_eq!(s, round_sqrt(num, den));
        prop_assert!(spec::is_sqrt_ratio(s, num, den));
        prop_assert!(!spec::is_sqrt_ratio(s + 1, num, den));
        prop_assert!(s == 0 || !spec::is_sqrt_ratio(s - 1, num, den));
    }

    #[test]
    fn range(v in any::<i128>(), bits in 2u32..=127) {
        let fmt = Format { bits, ..INT };
        let (min, max) = (fmt.min(), fmt.max());
        let big = BigInt::from(v);
        prop_assert_eq!(spec::saturate(v, bits), fmt.saturate(big.clone()));
        prop_assert_eq!(spec::fits(v, bits), fmt.fits(&big));
        let modulus = BigInt::one() << bits;
        let low = (big - &min).mod_floor(&modulus) + &min;
        prop_assert_eq!(spec::wrap(v, bits), low.to_i128().unwrap());
        let expected = match v.signum() { 1 => max, -1 => min, _ => BigInt::from(0) };
        prop_assert_eq!(spec::div_by_zero(v, bits), expected.to_i128().unwrap());
    }
}
