//! Property tests: every operation equals the exact rational oracle bit for bit.

use fulcrum::{FixedFloat16, FixedFloat32, FixedFloat64, FixedFloat8};
use fulcrum_oracle::Format;
use num_bigint::BigInt;
use num_rational::BigRational;
use proptest::prelude::*;

fn edge(bits: u32, frac: u32) -> impl Strategy<Value = i128> {
    let min = -(1i128 << (bits - 1));
    let max = (1i128 << (bits - 1)) - 1;
    let one = 1i128 << frac;
    let full = (min..=max).boxed();
    prop_oneof![
        1 => Just(0i128),
        1 => Just(1i128),
        1 => Just(-1i128),
        1 => Just(one),
        1 => Just(-one),
        1 => Just(one / 2),
        1 => Just(min),
        1 => Just(max),
        1 => Just(min + 1),
        1 => Just(max - 1),
        2 => (0..bits - 1, any::<bool>()).prop_map(|(k, n)| if n { -(1i128 << k) } else { 1i128 << k }),
        2 => -4 * one..=4 * one,
        8 => full,
    ]
}

fn decimal_text() -> impl Strategy<Value = String> {
    (
        any::<bool>(),
        "[0-9]{0,12}",
        proptest::option::of("[0-9]{0,80}"),
    )
        .prop_filter_map("needs a digit", |(neg, int, frac)| {
            let frac_text = frac.clone().unwrap_or_default();
            if int.is_empty() && frac_text.is_empty() {
                return None;
            }
            let sign = if neg { "-" } else { "" };
            Some(match frac {
                Some(f) => format!("{}{}.{}", sign, int, f),
                None => format!("{}{}", sign, int),
            })
        })
}

macro_rules! oracle_suite {
    ($module:ident, $T:ident, $Bits:ty, $bits:expr, $frac:expr) => {
        mod $module {
            use super::*;

            const FMT: Format = Format { bits: $bits, frac: $frac };

            fn v(raw: i128) -> $T {
                $T::from_bits(raw as $Bits)
            }

            proptest! {
                #![proptest_config(ProptestConfig { cases: 20_000, ..ProptestConfig::default() })]

                #[test]
                fn add_sub(a in edge($bits, $frac), b in edge($bits, $frac)) {
                    let sum = BigInt::from(a) + BigInt::from(b);
                    prop_assert_eq!((v(a) + v(b)).to_bits() as i128, FMT.saturate(sum.clone()));
                    prop_assert_eq!(v(a).checked_add(v(b)).is_some(), FMT.fits(&sum));
                    let diff = BigInt::from(a) - BigInt::from(b);
                    prop_assert_eq!((v(a) - v(b)).to_bits() as i128, FMT.saturate(diff.clone()));
                    prop_assert_eq!(v(a).checked_sub(v(b)).is_some(), FMT.fits(&diff));
                }

                #[test]
                fn mul(a in edge($bits, $frac), b in edge($bits, $frac)) {
                    let (expected, fits) = FMT.mul(a, b);
                    prop_assert_eq!((v(a) * v(b)).to_bits() as i128, expected);
                    prop_assert_eq!(v(a).checked_mul(v(b)).is_some(), fits);
                    prop_assert_eq!(v(a).overflowing_mul(v(b)).1, !fits);
                }

                #[test]
                fn div(a in edge($bits, $frac), b in edge($bits, $frac)) {
                    let (expected, fits) = FMT.div(a, b);
                    prop_assert_eq!((v(a) / v(b)).to_bits() as i128, expected);
                    prop_assert_eq!(v(a).checked_div(v(b)).is_some(), fits && b != 0);
                    let rem = BigRational::from_integer(BigInt::from(a)) - BigRational::from_integer(BigInt::from(b)) * if b == 0 { BigRational::from_integer(BigInt::from(0)) } else { (FMT.exact(a) / FMT.exact(b)).trunc() };
                    if b != 0 {
                        prop_assert_eq!(BigRational::from_integer(BigInt::from((v(a) % v(b)).to_bits() as i128)), rem);
                    }
                }

                #[test]
                fn ratio(num in edge($bits, $frac), den in edge($bits, $frac)) {
                    prop_assert_eq!($T::checked_from_ratio(num as $Bits, den as $Bits).map(|x| x.to_bits() as i128), FMT.ratio(num, den));
                }

                #[test]
                fn display_is_exact_and_round_trips(a in edge($bits, $frac)) {
                    let text = v(a).to_string();
                    prop_assert!(FMT.displays_exactly(a, &text), "{} is not exact", text);
                    prop_assert_eq!(text.parse::<$T>(), Ok(v(a)));
                }

                #[test]
                fn display_precision_is_correctly_rounded(a in edge($bits, $frac), p in 0u32..40) {
                    let text = format!("{:.*}", p as usize, v(a));
                    let frac_len = text.split_once('.').map_or(0, |(_, f)| f.len());
                    prop_assert_eq!(frac_len, p as usize);
                    let err = FMT.display_error_doubled(a, &text, p);
                    prop_assert!(err <= BigRational::from_integer(BigInt::from(1)), "{} err {}", text, err);
                }

                #[test]
                fn parse_matches_oracle(text in decimal_text()) {
                    let got = text.parse::<$T>().ok().map(|x| x.to_bits() as i128);
                    prop_assert_eq!(got, FMT.parse(&text), "{}", text);
                }
            }
        }
    };
}

oracle_suite!(fixed8, FixedFloat8, i8, 8, 4);
oracle_suite!(fixed16, FixedFloat16, i16, 16, 8);
oracle_suite!(fixed32, FixedFloat32, i32, 32, 16);
oracle_suite!(fixed64, FixedFloat64, i64, 64, 32);
