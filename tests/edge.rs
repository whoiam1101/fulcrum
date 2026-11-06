//! Edge cases on every width: parts of negative numbers, `-MIN`, `MIN / -1`,
//! division by zero, conversions, literals, formatting flags, byte layout.

#![cfg(not(feature = "strict-overflow"))]

mod common;

use core::convert::TryFrom;
use fulcrum::{
    ff16, ff32, ff64, ff8, FixedFloat, FixedFloat16, FixedFloat32, FixedFloat64, FixedFloat8,
    OverflowError, ParseErrorKind,
};

macro_rules! edge_suite {
    ($module:ident, $T:ident, $lit:ident) => {
        mod $module {
            use super::*;

            #[test]
            fn constants() {
                assert_eq!($T::ZERO.to_bits(), 0);
                assert_eq!($T::ONE.to_bits(), 1 << $T::FRAC_BITS);
                assert_eq!($T::NEG_ONE, -$T::ONE);
                assert_eq!($T::HALF + $T::HALF, $T::ONE);
                assert_eq!($T::DELTA.to_bits(), 1);
                assert_eq!(
                    $T::INT_BITS + $T::FRAC_BITS,
                    8 * core::mem::size_of::<$T>() as u32
                );
                assert_eq!(<$T as FixedFloat>::MAX, $T::MAX);
                assert_eq!($T::default(), $T::ZERO);
            }

            #[test]
            fn parts_of_negative_numbers() {
                let x = $lit!(-1.25);
                assert_eq!(x.int_part(), -2);
                assert_eq!(x.frac_part() as i128, 3i128 << ($T::FRAC_BITS - 2));
                assert_eq!($T::from_parts(-2, x.frac_part()), x);
                assert_eq!($T::MIN.int_part() as i128, -(1i128 << ($T::INT_BITS - 1)));
                assert_eq!($T::MAX.frac_part() as i128, (1i128 << $T::FRAC_BITS) - 1);
            }

            #[test]
            fn saturation_never_panics() {
                assert_eq!($T::MAX + $T::DELTA, $T::MAX);
                assert_eq!($T::MIN - $T::DELTA, $T::MIN);
                assert_eq!(-$T::MIN, $T::MAX);
                assert_eq!($T::MIN.abs(), $T::MAX);
                assert_eq!($T::MIN.wrapping_neg(), $T::MIN);
                assert_eq!($T::MIN.checked_neg(), None);
                assert_eq!($T::MAX * $T::MAX, $T::MAX);
                assert_eq!($T::MIN * $T::MAX, $T::MIN);
                assert_eq!($T::MIN / $T::NEG_ONE, $T::MAX);
                assert_eq!($T::MIN.checked_div($T::NEG_ONE), None);
                assert_eq!($T::MIN.div_int(-1), $T::MAX);
                assert_eq!($T::MIN % $T::NEG_ONE, $T::ZERO);
                assert_eq!($T::MIN % -$T::DELTA, $T::ZERO);
                assert_eq!($T::MAX.mul_int(2), $T::MAX);
                assert_eq!($T::MAX.ceil(), $T::MAX);
                assert_eq!($T::MAX.checked_ceil(), None);
                assert_eq!($T::MAX.round(), $T::MAX);
                assert_eq!($T::MIN.floor(), $T::MIN);
                assert_eq!($T::MIN.round(), $T::MIN);
                assert_eq!($T::MAX.abs_diff($T::MIN), $T::MAX);
                assert_eq!($T::MAX.midpoint($T::MAX), $T::MAX);
                assert_eq!($T::MIN.midpoint($T::MIN), $T::MIN);
                assert_eq!($T::MAX.midpoint($T::MIN), $T::ZERO);
            }

            #[test]
            fn division_by_zero() {
                let z = $T::ZERO;
                assert_eq!($T::ONE / z, $T::MAX);
                assert_eq!($T::NEG_ONE / z, $T::MIN);
                assert_eq!(z / z, $T::ZERO);
                assert_eq!($T::ONE.checked_div(z), None);
                assert_eq!($T::ONE.overflowing_div(z), ($T::MAX, true));
                assert_eq!($T::ONE % z, $T::ZERO);
                assert_eq!($T::ONE.checked_rem(z), None);
                assert_eq!($T::ONE.div_int(0), $T::MAX);
                assert_eq!($T::ONE.checked_div_int(0), None);
                assert_eq!(z.recip(), $T::MAX);
                assert_eq!($T::saturating_from_ratio(-1, 0), $T::MIN);
                assert_eq!($T::checked_from_ratio(1, 0), None);
            }

            #[test]
            fn rounding_ties_toward_positive_infinity() {
                let h = $T::from_bits(1);
                let half = $T::HALF;
                assert_eq!(h * half, $T::from_bits(1));
                assert_eq!((-h) * half, $T::ZERO);
                assert_eq!(h.div_int(2), $T::from_bits(1));
                assert_eq!((-h).div_int(2), $T::ZERO);
                assert_eq!($T::saturating_from_ratio(1, 2), $T::HALF);
                assert_eq!($T::saturating_from_ratio(-3, 4), -$T::HALF - $lit!(0.25));
            }

            #[test]
            fn rounding_functions() {
                assert_eq!($lit!(2.5).round(), $lit!(3));
                assert_eq!($lit!(-2.5).round(), $lit!(-3));
                assert_eq!($lit!(2.5).round_ties_even(), $lit!(2));
                assert_eq!($lit!(3.5).round_ties_even(), $lit!(4));
                assert_eq!($lit!(-2.5).round_ties_even(), $lit!(-2));
                assert_eq!($lit!(-1.25).floor(), $lit!(-2));
                assert_eq!($lit!(-1.25).ceil(), $lit!(-1));
                assert_eq!($lit!(-1.25).trunc(), $lit!(-1));
                assert_eq!($lit!(-1.25).fract(), $lit!(-0.25));
                assert_eq!($lit!(-1.25).to_int_floor(), -2);
                assert_eq!($lit!(-1.25).to_int_trunc(), -1);
                assert_eq!($T::MAX.to_int_ceil() as i128, 1i128 << ($T::INT_BITS - 1));
            }

            #[test]
            fn integers() {
                assert_eq!($T::saturating_from_int(i128::MAX), $T::MAX);
                assert_eq!($T::saturating_from_int(i128::MIN), $T::MIN);
                assert_eq!($T::checked_from_int(1i128 << ($T::INT_BITS - 1)), None);
                assert_eq!(
                    $T::checked_from_int(-(1i128 << ($T::INT_BITS - 1))),
                    Some($T::MIN)
                );
                assert_eq!($T::checked_from_int(3), Some($lit!(3)));
                assert_eq!(
                    $T::checked_from_parts(<$T>::MAX.int_part(), <$T>::MAX.frac_part()),
                    Some($T::MAX)
                );
            }

            #[test]
            fn literals_and_parsing() {
                assert_eq!($lit!(0.2_5), $lit!(0.25));
                assert_eq!($lit!(-0.0), $T::ZERO);
                assert_eq!($lit!(-7), -$lit!(7));
                assert_eq!("+1.5".parse::<$T>(), Ok($lit!(1.5)));
                assert_eq!(".5".parse::<$T>(), Ok($T::HALF));
                assert_eq!("5.".parse::<$T>(), Ok($lit!(5)));
                assert_eq!("".parse::<$T>().unwrap_err().kind(), ParseErrorKind::Empty);
                assert_eq!("-".parse::<$T>().unwrap_err().kind(), ParseErrorKind::Empty);
                assert_eq!(
                    ".".parse::<$T>().unwrap_err().kind(),
                    ParseErrorKind::InvalidDigit
                );
                assert_eq!(
                    "1e3".parse::<$T>().unwrap_err().kind(),
                    ParseErrorKind::InvalidDigit
                );
                assert_eq!(
                    "1_0".parse::<$T>().unwrap_err().kind(),
                    ParseErrorKind::InvalidDigit
                );
                assert_eq!(
                    "--1".parse::<$T>().unwrap_err().kind(),
                    ParseErrorKind::InvalidDigit
                );
                assert_eq!(
                    " 1".parse::<$T>().unwrap_err().kind(),
                    ParseErrorKind::InvalidDigit
                );
                assert_eq!(
                    "99999999999999999999999999"
                        .parse::<$T>()
                        .unwrap_err()
                        .kind(),
                    ParseErrorKind::Overflow
                );
                let min = $T::MIN.to_string();
                assert_eq!(min.parse::<$T>(), Ok($T::MIN));
                let max = $T::MAX.to_string();
                assert_eq!(max.parse::<$T>(), Ok($T::MAX));
            }

            #[test]
            fn formatting_flags() {
                let x = $lit!(-1.5);
                assert_eq!(format!("{}", x), "-1.5");
                assert_eq!(format!("{:8}", x), "    -1.5");
                assert_eq!(format!("{:<8}|", x), "-1.5    |");
                assert_eq!(format!("{:^8}|", x), "  -1.5  |");
                assert_eq!(format!("{:*>8}", x), "****-1.5");
                assert_eq!(format!("{:08.2}", x), "-0001.50");
                assert_eq!(format!("{:+}", $lit!(1.5)), "+1.5");
                assert_eq!(format!("{:.0}", $lit!(0.5)), "0");
                assert_eq!(format!("{:.0}", $lit!(1.5)), "2");
                assert_eq!(format!("{:.0}", $lit!(-0.5)), "-0");
                assert_eq!(format!("{:.3}", $lit!(2)), "2.000");
                assert_eq!(format!("{:.70}", $T::DELTA).len(), 72);
                assert!(format!("{:?}", $T::ONE).starts_with("1 (0x"));
            }

            #[test]
            fn bytes_are_little_endian_twos_complement() {
                let x = $T::NEG_ONE;
                let le = x.to_le_bytes();
                assert_eq!(le, x.to_bits().to_le_bytes());
                let mut be = x.to_be_bytes();
                be.reverse();
                assert_eq!(be, le);
            }

            #[test]
            fn operators_by_reference_and_iterators() {
                let a = $lit!(1.5);
                let b = $lit!(0.5);
                assert_eq!(&a + &b, $lit!(2));
                assert_eq!(a - &b, $lit!(1));
                let mut c = a;
                c *= b;
                c /= b;
                c -= &b;
                c %= $lit!(0.75);
                assert_eq!(c, $lit!(0.25));
                let v = [a, b, b];
                assert_eq!(v.iter().sum::<$T>(), $lit!(2.5));
                assert_eq!(v.iter().copied().product::<$T>(), $lit!(0.375));
                assert_eq!(core::iter::repeat($T::MAX).take(3).sum::<$T>(), $T::MAX);
            }
        }
    };
}

edge_suite!(fixed8, FixedFloat8, ff8);
edge_suite!(fixed16, FixedFloat16, ff16);
edge_suite!(fixed32, FixedFloat32, ff32);
edge_suite!(fixed64, FixedFloat64, ff64);

#[test]
fn widening_is_lossless() {
    let mut rng = common::Pcg32::new(1, 2);
    for _ in 0..10_000 {
        let a = FixedFloat8::from_bits(rng.next_u32() as i8);
        let b = FixedFloat16::from(a);
        let c = FixedFloat32::from(b);
        let d = FixedFloat64::from(c);
        assert_eq!(a.to_string(), b.to_string());
        assert_eq!(b.to_string(), d.to_string());
        assert_eq!(FixedFloat64::from(a), d);
        assert_eq!(FixedFloat8::try_from(d), Ok(a));
        assert_eq!(FixedFloat16::try_from(c), Ok(b));
    }
}

#[test]
fn narrowing_rounds_and_checks_range() {
    assert_eq!(
        FixedFloat8::try_from(ff16!(0.03125)),
        Ok(FixedFloat8::DELTA)
    );
    assert_eq!(
        FixedFloat8::try_from(ff16!(-0.03125)),
        Ok(FixedFloat8::ZERO)
    );
    assert_eq!(FixedFloat8::try_from(ff16!(8)), Err(OverflowError));
    assert_eq!(FixedFloat8::try_from(ff16!(7.96875)), Err(OverflowError));
    assert_eq!(FixedFloat8::try_from(ff16!(-8)), Ok(FixedFloat8::MIN));
    assert_eq!(
        FixedFloat32::try_from(FixedFloat64::MAX),
        Err(OverflowError)
    );
    assert_eq!(FixedFloat32::try_from(ff64!(-32768)), Ok(FixedFloat32::MIN));
}

#[test]
fn literal_underscores() {
    assert_eq!(
        ff64!(1_000.000_5),
        "1000.0005".parse::<FixedFloat64>().unwrap()
    );
    assert_eq!(ff32!(-1_0), ff32!(-10));
}

#[test]
fn from_integers() {
    assert_eq!(FixedFloat16::from(-128i8), FixedFloat16::MIN);
    assert_eq!(FixedFloat32::from(i16::MIN), FixedFloat32::MIN);
    assert_eq!(FixedFloat32::from(255u8), ff32!(255));
    assert_eq!(FixedFloat64::from(i32::MAX), FixedFloat64::MAX.floor());
    assert_eq!(FixedFloat64::from(u16::MAX), ff64!(65535));
}

#[test]
fn readme_example() {
    const SPEED: FixedFloat64 = ff64!(12.6);
    assert_eq!(SPEED.to_bits(), 0x0000_000c_9999_999a);
    assert_eq!(
        format!("{:?}", SPEED),
        "12.6000000000931322574615478515625 (0x0000000c9999999a)"
    );
    assert_eq!(format!("{:.1}", SPEED), "12.6");
}

#[cfg(feature = "float-convert")]
#[test]
fn f64_round_trip() {
    let mut rng = common::Pcg32::new(7, 7);
    for _ in 0..100_000 {
        let x = FixedFloat32::from_bits(rng.next_u32() as i32);
        assert_eq!(FixedFloat32::checked_from_f64(x.to_f64()), Some(x));
        let y = FixedFloat64::from_bits(rng.edge_bits(64, 32));
        let f = y.to_f64();
        let back = FixedFloat64::saturating_from_f64(f);
        assert!(
            back.abs_diff(y).to_bits() <= 1 << 11,
            "{:?} {} {:?}",
            y,
            f,
            back
        );
    }
    assert_eq!(FixedFloat8::checked_from_f64(f64::NAN), None);
    assert_eq!(
        FixedFloat8::saturating_from_f64(f64::NAN),
        FixedFloat8::ZERO
    );
    assert_eq!(
        FixedFloat8::saturating_from_f64(f64::INFINITY),
        FixedFloat8::MAX
    );
    assert_eq!(FixedFloat8::saturating_from_f64(-1e300), FixedFloat8::MIN);
    assert_eq!(FixedFloat8::checked_from_f64(-8.0), Some(FixedFloat8::MIN));
    assert_eq!(
        FixedFloat8::checked_from_f64(0.03125),
        Some(FixedFloat8::DELTA)
    );
    assert_eq!(
        FixedFloat8::checked_from_f64(-0.03125),
        Some(FixedFloat8::ZERO)
    );
    assert_eq!(
        FixedFloat8::checked_from_f64(5e-324),
        Some(FixedFloat8::ZERO)
    );
    assert_eq!(FixedFloat64::ONE.to_f64(), 1.0);
    assert_eq!(FixedFloat64::MIN.to_f64(), -2147483648.0);
}
