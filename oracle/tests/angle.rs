//! The angle types against the oracle (`fulcrum_oracle`, 256 bits):
//! `to_radians` and `from_radians` are correctly rounded wherever the interval
//! of `π` decides the rounding (every value of 8 and 16 bits, random values of
//! 32 and 64), and `sin`, `cos` of `Angle64` are within 1 ulp of the interval
//! Taylor series.

use fulcrum::*;
use fulcrum_oracle::{angle_from_radians, angle_to_radians, sin_turns, TRIG_SCALE};
use num_bigint::BigInt;
use num_traits::One;
use proptest::prelude::*;

/// `got / 2^frac` is within one ulp of every value of `[lo, hi] / 2^TRIG_SCALE`.
fn within_ulp_of_interval(got: i128, (lo, hi): (BigInt, BigInt), frac: u32) -> bool {
    let shift = TRIG_SCALE - frac;
    let got = BigInt::from(got) << shift;
    let ulp = BigInt::one() << shift;
    &got - &lo < ulp && &hi - &got < ulp
}

macro_rules! check_radians {
    ($A:ident, $T:ident, $n:expr, $f:expr, $t:expr, $x:expr) => {{
        let a = $A::from_bits($t);
        let r = angle_to_radians($t as u64, $n, $f).expect("decided at 256 bits");
        assert_eq!(
            BigInt::from(a.to_radians().to_bits()),
            r,
            "to_radians {:?}",
            a
        );
        let x = $T::from_bits($x);
        let t = angle_from_radians($x as i128, $f, $n).expect("decided at 256 bits");
        assert_eq!(
            $A::from_radians(x).to_bits() as u64,
            t,
            "from_radians {:?}",
            x
        );
    }};
}

#[test]
fn angle8_all_values() {
    for t in u8::MIN..=u8::MAX {
        check_radians!(Angle8, FixedFloat8, 8, 4, t, t as i8);
    }
}

#[test]
fn angle16_all_values() {
    for t in u16::MIN..=u16::MAX {
        check_radians!(Angle16, FixedFloat16, 16, 8, t, t as i16);
    }
}

#[test]
fn oracle_known_values() {
    assert_eq!(
        angle_to_radians(1 << 62, 64, 32),
        Some(BigInt::from(FixedFloat64::FRAC_PI_2.to_bits()))
    );
    assert_eq!(
        angle_to_radians(1 << 63, 64, 32),
        Some(BigInt::from(-FixedFloat64::PI.to_bits()))
    );
    assert_eq!(angle_from_radians(0, 32, 64), Some(0));
    let pi = FixedFloat64::PI.to_bits() as i128;
    let half = angle_from_radians(pi, 32, 64).unwrap();
    assert!(half.abs_diff(1 << 63) < 1 << 32, "π is half a turn");
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 20_000, ..ProptestConfig::default() })]

    #[test]
    fn angle32_radians(t in any::<u32>(), x in any::<i32>()) {
        check_radians!(Angle32, FixedFloat32, 32, 16, t, x);
    }

    #[test]
    fn angle64_radians(t in any::<u64>(), x in any::<i64>()) {
        check_radians!(Angle64, FixedFloat64, 64, 32, t, x);
    }

    #[test]
    fn angle64_sin_cos(t in any::<u64>()) {
        let a = Angle64::from_bits(t);
        let (s, c) = a.sin_cos();
        prop_assert!(within_ulp_of_interval(s.to_bits() as i128, sin_turns(t as i128, 64), 32), "sin {:?}", a);
        let quarter = (t as i128) + (1 << 62);
        prop_assert!(within_ulp_of_interval(c.to_bits() as i128, sin_turns(quarter, 64), 32), "cos {:?}", a);
    }
}
