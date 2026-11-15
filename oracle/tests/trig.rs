//! `sin_turns`, `cos_turns` and the radian `sin`, `cos`, `tan` against the
//! interval Taylor series of the oracle (`fulcrum_oracle`, 256 bits): within
//! 1 ulp on every width, `tan` of the value clamped to the range, and
//! `checked_tan` is `None` exactly when the rounded value is out of range.
//! The same intervals check the bound `ERROR` of the test reference
//! `tests/common/trig.rs`, and known values check the oracle itself.

#[allow(dead_code)]
#[path = "../../tests/common/trig.rs"]
mod trig;

#[macro_use]
#[path = "../../tests/common/widths.rs"]
mod widths;

use fulcrum::*;
use fulcrum_oracle::{cos, pi_interval, sin, sin_turns, tan, TRIG_SCALE};
use num_bigint::BigInt;
use num_traits::{One, ToPrimitive};
use proptest::prelude::*;

/// `got / 2^frac` is within one ulp of every value of `[lo, hi] / 2^TRIG_SCALE`.
fn within_ulp_of_interval(got: i128, (lo, hi): (BigInt, BigInt), frac: u32) -> bool {
    let shift = TRIG_SCALE - frac;
    let got = BigInt::from(got) << shift;
    let ulp = BigInt::one() << shift;
    &got - &lo < ulp && &hi - &got < ulp
}

fn turn(frac: u32) -> impl Strategy<Value = i128> {
    let one = 1i128 << frac;
    prop_oneof![
        1 => (0i128..16).prop_map(move |k| k * one / 16),
        1 => (0i128..16, -3i128..=3).prop_map(move |(k, d)| k * one / 16 + d),
        4 => any::<i64>().prop_map(move |v| (v as i128) >> (64 - 2 * frac).min(63)),
    ]
}

#[test]
fn oracle_known_values() {
    let (lo, hi) = sin_turns(1 << 30, 32);
    assert!(lo <= BigInt::one() << TRIG_SCALE && BigInt::one() << TRIG_SCALE <= hi);
    assert!(hi - lo < BigInt::from(1u64 << 16));
    let (lo, hi) = sin_turns(1 << 29, 32);
    let half = BigInt::one() << (2 * TRIG_SCALE - 1);
    assert!(&lo * &lo <= half && half <= &hi * &hi, "sin(π/4)² = ½");
    let (lo, hi) = sin_turns(3 << 30, 32);
    assert!(lo <= -(BigInt::one() << TRIG_SCALE) && -(BigInt::one() << TRIG_SCALE) <= hi);
}

/// `(lo, hi)` clamped to the range of a type with `frac` fractional bits and
/// `bits` bits, in units of `2^-TRIG_SCALE`.
fn clamp((lo, hi): (BigInt, BigInt), bits: u32, frac: u32) -> (BigInt, BigInt) {
    let shift = TRIG_SCALE - frac;
    let max: BigInt = ((BigInt::one() << (bits - 1)) - 1) << shift;
    let min: BigInt = -(BigInt::one() << (bits - 1)) << shift;
    let c = |v: BigInt| v.max(min.clone()).min(max.clone());
    (c(lo), c(hi))
}

/// The value with `frac` fractional bits nearest to every value of the
/// interval, if there is one.
fn rounded((lo, hi): &(BigInt, BigInt), frac: u32) -> Option<BigInt> {
    let shift = TRIG_SCALE - frac;
    let half = BigInt::one() << (shift - 1);
    let (a, b) = ((lo + &half) >> shift, (hi + &half) >> shift);
    if a == b {
        Some(a)
    } else {
        None
    }
}

#[test]
fn oracle_known_radians() {
    let pi_2 = FixedFloat64::FRAC_PI_2.to_bits() as i128;
    let (lo, hi) = sin(pi_2, 32);
    let one = BigInt::one() << TRIG_SCALE;
    assert!(&one - &lo < BigInt::one() << (TRIG_SCALE - 60) && hi <= &one + 1000);
    let (lo, hi) = cos(0, 32);
    assert!(lo <= one && one <= hi && &hi - &lo < BigInt::from(1u64 << 20));
    let (lo, hi) = sin(-(1i128 << 62), 32);
    let (rlo, rhi) = sin(1i128 << 62, 32);
    assert!(lo <= -&rlo && -&rhi <= hi, "sin is odd");
    let (lo, hi) = tan(pi_2 / 2 + 1, 32).unwrap();
    let near = BigInt::one() << (TRIG_SCALE - 30);
    assert!(&lo - &one < near && &one - &hi < near, "tan(π/4) ≈ 1");
    assert!(&hi - &lo < BigInt::from(1u64 << 40));
}

/// The `tan` values of `FixedFloat32` that the test reference cannot round
/// (`trig::TAN_NEAR_MIDPOINT_32`) are correctly rounded: 256 bits decide them.
#[test]
fn tan_near_midpoint_fixed32() {
    for &a in trig::TAN_NEAR_MIDPOINT_32.iter() {
        let x = FixedFloat32::from_bits(a);
        let exact = tan(a as i128, 16).unwrap();
        let r = rounded(&exact, 16).expect("decided at 256 bits");
        let r = r.max(BigInt::from(i32::MIN)).min(BigInt::from(i32::MAX));
        assert_eq!(BigInt::from(x.tan().to_bits()), r, "tan {:#x}", a);
    }
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 4_000, ..ProptestConfig::default() })]

    #[test]
    fn reference_radians_within_its_bound(raw in any::<i64>(), frac in prop::sample::select(vec![4u32, 8, 16, 32])) {
        let raw = (raw as i128) >> (64 - 2 * frac);
        let shift = TRIG_SCALE - trig::SCALE;
        let err = BigInt::from(trig::ERROR) << shift;
        for (r, (lo, hi)) in [
            (trig::sin(raw, frac), sin(raw, frac)),
            (trig::cos(raw, frac), cos(raw, frac)),
        ] {
            let r = BigInt::from(r) << shift;
            prop_assert!(&r - &err <= lo && hi <= &r + &err, "{} / 2^{}", raw, frac);
        }
    }

    #[test]
    fn reference_within_its_bound(raw in any::<i64>(), frac in 2u32..=64) {
        let raw = raw as i128;
        let shift = TRIG_SCALE - trig::SCALE;
        let err = BigInt::from(trig::ERROR) << shift;
        for (r, (lo, hi)) in [
            (trig::sin_turns(raw, frac), sin_turns(raw, frac)),
            (trig::cos_turns(raw, frac), sin_turns(raw + (1 << (frac - 2)), frac)),
        ] {
            let r = BigInt::from(r) << shift;
            prop_assert!(&r - &err <= lo && hi <= &r + &err, "{} / 2^{}", raw, frac);
        }
    }
}

/// The raw value `near` ulps from the odd multiple `(2·pole + 1) · π/2`,
/// with `frac` fractional bits, clamped to `[min, max]`: arguments where `tan`
/// is large or out of range.
fn pole_neighbour(pole: i128, near: i128, frac: u32, min: i128, max: i128) -> i128 {
    let (lo, hi) = pi_interval();
    let mid: BigInt = ((lo + hi) * BigInt::from(2 * pole + 1)) >> (TRIG_SCALE + 2 - frac);
    (mid + near)
        .max(BigInt::from(min))
        .min(BigInt::from(max))
        .to_i128()
        .unwrap()
}

macro_rules! trig_suite {
    ($module:ident, $T:ident, $lit:ident, $Acc:ident, $Bits:ty, $bits:tt, $frac:tt) => {
        mod $module {
            use super::*;

            proptest! {
                #![proptest_config(ProptestConfig { cases: 4_000, ..ProptestConfig::default() })]

                #[test]
                fn sin_cos_turns(a in turn($frac)) {
                    let x = $T::from_bits(a as $Bits);
                    let a = x.to_bits() as i128;
                    let s = x.sin_turns().to_bits() as i128;
                    prop_assert!(within_ulp_of_interval(s, sin_turns(a, $frac), $frac), "sin_turns {:?} = {}", x, s);
                    let c = x.cos_turns().to_bits() as i128;
                    let quarter = 1i128 << ($frac - 2);
                    prop_assert!(within_ulp_of_interval(c, sin_turns(a + quarter, $frac), $frac), "cos_turns {:?} = {}", x, c);
                }

                #[test]
                fn sin_cos_tan(a in any::<$Bits>(), near in -64i128..=64, pole in 0i128..8) {
                    for x in [$T::from_bits(a), $T::from_bits(pole_neighbour(pole, near, $frac, <$Bits>::MIN as i128, <$Bits>::MAX as i128) as $Bits)] {
                        let a = x.to_bits() as i128;
                        let (s, c) = x.sin_cos();
                        prop_assert_eq!((s, c), (x.sin(), x.cos()));
                        prop_assert!(within_ulp_of_interval(s.to_bits() as i128, sin(a, $frac), $frac), "sin {:?} = {:?}", x, s);
                        prop_assert!(within_ulp_of_interval(c.to_bits() as i128, cos(a, $frac), $frac), "cos {:?} = {:?}", x, c);
                        let exact = tan(a, $frac).unwrap();
                        let t = x.tan().to_bits() as i128;
                        prop_assert!(within_ulp_of_interval(t, clamp(exact.clone(), $bits, $frac), $frac), "tan {:?} = {}", x, t);
                        if let Some(r) = rounded(&exact, $frac) {
                            let fits = BigInt::from(<$Bits>::MIN) <= r && r <= BigInt::from(<$Bits>::MAX);
                            prop_assert_eq!(x.checked_tan().is_some(), fits, "checked_tan {:?}", x);
                        }
                    }
                }
            }
        }
    };
}

for_each_width!(trig_suite!());
