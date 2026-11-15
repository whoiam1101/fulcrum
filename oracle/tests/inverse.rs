//! `atan`, `atan2`, `asin` and `acos` against the interval Euler series of
//! the oracle (`fulcrum_oracle`, 256 bits): within 1 ulp on every width. The
//! same intervals check the bound `ERROR` of the test reference
//! `tests/common/trig.rs`, and known values check the oracle itself.

#[allow(dead_code)]
#[path = "../../tests/common/trig.rs"]
mod trig;

#[macro_use]
#[path = "../../tests/common/widths.rs"]
mod widths;

use fulcrum::*;
use fulcrum_oracle::{acos, asin, atan, atan2, pi_interval, TRIG_SCALE};
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

/// `[lo, hi]` contains `v` and is narrower than `2^-200`.
fn holds((lo, hi): &(BigInt, BigInt), v: &BigInt) -> bool {
    lo <= v && v <= hi && hi - lo < BigInt::one() << (TRIG_SCALE - 200)
}

#[test]
fn oracle_known_values() {
    let (plo, phi) = pi_interval();
    let quarter = |k: u32| (&plo * k) >> 2u32;
    let one = 1i128 << 32;
    let (lo, hi) = atan(one, 32);
    assert!(lo <= (&phi >> 2u32) && quarter(1) <= hi, "atan 1 = π/4");
    assert!(&hi - &lo < BigInt::one() << (TRIG_SCALE - 200));
    let (lo, hi) = asin(one, 32);
    assert!(lo <= (&phi >> 1u32) && quarter(2) <= hi, "asin 1 = π/2");
    let (lo, hi) = acos(-one, 32);
    assert!(lo <= phi && plo <= hi, "acos -1 = π");
    assert!(holds(&acos(one, 32), &BigInt::from(0)), "acos 1 = 0");
    let (lo, hi) = asin(one / 2, 32);
    let sixth = (&plo / 6u32, &phi / 6u32);
    assert!(lo <= sixth.1 && sixth.0 <= hi, "asin ½ = π/6");
    let (lo, hi) = atan2(-1, -1);
    assert!(lo <= -((&plo * 3u32) >> 2u32) && -((&phi * 3u32) >> 2u32) <= hi);
    let (lo, hi) = atan(1i128 << 34, 32);
    let tan_lo = atan(1i128 << 30, 32);
    let sum = (&lo + &tan_lo.0, &hi + &tan_lo.1);
    assert!(
        sum.0 <= (&phi >> 1u32) && (&plo >> 1u32) <= sum.1,
        "atan 4 + atan ¼ = π/2"
    );
}

fn unit(frac: u32) -> impl Strategy<Value = i128> {
    let one = 1i128 << frac;
    prop_oneof![
        1 => -one..=one,
        1 => (-8i128..=8).prop_map(move |d| if d < 0 { -one - d } else { one - d }),
        1 => -8i128..=8,
    ]
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 4_000, ..ProptestConfig::default() })]

    #[test]
    fn reference_within_its_bound(raw in any::<i64>(), other in any::<i64>(), frac in prop::sample::select(vec![4u32, 8, 16, 32])) {
        let (y, x) = ((raw as i128) >> (64 - 2 * frac), (other as i128) >> (64 - 2 * frac));
        let a = raw as i128 >> (63 - frac);
        let shift = TRIG_SCALE - trig::SCALE;
        let err = BigInt::from(trig::ERROR) << shift;
        for (r, (lo, hi)) in [
            (trig::atan(y, frac), atan(y, frac)),
            (trig::atan2(y, x), atan2(y, x)),
            (trig::asin(a, frac), asin(a, frac)),
            (trig::acos(a, frac), acos(a, frac)),
        ] {
            let r = BigInt::from(r) << shift;
            prop_assert!(&r - &err <= lo && hi <= &r + &err, "{} {} {} / 2^{}", y, x, a, frac);
        }
    }
}

macro_rules! inverse_suite {
    ($module:ident, $T:ident, $lit:ident, $Acc:ident, $Bits:ty, $bits:tt, $frac:tt) => {
        mod $module {
            use super::*;

            proptest! {
                #![proptest_config(ProptestConfig { cases: 4_000, ..ProptestConfig::default() })]

                #[test]
                fn atan_atan2(a in any::<$Bits>(), b in any::<$Bits>(), small in -64i128..=64) {
                    for (y, x) in [(a, b), (a, small as $Bits), (small as $Bits, b)] {
                        let (y, x) = ($T::from_bits(y), $T::from_bits(x));
                        let (ry, rx) = (y.to_bits() as i128, x.to_bits() as i128);
                        let t = y.atan().to_bits() as i128;
                        prop_assert!(within_ulp_of_interval(t, atan(ry, $frac), $frac), "atan {:?} = {}", y, t);
                        let t = y.atan2(x).to_bits() as i128;
                        prop_assert!(within_ulp_of_interval(t, atan2(ry, rx), $frac), "atan2 {:?} {:?} = {}", y, x, t);
                    }
                }

                #[test]
                fn asin_acos(a in unit($frac)) {
                    let x = $T::from_bits(a as $Bits);
                    let s = x.asin().to_bits() as i128;
                    prop_assert!(within_ulp_of_interval(s, asin(a, $frac), $frac), "asin {:?} = {}", x, s);
                    let c = x.acos().to_bits() as i128;
                    prop_assert!(within_ulp_of_interval(c, acos(a, $frac), $frac), "acos {:?} = {}", x, c);
                }
            }
        }
    };
}

for_each_width!(inverse_suite!());
