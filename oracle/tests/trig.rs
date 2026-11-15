//! `sin_turns` and `cos_turns` against the interval Taylor series of the
//! oracle (`fulcrum_oracle::sin_turns`, 256 bits): within 1 ulp on every
//! width. The same intervals check the bound `ERROR` of the test reference
//! `tests/common/trig.rs`, and known values check the oracle itself.

#[allow(dead_code)]
#[path = "../../tests/common/trig.rs"]
mod trig;

#[macro_use]
#[path = "../../tests/common/widths.rs"]
mod widths;

use fulcrum::*;
use fulcrum_oracle::{sin_turns, TRIG_SCALE};
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

proptest! {
    #![proptest_config(ProptestConfig { cases: 4_000, ..ProptestConfig::default() })]

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
            }
        }
    };
}

for_each_width!(trig_suite!());
