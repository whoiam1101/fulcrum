//! `exp2`, `log2`, `exp` and `ln` against the interval series of the oracle
//! (`fulcrum_oracle`, 256 bits): within 1 ulp on every width, `exp2` and
//! `exp` saturated and `checked_*` `None` exactly when the rounded value is
//! out of range. The same intervals check the bounds `LOG2_ERROR`,
//! `EXP2_ERROR`, `LN_ERROR` and `EXP_ERROR` of the test reference
//! `tests/common/exp.rs`, and known values check the oracle itself.

#[allow(dead_code)]
#[path = "../../tests/common/exp.rs"]
mod exp;

#[macro_use]
#[path = "../../tests/common/widths.rs"]
mod widths;

use fulcrum::*;
use fulcrum_oracle::{exp, exp2, ln, ln2_interval, log2, TRIG_SCALE};
use num_bigint::BigInt;
use num_traits::{One, Zero};
use proptest::prelude::*;

/// `got / 2^frac` is within one ulp of every value of `[lo, hi] / 2^TRIG_SCALE`.
fn within_ulp_of_interval(got: i128, (lo, hi): &(BigInt, BigInt), frac: u32) -> bool {
    let shift = TRIG_SCALE - frac;
    let got = BigInt::from(got) << shift;
    let ulp = BigInt::one() << shift;
    &got - lo < ulp && hi - &got < ulp
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
fn oracle_known_values() {
    let one = BigInt::one() << TRIG_SCALE;
    let (lo, hi) = ln2_interval();
    assert!(&hi - &lo < BigInt::from(1u64 << 16));
    assert!(lo > BigInt::from(693) * &one / 1000 && hi < BigInt::from(694) * &one / 1000);
    let (lo, hi) = exp2(1 << 31, 32);
    let two = BigInt::from(2) << (2 * TRIG_SCALE);
    assert!(&lo * &lo <= two && two <= &hi * &hi, "2^½ squared is 2");
    assert!(&hi - &lo < BigInt::from(1u64 << 16));
    let (lo, hi) = exp2(-3 << 32, 32);
    assert!(lo <= &one >> 3 && &one >> 3 <= hi, "2^-3");
    let (lo, hi) = log2(8 << 32, 32);
    let three = BigInt::from(3) << TRIG_SCALE;
    assert!(lo <= three && three <= hi, "log₂ 8 = 3");
    assert!(&hi - &lo < BigInt::from(1u64 << 16));
    let (lo, hi) = log2(3 << 31, 32);
    let digits: BigInt = "5849625007211561814537389439478165087598".parse().unwrap();
    let log2_1_5 = (digits << TRIG_SCALE) / BigInt::from(10u32).pow(40);
    let near = BigInt::one() << (TRIG_SCALE - 120);
    assert!(lo - &near <= log2_1_5 && log2_1_5 <= hi + &near, "log₂ 1.5");
    let (lo, hi) = ln(1 << 32, 32);
    assert!(lo <= BigInt::zero() && BigInt::zero() <= hi, "ln 1 = 0");
    let (lo, hi) = ln(2 << 32, 32);
    let (llo, lhi) = ln2_interval();
    assert!(lo <= lhi && llo <= hi, "ln 2");
    let (lo, hi) = exp(1 << 32, 32);
    let digits: BigInt = "27182818284590452353602874713526624977572".parse().unwrap();
    let e = (digits << TRIG_SCALE) / BigInt::from(10u32).pow(40);
    assert!(&lo - &near <= e && e <= &hi + &near, "e");
    assert!(&hi - &lo < BigInt::from(1u64 << 16));
    let (lo, hi) = exp(-(1 << 32), 32);
    let product = &lo * &e;
    let one_squared = BigInt::one() << (2 * TRIG_SCALE);
    assert!(
        product <= one_squared && one_squared <= (&hi + &near) * (&e + &near),
        "e · e^-1 = 1"
    );
    let (lo, hi) = exp(0, 32);
    assert!(lo <= one && one <= hi, "e^0 = 1");
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 4_000, ..ProptestConfig::default() })]

    #[test]
    fn reference_log2_within_its_bound(raw in 1i64.., frac in prop::sample::select(vec![4u32, 8, 16, 32])) {
        let raw = (raw as i128) >> (64 - 2 * frac);
        prop_assume!(raw > 0);
        let shift = TRIG_SCALE - exp::SCALE;
        let err = BigInt::from(exp::LOG2_ERROR) << shift;
        let r = BigInt::from(exp::log2(raw, frac)) << shift;
        let (lo, hi) = log2(raw, frac);
        prop_assert!(&r - &err <= lo && hi <= &r + &err, "{} / 2^{}", raw, frac);
    }

    #[test]
    fn reference_exp2_within_its_bound(raw in any::<i64>(), frac in prop::sample::select(vec![4u32, 8, 16, 32])) {
        let raw = (raw as i128) >> (64 - frac - 7);
        let (m, s, error) = exp::exp2(raw, frac);
        let (lo, hi) = exp2(raw, frac);
        let shift = (s + i128::from(frac)) as usize;
        let (lo, hi) = (lo << shift, hi << shift);
        let r_lo = BigInt::from(m - error) << TRIG_SCALE;
        let r_hi = BigInt::from(m + error) << TRIG_SCALE;
        if error == 0 {
            prop_assert!(lo <= r_lo && r_hi <= hi, "exact {} / 2^{}", raw, frac);
        } else {
            prop_assert!(r_lo <= lo && hi <= r_hi, "{} / 2^{}", raw, frac);
        }
    }

    #[test]
    fn reference_ln_within_its_bound(raw in 1i64.., frac in prop::sample::select(vec![4u32, 8, 16, 32])) {
        let raw = (raw as i128) >> (64 - 2 * frac);
        prop_assume!(raw > 0);
        let shift = TRIG_SCALE - exp::SCALE;
        let err = BigInt::from(exp::LN_ERROR) << shift;
        let r = BigInt::from(exp::ln(raw, frac)) << shift;
        let (lo, hi) = ln(raw, frac);
        prop_assert!(&r - &err <= lo && hi <= &r + &err, "{} / 2^{}", raw, frac);
    }

    #[test]
    fn reference_exp_within_its_bound(raw in any::<i64>(), frac in prop::sample::select(vec![4u32, 8, 16, 32])) {
        let raw = (raw as i128) >> (64 - frac - 6);
        let (m, s, error) = exp::exp(raw, frac);
        let (lo, hi) = exp(raw, frac);
        let shift = s + i128::from(frac);
        let (lo, hi) = if shift >= 0 {
            (lo << shift as usize, hi << shift as usize)
        } else {
            (lo >> (-shift) as usize, (hi >> (-shift) as usize) + 1)
        };
        let r_lo = BigInt::from(m - error) << TRIG_SCALE;
        let r_hi = BigInt::from(m + error) << TRIG_SCALE;
        if error == 0 {
            prop_assert!(lo <= r_lo && r_hi <= hi, "exact {} / 2^{}", raw, frac);
        } else {
            prop_assert!(r_lo <= lo && hi <= r_hi, "{} / 2^{}", raw, frac);
        }
    }
}

macro_rules! exp_suite {
    ($module:ident, $T:ident, $lit:ident, $Acc:ident, $Bits:ty, $bits:tt, $frac:tt) => {
        mod $module {
            use super::*;

            proptest! {
                #![proptest_config(ProptestConfig { cases: 4_000, ..ProptestConfig::default() })]

                #[test]
                fn log2_within_ulp(a in 1..=<$Bits>::MAX, shift in 0u32..$bits) {
                    let x = $T::from_bits((a >> shift).max(1));
                    let a = x.to_bits() as i128;
                    let y = x.log2();
                    prop_assert_eq!(x.checked_log2(), Some(y));
                    prop_assert!(within_ulp_of_interval(y.to_bits() as i128, &log2(a, $frac), $frac), "log2 {:?} = {:?}", x, y);
                }

                #[test]
                fn ln_within_ulp(a in 1..=<$Bits>::MAX, shift in 0u32..$bits) {
                    let x = $T::from_bits((a >> shift).max(1));
                    let a = x.to_bits() as i128;
                    let y = x.ln();
                    prop_assert_eq!(x.checked_ln(), Some(y));
                    prop_assert!(within_ulp_of_interval(y.to_bits() as i128, &ln(a, $frac), $frac), "ln {:?} = {:?}", x, y);
                }

                #[test]
                fn exp_within_ulp(a in any::<$Bits>(), shift in 0u32..$bits) {
                    let x = $T::from_bits(a >> shift);
                    let y = x.exp();
                    if x >= $T::saturating_from_int($frac) {
                        prop_assert_eq!(y, $T::MAX);
                        prop_assert_eq!(x.checked_exp(), None);
                    } else if x <= $T::saturating_from_int(-2 * $frac) {
                        prop_assert_eq!(y, $T::ZERO);
                        prop_assert_eq!(x.checked_exp(), Some(y));
                    } else {
                        let exact = exp(x.to_bits() as i128, $frac);
                        let max = BigInt::from(<$Bits>::MAX);
                        match rounded(&exact, $frac) {
                            Some(v) if v > max => {
                                prop_assert_eq!(y, $T::MAX);
                                prop_assert_eq!(x.checked_exp(), None);
                            }
                            rounded_value => {
                                if rounded_value.is_some() {
                                    prop_assert_eq!(x.checked_exp(), Some(y));
                                }
                                let top = max << (TRIG_SCALE - $frac);
                                let clamped = (exact.0.min(top.clone()), exact.1.min(top));
                                prop_assert!(within_ulp_of_interval(y.to_bits() as i128, &clamped, $frac), "exp {:?} = {:?}", x, y);
                            }
                        }
                    }
                }

                #[test]
                fn exp2_within_ulp(a in any::<$Bits>(), shift in 0u32..$bits) {
                    let x = $T::from_bits(a >> shift);
                    let y = x.exp2();
                    if x >= $T::saturating_from_int($frac - 1) {
                        prop_assert_eq!(y, $T::MAX);
                        prop_assert_eq!(x.checked_exp2(), None);
                    } else {
                        let exact = exp2(x.to_bits() as i128, $frac);
                        let max = BigInt::from(<$Bits>::MAX);
                        match rounded(&exact, $frac) {
                            Some(v) if v > max => {
                                prop_assert_eq!(y, $T::MAX);
                                prop_assert_eq!(x.checked_exp2(), None);
                            }
                            rounded_value => {
                                if rounded_value.is_some() {
                                    prop_assert_eq!(x.checked_exp2(), Some(y));
                                }
                                let top = max << (TRIG_SCALE - $frac);
                                let clamped = (exact.0.min(top.clone()), exact.1.min(top));
                                prop_assert!(within_ulp_of_interval(y.to_bits() as i128, &clamped, $frac), "exp2 {:?} = {:?}", x, y);
                            }
                        }
                    }
                }
            }
        }
    };
}

for_each_width!(exp_suite!());
