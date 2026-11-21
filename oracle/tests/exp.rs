//! `exp2`, `log2`, `exp`, `ln`, `pow` and `powi` against the interval series
//! of the oracle (`fulcrum_oracle`, 256 bits): within 1 ulp on every width,
//! `exp2`, `exp`, `pow` and `powi` saturated and `checked_*` `None` exactly
//! when the rounded value is out of range. The same intervals check the
//! bounds `LOG2_ERROR`, `EXP2_ERROR`, `LN_ERROR`, `EXP_ERROR` and the error
//! of `pow` of the test reference `tests/common/exp.rs`, and known values
//! check the oracle itself.

#[allow(dead_code)]
#[path = "../../tests/common/exp.rs"]
mod exp;

#[allow(dead_code)]
#[path = "../../tests/common/trig.rs"]
mod trig;

#[macro_use]
#[path = "../../tests/common/widths.rs"]
mod widths;

use fulcrum::*;
use fulcrum_oracle::{
    exp, exp2, ln, ln2_interval, log2, pow, rounded, within_ulp_of_interval, TRIG_SCALE,
};
use num_bigint::BigInt;
use num_traits::{One, Zero};
use proptest::prelude::*;

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
    let (lo, hi) = pow(2 << 32, 32, 1 << 31, 32).unwrap();
    assert!(&lo * &lo <= two && two <= &hi * &hi, "2^½ squared is 2");
    assert!(&hi - &lo < BigInt::from(1u64 << 16));
    let (lo, hi) = pow(3 << 32, 32, 4, 0).unwrap();
    let eighty_one = BigInt::from(81) << TRIG_SCALE;
    assert!(lo <= eighty_one && eighty_one <= hi, "3^4 = 81");
    let (lo, hi) = pow(1 << 31, 32, -3, 0).unwrap();
    let eight = BigInt::from(8) << TRIG_SCALE;
    assert!(lo <= eight && eight <= hi, "½^-3 = 8");
    assert!(pow(3 << 32, 32, 41, 0).is_none(), "3^41 > 2^64");
}

/// Checks `got`, `checked` of `x^y` for `x = a / 2^frac`, `y = y / 2^frac_y`
/// against the oracle, for a type with `frac` fractional bits and raw values
/// in `[min, max]`.
fn check_pow_oracle(
    a: i128,
    y: i128,
    frac_y: u32,
    (got, checked): (i128, Option<i128>),
    frac: u32,
    (min, max): (i128, i128),
) -> Result<(), TestCaseError> {
    let one = 1i128 << frac;
    if y == 0 {
        prop_assert_eq!((got, checked), (one, Some(one)));
        return Ok(());
    }
    if a == 0 {
        let expected = if y > 0 { (0, Some(0)) } else { (max, None) };
        prop_assert_eq!((got, checked), expected);
        return Ok(());
    }
    if a < 0 && y & ((1 << frac_y) - 1) != 0 {
        prop_assert_eq!((got, checked), (0, None));
        return Ok(());
    }
    let negative = a < 0 && (y >> frac_y) & 1 == 1;
    let (saturated, limit) = if negative { (min, -min) } else { (max, max) };
    let magnitude = if negative { -got } else { got };
    match pow(a.abs(), frac, y, frac_y) {
        None => prop_assert_eq!((got, checked), (saturated, None)),
        Some(exact) => match rounded(&exact, frac) {
            Some(v) if v > BigInt::from(limit) => {
                prop_assert_eq!((got, checked), (saturated, None));
            }
            rounded_value => {
                if rounded_value.is_some() {
                    prop_assert_eq!(checked, Some(got));
                }
                let top = BigInt::from(limit) << (TRIG_SCALE - frac);
                let clamped = (exact.0.min(top.clone()), exact.1.min(top));
                prop_assert!(
                    magnitude >= 0,
                    "sign of {} ^ {} / 2^{} = {}",
                    a,
                    y,
                    frac_y,
                    got
                );
                prop_assert!(
                    within_ulp_of_interval(magnitude, &clamped, frac),
                    "{} ^ {} / 2^{} = {}",
                    a,
                    y,
                    frac_y,
                    got
                );
            }
        },
    }
    Ok(())
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 4_000, ..ProptestConfig::default() })]

    #[test]
    fn reference_pow_within_its_bound(
        raw in 1i64..,
        y in any::<i32>(),
        y_shift in 0u32..40,
        frac in prop::sample::select(vec![4u32, 8, 16, 32]),
        frac_y in prop::sample::select(vec![0u32, 4, 8, 16, 32]),
    ) {
        let raw = (raw as i128) >> (64 - 2 * frac);
        prop_assume!(raw > 0);
        let y = i128::from(y) >> y_shift;
        let (m, s, error) = exp::pow(raw, frac, y, frac_y);
        let shift = s + i128::from(frac);
        if !(0..=200).contains(&shift) {
            return Ok(());
        }
        if let Some((lo, hi)) = pow(raw, frac, y, frac_y) {
            let (lo, hi) = (lo << shift as usize, hi << shift as usize);
            let r_lo = BigInt::from(m - error) << TRIG_SCALE;
            let r_hi = BigInt::from(m + error) << TRIG_SCALE;
            prop_assert!(r_lo <= lo && hi <= r_hi, "{} / 2^{} ^ {} / 2^{}", raw, frac, y, frac_y);
        }
    }

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
                fn pow_within_ulp(a in any::<$Bits>(), b in any::<$Bits>(), sa in 0u32..$bits, sb in 0u32..$bits) {
                    let (x, y) = ($T::from_bits(a >> sa), $T::from_bits(b >> sb));
                    let range = ($T::MIN.to_bits() as i128, $T::MAX.to_bits() as i128);
                    let result = (x.pow(y).to_bits() as i128, x.checked_pow(y).map(|v| v.to_bits() as i128));
                    check_pow_oracle(x.to_bits() as i128, y.to_bits() as i128, $frac, result, $frac, range)?;
                }

                #[test]
                fn pow_near_one_within_ulp(d in -4096i64..4096, b in any::<$Bits>(), sb in 0u32..$bits) {
                    let a = ((1i64 << $frac) + (d >> (12 - ($frac / 3).min(12)))) as $Bits;
                    let (x, y) = ($T::from_bits(a), $T::from_bits(b >> sb));
                    let range = ($T::MIN.to_bits() as i128, $T::MAX.to_bits() as i128);
                    let result = (x.pow(y).to_bits() as i128, x.checked_pow(y).map(|v| v.to_bits() as i128));
                    check_pow_oracle(x.to_bits() as i128, y.to_bits() as i128, $frac, result, $frac, range)?;
                    let n = (b >> sb) as i32;
                    let result = (x.powi(n).to_bits() as i128, x.checked_powi(n).map(|v| v.to_bits() as i128));
                    check_pow_oracle(x.to_bits() as i128, i128::from(n), 0, result, $frac, range)?;
                }

                #[test]
                fn powi_within_ulp(a in any::<$Bits>(), sa in 0u32..$bits, n in -80i32..80) {
                    let x = $T::from_bits(a >> sa);
                    let range = ($T::MIN.to_bits() as i128, $T::MAX.to_bits() as i128);
                    let result = (x.powi(n).to_bits() as i128, x.checked_powi(n).map(|v| v.to_bits() as i128));
                    check_pow_oracle(x.to_bits() as i128, i128::from(n), 0, result, $frac, range)?;
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
