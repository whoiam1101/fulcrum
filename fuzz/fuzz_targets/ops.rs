//! Arbitrary operands: no operation panics; `*`, `/`, `mul_add`, `mul_div`,
//! `lerp`, `sqrt`, `rsqrt`, `hypot` and their `checked_*` equal the exact
//! rational oracle; `sin`, `cos`, `tan` (clamped to the range), `atan`,
//! `atan2`, `asin`, `acos` and `sin`, `cos` of the angle type are within 1
//! ulp of the interval oracle, its `to_radians` and `from_radians` equal it
//! where it decides the rounding; `exp2`, `exp` (clamped to the range),
//! `log2` and `ln` are within 1 ulp of the interval oracle, `MAX` and `MIN`
//! with `checked_*` `None` outside it, `exp` far below the range `0`; `+`,
//! `-` saturate exactly; `%` is exact.

#![no_main]

#[macro_use]
#[path = "../../tests/common/widths.rs"]
mod widths;

use fulcrum::*;
use fulcrum_oracle::{Format, TRIG_SCALE};
use libfuzzer_sys::fuzz_target;
use num_bigint::BigInt;

/// `got / 2^frac` is within one ulp of every value of `[lo, hi] / 2^TRIG_SCALE`
/// clamped to `[min, max] / 2^frac`.
fn within_ulp((lo, hi): (BigInt, BigInt), got: i128, frac: u32, min: i128, max: i128) -> bool {
    let shift = TRIG_SCALE - frac;
    let clamp = |v: BigInt| {
        v.max(BigInt::from(min) << shift)
            .min(BigInt::from(max) << shift)
    };
    let (lo, hi) = (clamp(lo), clamp(hi));
    let got = BigInt::from(got) << shift;
    let ulp = BigInt::from(1) << shift;
    &got - lo < ulp && hi - &got < ulp
}

macro_rules! check {
    ($data:ident, $module:ident, $T:ident, $lit:ident, $Acc:ident, $Bits:ty, $bits:tt, $frac:tt) => {{
        const N: usize = core::mem::size_of::<$Bits>();
        if $data.len() >= 2 * N {
            let a = <$Bits>::from_le_bytes($data[..N].try_into().unwrap());
            let b = <$Bits>::from_le_bytes($data[N..2 * N].try_into().unwrap());
            let fmt = Format {
                bits: $bits,
                frac: $frac,
            };
            let x = $T::from_bits(a);
            let y = $T::from_bits(b);
            let (mul, mul_fits) = fmt.mul(a as i128, b as i128);
            assert_eq!((x * y).to_bits() as i128, mul);
            assert_eq!(x.checked_mul(y).is_some(), mul_fits);
            let (div, div_fits) = fmt.div(a as i128, b as i128);
            assert_eq!((x / y).to_bits() as i128, div);
            assert_eq!(x.checked_div(y).is_some(), div_fits);
            let (sqrt, sqrt_fits) = fmt.sqrt(a as i128);
            assert_eq!(x.sqrt().to_bits() as i128, sqrt);
            assert_eq!(x.checked_sqrt().is_some(), sqrt_fits);
            let (rsqrt, rsqrt_fits) = fmt.rsqrt(a as i128);
            assert_eq!(x.rsqrt().to_bits() as i128, rsqrt);
            assert_eq!(x.checked_rsqrt().is_some(), rsqrt_fits);
            let (hypot, hypot_fits) = fmt.hypot(a as i128, b as i128);
            assert_eq!(x.hypot(y).to_bits() as i128, hypot);
            assert_eq!(x.checked_hypot(y).is_some(), hypot_fits);
            let (min, max) = (<$Bits>::MIN as i128, <$Bits>::MAX as i128);
            let (s, c) = x.sin_cos();
            let trig = [
                (fulcrum_oracle::sin(a as i128, $frac), s),
                (fulcrum_oracle::cos(a as i128, $frac), c),
            ];
            for (exact, got) in trig {
                assert!(within_ulp(exact, got.to_bits() as i128, $frac, min, max));
            }
            if let Some(exact) = fulcrum_oracle::tan(a as i128, $frac) {
                assert!(within_ulp(
                    exact,
                    x.tan().to_bits() as i128,
                    $frac,
                    min,
                    max
                ));
            }
            assert_eq!(x.checked_tan().unwrap_or(x.tan()), x.tan());
            let unit = (a as i128).rem_euclid((1 << ($frac + 1)) + 1) - (1 << $frac);
            let u = $T::from_bits(unit as $Bits);
            let inverse = [
                (fulcrum_oracle::atan(a as i128, $frac), x.atan()),
                (fulcrum_oracle::atan2(a as i128, b as i128), x.atan2(y)),
                (fulcrum_oracle::asin(unit, $frac), u.asin()),
                (fulcrum_oracle::acos(unit, $frac), u.acos()),
            ];
            for (exact, got) in inverse {
                assert!(within_ulp(exact, got.to_bits() as i128, $frac, min, max));
            }
            let g = <<$T as FixedFloat>::Angle>::from_bits(a as _);
            let t = g.to_bits() as u64;
            let (s, c) = g.sin_cos();
            let turns = [
                (fulcrum_oracle::sin_turns(t as i128, $bits), s),
                (
                    fulcrum_oracle::sin_turns(t as i128 + (1 << ($bits - 2)), $bits),
                    c,
                ),
            ];
            for (exact, got) in turns {
                assert!(within_ulp(exact, got.to_bits() as i128, $frac, min, max));
            }
            if let Some(r) = fulcrum_oracle::angle_to_radians(t, $bits, $frac) {
                assert_eq!(BigInt::from(g.to_radians().to_bits()), r);
            }
            if let Some(r) = fulcrum_oracle::angle_from_radians(b as i128, $frac, $bits) {
                assert_eq!(
                    <<$T as FixedFloat>::Angle>::from_radians(y).to_bits() as u64,
                    r
                );
            }
            if a > 0 {
                let exact = fulcrum_oracle::log2(a as i128, $frac);
                assert!(within_ulp(
                    exact,
                    x.log2().to_bits() as i128,
                    $frac,
                    min,
                    max
                ));
                assert_eq!(x.checked_log2(), Some(x.log2()));
            } else {
                assert_eq!((x.log2(), x.checked_log2()), ($T::MIN, None));
            }
            if (a as i128) >> $frac < $frac - 1 {
                let exact = fulcrum_oracle::exp2(a as i128, $frac);
                assert!(within_ulp(
                    exact,
                    x.exp2().to_bits() as i128,
                    $frac,
                    min,
                    max
                ));
                assert_eq!(x.checked_exp2().unwrap_or($T::MAX), x.exp2());
            } else {
                assert_eq!((x.exp2(), x.checked_exp2()), ($T::MAX, None));
            }
            if a > 0 {
                let exact = fulcrum_oracle::ln(a as i128, $frac);
                assert!(within_ulp(exact, x.ln().to_bits() as i128, $frac, min, max));
                assert_eq!(x.checked_ln(), Some(x.ln()));
            } else {
                assert_eq!((x.ln(), x.checked_ln()), ($T::MIN, None));
            }
            if (a as i128) >= $frac << $frac {
                assert_eq!((x.exp(), x.checked_exp()), ($T::MAX, None));
            } else if (a as i128) <= -(2 * $frac) << $frac {
                assert_eq!((x.exp(), x.checked_exp()), ($T::ZERO, Some($T::ZERO)));
            } else {
                let exact = fulcrum_oracle::exp(a as i128, $frac);
                assert!(within_ulp(
                    exact,
                    x.exp().to_bits() as i128,
                    $frac,
                    min,
                    max
                ));
                assert_eq!(x.checked_exp().unwrap_or($T::MAX), x.exp());
            }
            assert_eq!((x + y).to_bits(), a.saturating_add(b));
            assert_eq!((x - y).to_bits(), a.saturating_sub(b));
            if b != 0 {
                assert_eq!((x % y).to_bits(), a.wrapping_rem(b));
            }
            if $data.len() >= 3 * N {
                let c = <$Bits>::from_le_bytes($data[2 * N..3 * N].try_into().unwrap());
                let z = $T::from_bits(c);
                let (a, b, c) = (a as i128, b as i128, c as i128);
                let (mul_add, mul_add_fits) = fmt.mul_add(a, b, c);
                assert_eq!(x.mul_add(y, z).to_bits() as i128, mul_add);
                assert_eq!(x.checked_mul_add(y, z).is_some(), mul_add_fits);
                let (mul_div, mul_div_fits) = fmt.mul_div(a, b, c);
                assert_eq!(x.mul_div(y, z).to_bits() as i128, mul_div);
                assert_eq!(x.checked_mul_div(y, z).is_some(), mul_div_fits);
                let (lerp, lerp_fits) = fmt.lerp(a, b, c);
                assert_eq!(x.lerp(y, z).to_bits() as i128, lerp);
                assert_eq!(x.checked_lerp(y, z).is_some(), lerp_fits);
            }
            let _ = (
                x.wrapping_mul(y),
                x.overflowing_div(y),
                x.div_int(b),
                x.mul_int(b),
                x.midpoint(y),
                x.abs_diff(y),
                x.round(),
                x.round_ties_even(),
                x.ceil(),
                x.recip(),
                -x,
                x.abs(),
            );
        }
    }};
}

fuzz_target!(|data: &[u8]| {
    for_each_width!(check!(data,));
});
