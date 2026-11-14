//! Arbitrary operands: no operation panics; `*`, `/`, `mul_add`, `mul_div`,
//! `lerp` and their `checked_*` equal the exact rational oracle; `+`, `-`
//! saturate exactly; `%` is exact.

#![no_main]

#[macro_use]
#[path = "../../tests/common/widths.rs"]
mod widths;

use fulcrum::*;
use fulcrum_oracle::Format;
use libfuzzer_sys::fuzz_target;

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
