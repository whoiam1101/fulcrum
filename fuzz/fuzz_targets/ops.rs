//! Arbitrary operands: no operation panics, `*` and `/` equal the exact
//! rational oracle, `+`, `-` saturate exactly, `%` is exact.

#![no_main]

use fulcrum::{FixedFloat16, FixedFloat32, FixedFloat64, FixedFloat8};
use fulcrum_oracle::Format;
use libfuzzer_sys::fuzz_target;

macro_rules! check {
    ($T:ident, $Bits:ty, $bits:expr, $frac:expr, $data:expr) => {{
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
            assert_eq!((x * y).to_bits() as i128, fmt.mul(a as i128, b as i128).0);
            assert_eq!((x / y).to_bits() as i128, fmt.div(a as i128, b as i128).0);
            assert_eq!((x + y).to_bits(), a.saturating_add(b));
            assert_eq!((x - y).to_bits(), a.saturating_sub(b));
            if b != 0 {
                assert_eq!((x % y).to_bits(), a.wrapping_rem(b));
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
    check!(FixedFloat8, i8, 8, 4, data);
    check!(FixedFloat16, i16, 16, 8, data);
    check!(FixedFloat32, i32, 32, 16, data);
    check!(FixedFloat64, i64, 64, 32, data);
});
