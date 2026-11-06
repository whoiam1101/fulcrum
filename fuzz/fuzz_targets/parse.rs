//! Arbitrary bytes as a decimal string: parsing never panics, accepted input
//! equals the exact rational oracle, and `parse(display(x)) == x`.

#![no_main]

use fulcrum::{FixedFloat16, FixedFloat32, FixedFloat64, FixedFloat8, ParseErrorKind};
use fulcrum_oracle::Format;
use libfuzzer_sys::fuzz_target;

macro_rules! check {
    ($T:ident, $bits:expr, $frac:expr, $s:expr) => {{
        let fmt = Format {
            bits: $bits,
            frac: $frac,
        };
        match $s.parse::<$T>() {
            Ok(v) => {
                assert_eq!(fmt.parse($s), Some(v.to_bits() as i128), "{:?}", $s);
                assert_eq!(v.to_string().parse::<$T>(), Ok(v));
            }
            Err(e) if e.kind() == ParseErrorKind::Overflow => {
                let digits_only = $s.trim_start_matches(['-', '+']).replace('.', "");
                if digits_only.len() <= 60 {
                    assert_eq!(fmt.parse($s), None, "{:?}", $s);
                }
            }
            Err(_) => {}
        }
    }};
}

fuzz_target!(|data: &[u8]| {
    if let Ok(s) = core::str::from_utf8(data) {
        check!(FixedFloat8, 8, 4, s);
        check!(FixedFloat16, 16, 8, s);
        check!(FixedFloat32, 32, 16, s);
        check!(FixedFloat64, 64, 32, s);
    }
});
