//! Arbitrary bytes as a decimal string: parsing never panics, accepted input
//! equals the exact rational oracle, and `parse(display(x)) == x`.

#![no_main]

#[macro_use]
#[path = "../../tests/common/widths.rs"]
mod widths;

use fulcrum::*;
use fulcrum_oracle::Format;
use libfuzzer_sys::fuzz_target;

macro_rules! check {
    ($s:ident, $module:ident, $T:ident, $lit:ident, $Acc:ident, $Raw:ident, $bits:tt, $frac:tt) => {{
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
        for_each_width!(check!(s,));
    }
});
