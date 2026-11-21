//! `parse(display(x)) = x` for every value of `FixedFloat32`, only with
//! `--ignored` (2^32 values, the weekly run).

#![cfg(not(feature = "strict-overflow"))]

#[macro_use]
mod common;

use common::*;
use fulcrum::FixedFloat32;

struct Buf {
    bytes: [u8; 64],
    len: usize,
}

impl core::fmt::Write for Buf {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        let end = self.len + s.len();
        self.bytes[self.len..end].copy_from_slice(s.as_bytes());
        self.len = end;
        Ok(())
    }
}

#[test]
#[ignore = "2^32 values: run with --ignored --release"]
fn fixed32_parse_display_round_trip() {
    use core::fmt::Write;
    parallel(i64::from(i32::MIN), i64::from(i32::MAX) + 1, |raw| {
        let x = FixedFloat32::from_bits(raw as i32);
        let mut buf = Buf {
            bytes: [0; 64],
            len: 0,
        };
        write!(buf, "{x}").unwrap();
        let text = core::str::from_utf8(&buf.bytes[..buf.len]).unwrap();
        assert_eq!(text.parse::<FixedFloat32>(), Ok(x), "{text}");
    });
}
