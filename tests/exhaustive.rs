//! Exhaustive tests against a reference written independently of the library
//! kernels (exact quotient and remainder on `i128`).
//!
//! `FixedFloat8`: every pair for every binary operation, every value for unary
//! operations, formatting and parsing. `FixedFloat16`: every value for unary
//! operations; every pair for binary operations runs only with `--ignored`
//! (2^32 pairs, nightly CI). `FixedFloat32`: `parse(display(x)) = x` for
//! every value, also only with `--ignored`.

#![cfg(not(feature = "strict-overflow"))]

#[macro_use]
mod common;

use common::*;
use fulcrum::{FixedFloat16, FixedFloat32, FixedFloat8};

#[test]
fn fixed8_all_pairs() {
    for a in i8::MIN..=i8::MAX {
        for b in i8::MIN..=i8::MAX {
            check_pair!(FixedFloat8, 8, 4, a, b);
        }
    }
}

#[test]
fn fixed8_all_values() {
    for a in i8::MIN..=i8::MAX {
        check_unary!(FixedFloat8, 8, 4, a);
    }
}

#[test]
fn fixed16_all_values() {
    for a in i16::MIN..=i16::MAX {
        check_unary!(FixedFloat16, 16, 8, a);
    }
}

#[test]
fn fixed8_parse_rounding_below_ulp() {
    for extra in 1..=6u32 {
        let lim = 1i32 << (7 + extra);
        for raw in -lim - 64..lim + 64 {
            let text = exact_decimal(raw as i128, 4 + extra);
            let expected = ref_round_div(raw as i128, 1 << extra);
            let parsed = text.parse::<FixedFloat8>();
            if fits(expected, 8) {
                assert_eq!(
                    parsed.map(|v| v.to_bits() as i128),
                    Ok(expected),
                    "parse {}",
                    text
                );
            } else {
                assert!(parsed.is_err(), "parse {} should overflow", text);
            }
            let long = format!(
                "{}{}",
                if text.contains('.') {
                    text.clone()
                } else {
                    format!("{}.", text)
                },
                "0".repeat(40)
            );
            assert_eq!(
                long.parse::<FixedFloat8>(),
                parsed,
                "trailing zeros {}",
                long
            );
            let sticky = format!(
                "{}{}1",
                if text.contains('.') {
                    text.clone()
                } else {
                    format!("{}.", text)
                },
                "0".repeat(40)
            );
            let nudged = if raw < 0 {
                ref_round_div(raw as i128 * 2 - 1, 1 << (extra + 1))
            } else {
                ref_round_div(raw as i128 * 2 + 1, 1 << (extra + 1))
            };
            let parsed_sticky = sticky.parse::<FixedFloat8>();
            if fits(nudged, 8) {
                assert_eq!(
                    parsed_sticky.map(|v| v.to_bits() as i128),
                    Ok(nudged),
                    "sticky {}",
                    sticky
                );
            }
        }
    }
}

#[test]
#[ignore = "2^32 pairs: run with --ignored --release"]
fn fixed16_all_pairs() {
    let threads = std::thread::available_parallelism().map_or(4, |n| n.get());
    let chunk = (1usize << 16) / threads + 1;
    let handles: Vec<_> = (0..threads)
        .map(|t| {
            std::thread::spawn(move || {
                let start = i16::MIN as i32 + (t * chunk) as i32;
                let end = (start + chunk as i32).min(i16::MAX as i32 + 1);
                for a in start..end {
                    let a = a as i16;
                    for b in i16::MIN..=i16::MAX {
                        check_pair!(FixedFloat16, 16, 8, a, b);
                    }
                }
            })
        })
        .collect();
    for h in handles {
        h.join().unwrap();
    }
}

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
    let threads = std::thread::available_parallelism().map_or(4, |n| n.get()) as u64;
    let chunk = (1u64 << 32) / threads + 1;
    let handles: Vec<_> = (0..threads)
        .map(|t| {
            std::thread::spawn(move || {
                let start = i32::MIN as i64 + (t * chunk) as i64;
                let end = (start + chunk as i64).min(i32::MAX as i64 + 1);
                let mut buf = Buf {
                    bytes: [0; 64],
                    len: 0,
                };
                for raw in start..end {
                    let x = FixedFloat32::from_bits(raw as i32);
                    buf.len = 0;
                    write!(buf, "{}", x).unwrap();
                    let text = core::str::from_utf8(&buf.bytes[..buf.len]).unwrap();
                    assert_eq!(text.parse::<FixedFloat32>(), Ok(x), "{}", text);
                }
            })
        })
        .collect();
    for h in handles {
        h.join().unwrap();
    }
}
