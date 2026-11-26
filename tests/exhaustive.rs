//! Exhaustive tests against a reference written independently of the library
//! kernels (exact quotient and remainder on `i128`).
//!
//! `FixedFloat8`: every pair for every binary operation, every value for unary
//! operations, formatting and parsing. `FixedFloat16`: every value for unary
//! operations. Every pair of 16 bits is not run: the kernel behind the binary
//! operations is proven by Lean (`verify/lean/Fulcrum/L3/`).
//! `parse(display(x)) = x` of every `FixedFloat32` is in `round_trip.rs`.

#![cfg(not(feature = "strict-overflow"))]

#[macro_use]
mod common;

use common::*;
use fulcrum::{FixedFloat16, FixedFloat8};

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
            let text = exact_decimal(i128::from(raw), 4 + extra);
            let expected = spec::round_div(i128::from(raw), 1 << extra);
            let parsed = text.parse::<FixedFloat8>();
            if spec::fits(expected, 8) {
                assert_eq!(
                    parsed.map(|v| i128::from(v.to_bits())),
                    Ok(expected),
                    "parse {text}"
                );
            } else {
                assert!(parsed.is_err(), "parse {text} should overflow");
            }
            let long = format!(
                "{}{}",
                if text.contains('.') {
                    text.clone()
                } else {
                    format!("{text}.")
                },
                "0".repeat(40)
            );
            assert_eq!(long.parse::<FixedFloat8>(), parsed, "trailing zeros {long}");
            let sticky = format!(
                "{}{}1",
                if text.contains('.') {
                    text.clone()
                } else {
                    format!("{text}.")
                },
                "0".repeat(40)
            );
            let nudged = if raw < 0 {
                spec::round_div(i128::from(raw) * 2 - 1, 1 << (extra + 1))
            } else {
                spec::round_div(i128::from(raw) * 2 + 1, 1 << (extra + 1))
            };
            let parsed_sticky = sticky.parse::<FixedFloat8>();
            if spec::fits(nudged, 8) {
                assert_eq!(
                    parsed_sticky.map(|v| i128::from(v.to_bits())),
                    Ok(nudged),
                    "sticky {sticky}"
                );
            }
        }
    }
}
