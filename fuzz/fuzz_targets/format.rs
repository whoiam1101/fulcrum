//! Arbitrary value, precision, width and flags: formatting never panics, the
//! exact form is exact, a given precision is correctly rounded and the width
//! is respected.

#![no_main]

use fulcrum::{FixedFloat32, FixedFloat64};
use fulcrum_oracle::Format;
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    if data.len() < 11 {
        return;
    }
    let raw = i64::from_le_bytes(data[..8].try_into().unwrap());
    let precision = (data[8] % 48) as usize;
    let width = (data[9] % 80) as usize;
    let flags = data[10];

    let x = FixedFloat64::from_bits(raw);
    let fmt64 = Format { bits: 64, frac: 32 };
    let exact = x.to_string();
    assert!(fmt64.displays_exactly(raw as i128, &exact), "{}", exact);
    let rounded = format!("{:.*}", precision, x);
    assert!(
        fmt64.is_correctly_rounded(raw as i128, &rounded, precision as u32),
        "{}",
        rounded
    );

    let padded = match flags % 5 {
        0 => format!("{:w$.p$}", x, w = width, p = precision),
        1 => format!("{:<w$}", x, w = width),
        2 => format!("{:^w$}", x, w = width),
        3 => format!("{:*>w$}", x, w = width),
        _ => format!("{:+0w$.p$}", x, w = width, p = precision),
    };
    assert!(
        padded.chars().count() >= width,
        "{:?} width {}",
        padded,
        width
    );
    let _ = format!("{:?}", x);

    let y = FixedFloat32::from_bits(raw as i32);
    let fmt32 = Format { bits: 32, frac: 16 };
    assert!(fmt32.displays_exactly(raw as i32 as i128, &y.to_string()));
});
