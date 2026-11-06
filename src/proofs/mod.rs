//! Kani proof harnesses (docs/ARCHITECTURE.md §6.1.2).
//!
//! Run with `cargo kani`. Never compiled by a normal build. Kani also checks
//! every arithmetic operation for overflow, so each harness proves "never
//! panics" in addition to its assertions.
//!
//! The reference rounding below is written independently of the kernels:
//! exact quotient and remainder instead of a shifted sum.

use crate::{Accumulator8, FixedFloat16, FixedFloat32, FixedFloat64, FixedFloat8};

macro_rules! reference {
    ($R:ty, $round_div:ident, $round_shift:ident) => {
        #[allow(dead_code)]
        fn $round_div(n: $R, d: $R) -> $R {
            let (n, d) = if d < 0 { (-n, -d) } else { (n, d) };
            let q = n.div_euclid(d);
            let r = n.rem_euclid(d);
            if 2 * r >= d {
                q + 1
            } else {
                q
            }
        }

        #[allow(dead_code)]
        fn $round_shift(n: $R, f: u32) -> $R {
            let q = n >> f;
            let r = n & ((1 << f) - 1);
            if r >= 1 << (f - 1) {
                q + 1
            } else {
                q
            }
        }
    };
}

reference!(i32, ref_round_div_32, ref_round_shift_32);
reference!(i64, ref_round_div_64, ref_round_shift_64);

fn saturate(v: i128, bits: u32) -> i128 {
    let min = -(1i128 << (bits - 1));
    let max = (1i128 << (bits - 1)) - 1;
    if v > max {
        max
    } else if v < min {
        min
    } else {
        v
    }
}

macro_rules! mul_spec {
    ($name:ident, $T:ident, $Bits:ty, $R:ty, $shift:ident, $bits:expr, $f:expr) => {
        #[kani::proof]
        fn $name() {
            let a: $Bits = kani::any();
            let b: $Bits = kani::any();
            let x = $T::from_bits(a);
            let y = $T::from_bits(b);
            let exact = $shift(a as $R * b as $R, $f) as i128;
            let expected = saturate(exact, $bits);
            assert_eq!(x.saturating_mul(y).to_bits() as i128, expected);
            assert_eq!(x.checked_mul(y).is_some(), expected == exact);
            assert_eq!(x.wrapping_mul(y).to_bits(), exact as $Bits);
        }
    };
}

macro_rules! div_spec {
    ($name:ident, $T:ident, $Bits:ty, $R:ty, $div:ident, $bits:expr, $f:expr) => {
        #[kani::proof]
        fn $name() {
            let a: $Bits = kani::any();
            let b: $Bits = kani::any();
            let x = $T::from_bits(a);
            let y = $T::from_bits(b);
            if b == 0 {
                let expected = if a > 0 {
                    $T::MAX
                } else if a < 0 {
                    $T::MIN
                } else {
                    $T::ZERO
                };
                assert_eq!(x.saturating_div(y), expected);
                assert!(x.checked_div(y).is_none());
                assert_eq!(x.saturating_rem(y), $T::ZERO);
            } else {
                let exact = $div((a as $R) << $f, b as $R) as i128;
                let expected = saturate(exact, $bits);
                assert_eq!(x.saturating_div(y).to_bits() as i128, expected);
                assert_eq!(x.checked_div(y).is_some(), expected == exact);
                assert_eq!(x.saturating_rem(y).to_bits(), a.wrapping_rem(b));
            }
        }
    };
}

macro_rules! add_round_spec {
    ($name:ident, $T:ident, $Bits:ty, $bits:expr, $f:expr) => {
        #[kani::proof]
        fn $name() {
            let a: $Bits = kani::any();
            let b: $Bits = kani::any();
            let x = $T::from_bits(a);
            let y = $T::from_bits(b);
            let one = 1i128 << $f;
            let (ra, rb) = (a as i128, b as i128);

            assert_eq!((x + y).to_bits() as i128, saturate(ra + rb, $bits));
            assert_eq!((x - y).to_bits() as i128, saturate(ra - rb, $bits));
            assert_eq!((-x).to_bits() as i128, saturate(-ra, $bits));
            assert_eq!(x.abs().to_bits() as i128, saturate(ra.abs(), $bits));
            assert_eq!(x.midpoint(y).to_bits() as i128, (ra + rb + 1).div_euclid(2));

            let floor = ra.div_euclid(one) * one;
            let ceil = -((-ra).div_euclid(one) * one);
            assert_eq!(x.floor().to_bits() as i128, floor);
            assert_eq!(x.ceil().to_bits() as i128, saturate(ceil, $bits));
            assert_eq!(
                x.trunc().to_bits() as i128,
                if ra < 0 { ceil } else { floor }
            );
            assert_eq!(x.int_part() as i128, ra.div_euclid(one));
            assert_eq!(x.frac_part() as i128, ra.rem_euclid(one));
            assert_eq!($T::from_parts(x.int_part(), x.frac_part()), x);
            assert_eq!($T::from_le_bytes(x.to_le_bytes()), x);
            assert_eq!($T::from_be_bytes(x.to_be_bytes()), x);
        }
    };
}

mul_spec!(mul_spec_8, FixedFloat8, i8, i32, ref_round_shift_32, 8, 4);
mul_spec!(
    mul_spec_16,
    FixedFloat16,
    i16,
    i32,
    ref_round_shift_32,
    16,
    8
);
mul_spec!(
    mul_spec_32,
    FixedFloat32,
    i32,
    i64,
    ref_round_shift_64,
    32,
    16
);

div_spec!(div_spec_8, FixedFloat8, i8, i32, ref_round_div_32, 8, 4);

add_round_spec!(add_round_spec_8, FixedFloat8, i8, 8, 4);
add_round_spec!(add_round_spec_16, FixedFloat16, i16, 16, 8);
add_round_spec!(add_round_spec_32, FixedFloat32, i32, 32, 16);
add_round_spec!(add_round_spec_64, FixedFloat64, i64, 64, 32);

#[kani::proof]
#[kani::unwind(10)]
fn parse_never_panics_8() {
    let bytes: [u8; 8] = kani::any();
    let len: usize = kani::any();
    kani::assume(len <= 8);
    if let Ok(s) = core::str::from_utf8(&bytes[..len]) {
        if let Ok(v) = FixedFloat8::parse(s) {
            let _ = v.to_bits();
        }
    }
}

#[kani::proof]
fn accumulator_order_independent_8() {
    let a: i8 = kani::any();
    let b: i8 = kani::any();
    let c: i8 = kani::any();
    let (x, y, z) = (
        FixedFloat8::from_bits(a),
        FixedFloat8::from_bits(b),
        FixedFloat8::from_bits(c),
    );
    let mut p = Accumulator8::new();
    p.add(x);
    p.add(y);
    p.add(z);
    let mut q = Accumulator8::new();
    q.add(z);
    q.add(x);
    q.add(y);
    assert_eq!(p, q);
    let mut r1 = Accumulator8::new();
    r1.add(y);
    let mut r2 = Accumulator8::new();
    r2.add(z);
    r2.add(x);
    assert_eq!(r1.merge(r2), p);
    assert_eq!(r2.merge(r1), p);
    let exact = a as i128 + b as i128 + c as i128;
    assert_eq!(p.finish().to_bits() as i128, saturate(exact, 8));

    let mut d = Accumulator8::new();
    d.add_product(x, y);
    d.add_product(y, z);
    let dot = ref_round_shift_32(a as i32 * b as i32 + b as i32 * c as i32, 4) as i128;
    assert_eq!(d.finish().to_bits() as i128, saturate(dot, 8));
}
