//! Kani proof harnesses (docs/ARCHITECTURE.md §6.1.2).
//!
//! Run with `cargo kani`. Never compiled by a normal build. Kani also checks
//! every arithmetic operation for overflow, so each harness proves "never
//! panics" in addition to its assertions.
//!
//! The reference rounding below is written independently of the kernels:
//! exact quotient and remainder instead of a shifted sum.

use core::convert::TryFrom;

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

/// `round(n / 2^s)`, ties toward `+∞`, as `⌊(2n + 2^s) / 2^(s+1)⌋`.
fn ref_shr_round(n: i128, s: u32) -> i128 {
    (2 * n + (1i128 << s)).div_euclid(1i128 << (s + 1))
}

macro_rules! rounding_spec {
    ($name:ident, $T:ident, $Bits:ty, $bits:expr, $f:expr) => {
        #[kani::proof]
        fn $name() {
            let a: $Bits = kani::any();
            let x = $T::from_bits(a);
            let ra = a as i128;
            let one = 1i128 << $f;
            let q = ra.div_euclid(one);
            let r = ra.rem_euclid(one);
            let away = if ra >= 0 {
                (ra + one / 2).div_euclid(one) * one
            } else {
                -((-ra + one / 2).div_euclid(one) * one)
            };
            let even = if 2 * r > one || (2 * r == one && q % 2 != 0) {
                (q + 1) * one
            } else {
                q * one
            };
            let ceil = -((-ra).div_euclid(one));
            assert_eq!(x.round().to_bits() as i128, saturate(away, $bits));
            assert_eq!(x.checked_round().is_some(), saturate(away, $bits) == away);
            assert_eq!(x.round_ties_even().to_bits() as i128, saturate(even, $bits));
            assert_eq!(
                x.checked_round_ties_even().is_some(),
                saturate(even, $bits) == even
            );
            assert_eq!(x.to_int_floor() as i128, q);
            assert_eq!(x.to_int_ceil() as i128, ceil);
            assert_eq!(x.to_int_trunc() as i128, if ra < 0 { ceil } else { q });
            assert_eq!(x.to_int_round() as i128, away / one);
            assert_eq!(x.to_int_round_ties_even() as i128, even / one);
        }
    };
}

macro_rules! shift_spec {
    ($name:ident, $T:ident, $Bits:ty, $bits:expr) => {
        #[kani::proof]
        fn $name() {
            let a: $Bits = kani::any();
            let n: u32 = kani::any();
            let x = $T::from_bits(a);
            let ra = a as i128;
            if n < $bits {
                let exact = ra << n;
                assert_eq!(
                    x.saturating_shl(n).to_bits() as i128,
                    saturate(exact, $bits)
                );
                assert_eq!(x.checked_shl(n).is_some(), saturate(exact, $bits) == exact);
                assert_eq!(x.wrapping_shl(n).to_bits(), exact as $Bits);
                assert_eq!(x.shr_round(n).to_bits() as i128, ref_shr_round(ra, n));
            } else {
                assert_eq!(
                    x.saturating_shl(n).to_bits() as i128,
                    saturate(ra.signum() << 100, $bits)
                );
                assert_eq!(x.checked_shl(n).is_some(), a == 0);
                assert_eq!(x.wrapping_shl(n), $T::ZERO);
                assert_eq!(x.shr_round(n), $T::ZERO);
            }
        }
    };
}

macro_rules! mul_int_spec {
    ($name:ident, $T:ident, $Bits:ty, $bits:expr) => {
        #[kani::proof]
        fn $name() {
            let a: $Bits = kani::any();
            let m: $Bits = kani::any();
            let x = $T::from_bits(a);
            let exact = a as i128 * m as i128;
            assert_eq!(x.mul_int(m).to_bits() as i128, saturate(exact, $bits));
            assert_eq!(
                x.checked_mul_int(m).is_some(),
                saturate(exact, $bits) == exact
            );
            assert_eq!(x.wrapping_mul_int(m).to_bits(), exact as $Bits);
        }
    };
}

macro_rules! narrow_spec {
    ($name:ident, $Big:ident, $BigBits:ty, $big_f:expr, $Small:ident, $SmallBits:ty, $bits:expr, $f:expr) => {
        #[kani::proof]
        fn $name() {
            let a: $BigBits = kani::any();
            let x = $Big::from_bits(a);
            let exact = ref_shr_round(a as i128, $big_f - $f);
            let expected = saturate(exact, $bits);
            assert_eq!($Small::saturating_from(x).to_bits() as i128, expected);
            assert_eq!($Small::wrapping_from(x).to_bits(), exact as $SmallBits);
            match $Small::try_from(x) {
                Ok(v) => assert_eq!(v.to_bits() as i128, exact),
                Err(_) => assert!(expected != exact),
            }
            let s: $SmallBits = kani::any();
            let small = $Small::from_bits(s);
            let wide = $Big::from_bits((s as $BigBits) << ($big_f - $f));
            assert_eq!($Big::from(small), wide);
            assert_eq!($Big::saturating_from(small), wide);
            assert_eq!($Big::wrapping_from(small), wide);
            assert_eq!($Small::try_from(wide), Ok(small));
        }
    };
}

macro_rules! from_int_spec {
    ($name:ident, $T:ident, $bits:expr, $f:expr) => {
        #[kani::proof]
        fn $name() {
            let n: i128 = kani::any();
            let lo = -(1i128 << ($bits - 1 - $f));
            let hi = (1i128 << ($bits - 1 - $f)) - 1;
            let expected = if n < lo {
                $T::MIN
            } else if n > hi {
                $T::MAX
            } else {
                $T::from_bits((n << $f) as _)
            };
            assert_eq!($T::saturating_from_int(n), expected);
            assert_eq!($T::checked_from_int(n).is_some(), n >= lo && n <= hi);
            let w: i64 = kani::any();
            assert_eq!($T::try_from(w).ok(), $T::checked_from_int(w as i128));
            let u: u128 = kani::any();
            if u > hi as u128 {
                assert!($T::try_from(u).is_err());
            }
        }
    };
}

#[kani::proof]
fn ratio_and_div_int_spec_8() {
    let a: i8 = kani::any();
    let b: i8 = kani::any();
    let x = FixedFloat8::from_bits(a);
    if b == 0 {
        let expected = if a > 0 {
            FixedFloat8::MAX
        } else if a < 0 {
            FixedFloat8::MIN
        } else {
            FixedFloat8::ZERO
        };
        assert_eq!(FixedFloat8::saturating_from_ratio(a, b), expected);
        assert_eq!(x.div_int(b), expected);
        assert!(FixedFloat8::checked_from_ratio(a, b).is_none());
        assert!(x.checked_div_int(b).is_none());
    } else {
        let ratio = ref_round_div_32((a as i32) << 4, b as i32) as i128;
        assert_eq!(
            FixedFloat8::saturating_from_ratio(a, b).to_bits() as i128,
            saturate(ratio, 8)
        );
        assert_eq!(
            FixedFloat8::checked_from_ratio(a, b).is_some(),
            saturate(ratio, 8) == ratio
        );
        let quotient = ref_round_div_32(a as i32, b as i32) as i128;
        assert_eq!(x.div_int(b).to_bits() as i128, saturate(quotient, 8));
        assert_eq!(
            x.checked_div_int(b).is_some(),
            saturate(quotient, 8) == quotient
        );
    }
}

add_round_spec!(add_round_spec_8, FixedFloat8, i8, 8, 4);
add_round_spec!(add_round_spec_16, FixedFloat16, i16, 16, 8);
add_round_spec!(add_round_spec_32, FixedFloat32, i32, 32, 16);
add_round_spec!(add_round_spec_64, FixedFloat64, i64, 64, 32);

rounding_spec!(rounding_spec_8, FixedFloat8, i8, 8, 4);
rounding_spec!(rounding_spec_16, FixedFloat16, i16, 16, 8);
rounding_spec!(rounding_spec_32, FixedFloat32, i32, 32, 16);
rounding_spec!(rounding_spec_64, FixedFloat64, i64, 64, 32);

shift_spec!(shift_spec_8, FixedFloat8, i8, 8);
shift_spec!(shift_spec_16, FixedFloat16, i16, 16);
shift_spec!(shift_spec_32, FixedFloat32, i32, 32);
shift_spec!(shift_spec_64, FixedFloat64, i64, 64);

mul_int_spec!(mul_int_spec_8, FixedFloat8, i8, 8);
mul_int_spec!(mul_int_spec_16, FixedFloat16, i16, 16);
mul_int_spec!(mul_int_spec_32, FixedFloat32, i32, 32);

narrow_spec!(
    narrow_spec_16_8,
    FixedFloat16,
    i16,
    8,
    FixedFloat8,
    i8,
    8,
    4
);
narrow_spec!(
    narrow_spec_32_8,
    FixedFloat32,
    i32,
    16,
    FixedFloat8,
    i8,
    8,
    4
);
narrow_spec!(
    narrow_spec_32_16,
    FixedFloat32,
    i32,
    16,
    FixedFloat16,
    i16,
    16,
    8
);
narrow_spec!(
    narrow_spec_64_8,
    FixedFloat64,
    i64,
    32,
    FixedFloat8,
    i8,
    8,
    4
);
narrow_spec!(
    narrow_spec_64_16,
    FixedFloat64,
    i64,
    32,
    FixedFloat16,
    i16,
    16,
    8
);
narrow_spec!(
    narrow_spec_64_32,
    FixedFloat64,
    i64,
    32,
    FixedFloat32,
    i32,
    32,
    16
);

from_int_spec!(from_int_spec_8, FixedFloat8, 8, 4);
from_int_spec!(from_int_spec_16, FixedFloat16, 16, 8);
from_int_spec!(from_int_spec_32, FixedFloat32, 32, 16);
from_int_spec!(from_int_spec_64, FixedFloat64, 64, 32);

/// `double` never panics and keeps every digit at most 9, for any `k ≤ 65`.
#[kani::proof]
#[kani::unwind(67)]
#[kani::solver(cadical)]
fn double_spec() {
    let digits: crate::parse::Digits = kani::any();
    let k: usize = kani::any();
    kani::assume(k <= digits.len());
    let mut i = 0;
    while i < digits.len() {
        kani::assume(digits[i] <= 9);
        i += 1;
    }
    let (doubled, _) = crate::parse::double(digits, k);
    let mut i = 0;
    while i < doubled.len() {
        assert!(doubled[i] <= 9);
        i += 1;
    }
}

/// Asserts that every digit is at most 9: the precondition of `double` and
/// `fraction_bits`, checked at every replaced call.
fn assert_digits(digits: &crate::parse::Digits) {
    let mut i = 0;
    while i < digits.len() {
        assert!(digits[i] <= 9);
        i += 1;
    }
}

/// Replaces `double` in `fraction_bits_spec` by its proven contract
/// (`double_spec`): checks the precondition, then returns any digits at most 9
/// and any carry.
fn double_contract(input: crate::parse::Digits, k: usize) -> (crate::parse::Digits, bool) {
    assert_digits(&input);
    assert!(k <= input.len());
    let digits: crate::parse::Digits = kani::any();
    let mut i = 0;
    while i < digits.len() {
        kani::assume(digits[i] <= 9);
        i += 1;
    }
    (digits, kani::any())
}

/// `fraction_bits` never panics and returns fewer than `keep` bits, for any
/// digits at most 9 and any `k ≤ keep`, with `keep = F + 1` of every width.
macro_rules! fraction_bits_spec {
    ($name:ident, $keep:expr) => {
        #[kani::proof]
        #[kani::unwind(67)]
        #[kani::solver(cadical)]
        #[kani::stub(crate::parse::double, double_contract)]
        fn $name() {
            let digits: crate::parse::Digits = kani::any();
            let mut i = 0;
            while i < digits.len() {
                kani::assume(digits[i] <= 9);
                i += 1;
            }
            let k: usize = kani::any();
            kani::assume(k <= $keep);
            let (bits, _) = crate::parse::fraction_bits(digits, k, $keep);
            assert!(bits < 1u128 << $keep);
        }
    };
}

fraction_bits_spec!(fraction_bits_spec_8, 5);
fraction_bits_spec!(fraction_bits_spec_16, 9);
fraction_bits_spec!(fraction_bits_spec_32, 17);
fraction_bits_spec!(fraction_bits_spec_64, 33);

/// Replaces `fraction_bits` in `parse_spec` by its proven contract: checks the
/// precondition, then returns any result below `2^keep`. `fraction_bits_spec`
/// proves the contract for every width.
fn fraction_bits_contract(digits: crate::parse::Digits, k: usize, keep: usize) -> (u128, bool) {
    assert_digits(&digits);
    assert!(k <= keep && keep <= digits.len());
    let bits: u128 = kani::any();
    kani::assume(bits < 1u128 << keep);
    (bits, kani::any())
}

/// Parsing never panics on byte strings up to 64 bytes, with or without `_`
/// and an outer `-` (the `ffN!` literal path).
///
/// Every byte is a digit, `.`, `+`, `-`, `_` or `x`. This loses nothing:
/// `parse_magnitude` compares each byte only with these characters and with
/// the digit range, so any other byte takes the same path as `x`. Calling
/// `parse_bytes` directly skips UTF-8 validation, which belongs to `core`.
/// The fraction conversion is replaced by its contract, see
/// `fraction_bits_contract`.
macro_rules! parse_spec {
    ($name:ident, $T:ident) => {
        #[kani::proof]
        #[kani::unwind(66)]
        #[kani::solver(cadical)]
        #[kani::stub(crate::parse::fraction_bits, fraction_bits_contract)]
        fn $name() {
            let bytes: [u8; 64] = kani::any();
            let mut i = 0;
            while i < 64 {
                let c = bytes[i];
                kani::assume(
                    (c >= b'0' && c <= b'9')
                        || c == b'.'
                        || c == b'+'
                        || c == b'-'
                        || c == b'_'
                        || c == b'x',
                );
                i += 1;
            }
            let len: usize = kani::any();
            kani::assume(len <= 64);
            if let Ok(v) = $T::parse_bytes(&bytes[..len], kani::any(), kani::any()) {
                let _ = v.to_bits();
            }
        }
    };
}

parse_spec!(parse_never_panics_8, FixedFloat8);
parse_spec!(parse_never_panics_16, FixedFloat16);
parse_spec!(parse_never_panics_32, FixedFloat32);
parse_spec!(parse_never_panics_64, FixedFloat64);

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
