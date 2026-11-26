//! Kani proof harnesses.
//!
//! Run with `cargo kani`. Never compiled by a normal build. Kani also checks
//! every arithmetic operation for overflow, so each harness proves "never
//! panics" in addition to its assertions.
//!
//! The reference is `tests/common/reference.rs`, the same file the tests
//! use, over `i32` where the solver is faster and over `i128`.
//!
//! The functions of `src/kernel.rs` are proven by Lean on the extracted code
//! (`verify/lean/Fulcrum/L1`..`L5`), and no harness repeats them (`*`, `/`,
//! `div_int`, `from_ratio`, `mul_add`, `mul_div`, `lerp`, `midpoint`, `ceil`,
//! `round`, `round_ties_even`, `to_int_round*`, the shifts, `isqrt`). The
//! harnesses check the code outside the kernel: the arithmetic of `core` on the storage type
//! (`+ - neg abs`, `%`, `mul_int`), the masks and shifts of `floor`, `trunc`,
//! `to_int_floor`, `to_int_ceil`, `to_int_trunc`, the parts, the bytes, the conversions of `src/convert.rs`,
//! parsing, the accumulators and the conversions in turns.
//!
//! CI shards the harnesses of this module by name: one job each for the
//! substrings `_8`, `_16`, `_32` and `_64`, and one for the exact names
//! `double_spec`, `i256_spec` and `accumulator64_product_spec`. A new
//! harness ends with `_` and its width, so exactly one shard runs it (a
//! narrowing names its source width that way and its target without the
//! `_`: `narrow_spec_64to16`), or joins that list in
//! `.github/workflows/ci.yml`.

use core::convert::TryFrom;

use crate::{
    Accumulator8, Angle32, Angle64, FixedFloat16, FixedFloat32, FixedFloat64, FixedFloat8,
};

#[macro_use]
#[path = "../../tests/common/reference.rs"]
mod reference;

reference!(r32, i32);
reference!(r128, i128);

use r128::saturate;

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
            if b == 0 {
                assert_eq!(x.saturating_rem(y), $T::ZERO);
            } else {
                assert_eq!(x.saturating_rem(y).to_bits(), a.wrapping_rem(b));
            }

            let q = ra.div_euclid(one);
            let up = -((-ra).div_euclid(one));
            assert_eq!(x.floor().to_bits() as i128, q * one);
            assert_eq!(
                x.trunc().to_bits() as i128,
                if ra < 0 { up * one } else { q * one }
            );
            assert_eq!(x.to_int_floor() as i128, q);
            assert_eq!(x.to_int_ceil() as i128, up);
            assert_eq!(x.to_int_trunc() as i128, if ra < 0 { up } else { q });
            assert_eq!(x.int_part() as i128, q);
            assert_eq!(x.frac_part() as i128, ra.rem_euclid(one));
            assert_eq!($T::from_parts(x.int_part(), x.frac_part()), x);
            assert_eq!($T::from_le_bytes(x.to_le_bytes()), x);
            assert_eq!($T::from_be_bytes(x.to_be_bytes()), x);
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
            let exact = r128::round_shift(a as i128, $big_f - $f);
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

add_round_spec!(add_round_spec_8, FixedFloat8, i8, 8, 4);
add_round_spec!(add_round_spec_16, FixedFloat16, i16, 16, 8);
add_round_spec!(add_round_spec_32, FixedFloat32, i32, 32, 16);
add_round_spec!(add_round_spec_64, FixedFloat64, i64, 64, 32);

mul_int_spec!(mul_int_spec_8, FixedFloat8, i8, 8);
mul_int_spec!(mul_int_spec_16, FixedFloat16, i16, 16);
mul_int_spec!(mul_int_spec_32, FixedFloat32, i32, 32);

narrow_spec!(
    narrow_spec_16to8,
    FixedFloat16,
    i16,
    8,
    FixedFloat8,
    i8,
    8,
    4
);
narrow_spec!(
    narrow_spec_32to8,
    FixedFloat32,
    i32,
    16,
    FixedFloat8,
    i8,
    8,
    4
);
narrow_spec!(
    narrow_spec_32to16,
    FixedFloat32,
    i32,
    16,
    FixedFloat16,
    i16,
    16,
    8
);
narrow_spec!(
    narrow_spec_64to8,
    FixedFloat64,
    i64,
    32,
    FixedFloat8,
    i8,
    8,
    4
);
narrow_spec!(
    narrow_spec_64to16,
    FixedFloat64,
    i64,
    32,
    FixedFloat16,
    i16,
    16,
    8
);
narrow_spec!(
    narrow_spec_64to32,
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
    let dot = r32::round_shift(a as i32 * b as i32 + b as i32 * c as i32, 4) as i128;
    assert_eq!(d.finish().to_bits() as i128, saturate(dot, 8));
}

/// `I256` on full 256-bit operands: subtraction undoes addition, addition
/// commutes, the shift moves the low bits of `hi` into the top of `lo` and
/// composes; on values that fit `i128` everything agrees with `i128`.
#[kani::proof]
fn i256_spec() {
    use crate::wide::I256;
    let (lo1, hi1, lo2, hi2): (u128, i128, u128, i128) =
        (kani::any(), kani::any(), kani::any(), kani::any());
    let (u, v) = (I256::from_words(lo1, hi1), I256::from_words(lo2, hi2));
    assert_eq!(u.wrapping_add(v).wrapping_sub(v), u);
    assert_eq!(u.wrapping_add(v), v.wrapping_add(u));
    assert_eq!(u.is_negative(), hi1 < 0);

    let s: u32 = kani::any();
    kani::assume(s > 0 && s < 128);
    let (lo, hi) = u.shr(s).words();
    assert_eq!(hi, hi1 >> s);
    assert_eq!(lo << s >> s, lo1 >> s);
    assert_eq!((lo >> (128 - s)) as i128, hi1 & ((1u128 << s) - 1) as i128);
    let t: u32 = kani::any();
    kani::assume(t > 0 && t < 128 - s);
    assert_eq!(u.shr(s).shr(t), u.shr(s + t));

    let a: i128 = kani::any();
    let b: i128 = kani::any();
    let (wa, wb) = (I256::from_i128(a), I256::from_i128(b));
    assert_eq!(wa.wrapping_add(wb).to_i128(), a.checked_add(b));
    assert_eq!(wa.wrapping_sub(wb).to_i128(), a.checked_sub(b));
    assert_eq!(wa.shr(s).to_i128(), Some(a >> s));
    assert_eq!(wa.saturating_to_i128(), a);
    assert_eq!(
        u.saturating_to_i128() == i128::MAX,
        u.to_i128().map_or(hi1 >= 0, |w| w == i128::MAX)
    );
}

/// One `Accumulator64::add_product` against the independent rounding of the
/// exact product.
#[kani::proof]
fn accumulator64_product_spec() {
    let a: i64 = kani::any();
    let b: i64 = kani::any();
    let mut acc = crate::Accumulator64::new();
    acc.add_product(FixedFloat64::from_bits(a), FixedFloat64::from_bits(b));
    let expected = saturate(r128::round_shift(a as i128 * b as i128, 32), 64);
    assert_eq!(acc.finish().to_bits() as i128, expected);
    assert_eq!(
        acc.checked_finish().is_some(),
        expected == r128::round_shift(a as i128 * b as i128, 32)
    );
}

macro_rules! angle_no_panic {
    ($name:ident, $A:ident, $T:ident) => {
        /// The conversions in turns of the angle type never panic on every
        /// input. `sin`, `cos`, `scale` and the conversions in radians are
        /// proven never to fail by Lean (`verify/lean/Fulcrum/L4/Angle.lean`).
        #[kani::proof]
        fn $name() {
            let a = $A::from_bits(kani::any());
            let x = $T::from_bits(kani::any());
            let _ = (a.to_turns(), $A::from_turns(x));
        }
    };
}

angle_no_panic!(angle_no_panic_32, Angle32, FixedFloat32);
angle_no_panic!(angle_no_panic_64, Angle64, FixedFloat64);

macro_rules! vec_no_panic {
    ($name:ident, $T:ident) => {
        /// The vectors never panic outside their roots: the operators, `dot`,
        /// `length_sq`, `distance_sq`, `perp_dot` and `cross` keep their exact
        /// sums in range on every input (each product of raw values within
        /// `2^126`, the sums of `Accumulator64` in 256 bits). `length` and
        /// `distance` add only `hypot` and `hypot3` of the kernel, which Lean
        /// proves never to fail on every width
        /// (`verify/lean/Fulcrum/L5/Length.lean`).
        #[kani::proof]
        fn $name() {
            let a = crate::Vec3::new(
                $T::from_bits(kani::any()),
                $T::from_bits(kani::any()),
                $T::from_bits(kani::any()),
            );
            let b = crate::Vec3::new(
                $T::from_bits(kani::any()),
                $T::from_bits(kani::any()),
                $T::from_bits(kani::any()),
            );
            let s = $T::from_bits(kani::any());
            let (a2, b2) = (crate::Vec2::new(a.x, a.y), crate::Vec2::new(b.x, b.y));
            let _ = (a + b, a - b, -a, a * b, a * s, a / s, a.abs(), a.lerp(b, s));
            let _ = (a.dot(b), a.length_sq(), a.distance_sq(b), a.cross(b));
            let _ = (a2.dot(b2), a2.distance_sq(b2), a2.perp_dot(b2), a2.perp());
        }
    };
}

vec_no_panic!(vec_no_panic_8, FixedFloat8);
vec_no_panic!(vec_no_panic_16, FixedFloat16);
vec_no_panic!(vec_no_panic_32, FixedFloat32);
vec_no_panic!(vec_no_panic_64, FixedFloat64);
