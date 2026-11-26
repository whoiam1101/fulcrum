//! Square roots: `sqrt`, `rsqrt`, `hypot` and their `checked_*` variants
//! against `spec::sqrt_ratio` of `tests/common/reference.rs` over `i128`, a
//! binary search and the definition of rounding to nearest, independent of
//! the Newton iteration of the kernel. All three are correctly rounded.
//!
//! `FixedFloat8`: every value and every pair. `FixedFloat16`: every value.
//! Wider types: edge-biased random values; `hypot` of `FixedFloat64`
//! squares beyond `i128` and is checked by the rational oracle
//! (`oracle/tests/ops.rs`). The kernel behind all three is proven by Lean on
//! every width (`verify/lean/Fulcrum/L5/Length.lean`).

#![cfg(not(feature = "strict-overflow"))]

#[macro_use]
mod common;

use common::*;
use fulcrum::*;

macro_rules! check_roots {
    ($T:ident, $bits:expr, $f:expr, $a:expr) => {{
        let ra = i128::from($a);
        let x = $T::from_bits($a);

        let (sqrt, checked_sqrt) = if ra < 0 {
            (0, None)
        } else {
            let s = spec::sqrt(ra << $f);
            (s, Some(s))
        };
        assert_eq!(i128::from(x.sqrt().to_bits()), sqrt, "sqrt {:?}", x);
        assert_eq!(
            x.checked_sqrt().map(|v| i128::from(v.to_bits())),
            checked_sqrt,
            "checked_sqrt {:?}",
            x
        );
        assert_eq!(
            i128::from(generic_sqrt(x).to_bits()),
            sqrt,
            "FixedFloat::sqrt {:?}",
            x
        );

        let (rsqrt, checked_rsqrt) = if ra <= 0 {
            (spec::div_by_zero(1, $bits), None)
        } else {
            let s = spec::sqrt_ratio(1 << (3 * $f), ra);
            assert!(spec::fits(s, $bits), "rsqrt {:?} out of range", x);
            (s, Some(s))
        };
        assert_eq!(i128::from(x.rsqrt().to_bits()), rsqrt, "rsqrt {:?}", x);
        assert_eq!(
            x.checked_rsqrt().map(|v| i128::from(v.to_bits())),
            checked_rsqrt,
            "checked_rsqrt {:?}",
            x
        );
    }};
}

macro_rules! check_hypot {
    ($T:ident, $bits:expr, $a:expr, $b:expr) => {{
        let (ra, rb) = (i128::from($a), i128::from($b));
        let (x, y) = ($T::from_bits($a), $T::from_bits($b));
        let h = spec::sqrt(ra * ra + rb * rb);
        assert_eq!(
            i128::from(x.hypot(y).to_bits()),
            spec::saturate(h, $bits),
            "hypot {:?} {:?}",
            x,
            y
        );
        assert_eq!(
            x.checked_hypot(y).map(|v| i128::from(v.to_bits())),
            Some(h).filter(|&v| spec::fits(v, $bits)),
            "checked_hypot {:?} {:?}",
            x,
            y
        );
    }};
}

fn generic_sqrt<T: FixedFloat>(x: T) -> T {
    x.sqrt()
}

#[test]
fn fixed8_all_values_and_pairs() {
    for a in i8::MIN..=i8::MAX {
        check_roots!(FixedFloat8, 8, 4, a);
        for b in i8::MIN..=i8::MAX {
            check_hypot!(FixedFloat8, 8, a, b);
        }
    }
}

#[test]
fn fixed16_all_values() {
    for a in i16::MIN..=i16::MAX {
        check_roots!(FixedFloat16, 16, 8, a);
    }
}

macro_rules! random_values {
    (fixed8, $($rest:tt)*) => {};
    ($module:ident, $T:ident, $lit:ident, $Acc:ident, $Raw:ident, $bits:tt, $f:tt) => {{
        for_random_edges!(31, 100_000, $bits, $f, |a: $Raw, b: $Raw| {
            check_roots!($T, $bits, $f, a);
            if $bits < 64 {
                check_hypot!($T, $bits, a, b);
            }
        })
    }};
}

#[test]
fn random_values_on_wider_types() {
    for_each_width!(random_values!());
}

macro_rules! known_values {
    ($module:ident, $T:ident, $lit:ident, $Acc:ident, $Raw:ident, $bits:tt, $f:tt) => {
        mod $module {
            use super::*;

            #[test]
            fn exact_squares_and_constants() {
                let two = $lit!(2);
                assert_eq!($lit!(4).sqrt(), two);
                assert_eq!($lit!(0.25).sqrt(), $T::HALF);
                assert_eq!($T::ZERO.sqrt(), $T::ZERO);
                assert_eq!($T::ONE.sqrt(), $T::ONE);
                assert_eq!(two.sqrt(), $T::SQRT_2);
                assert_eq!($lit!(3).sqrt(), $T::SQRT_3);
                assert_eq!($lit!(4).rsqrt(), $T::HALF);
                assert_eq!(two.rsqrt(), $T::FRAC_1_SQRT_2);
                assert_eq!($lit!(3).hypot($lit!(-4)), $lit!(5));
                assert_eq!($lit!(-1).hypot($lit!(1)), $T::SQRT_2);
            }

            #[test]
            fn domain_edges() {
                assert_eq!($T::NEG_ONE.sqrt(), $T::ZERO);
                assert_eq!($T::MIN.checked_sqrt(), None);
                assert_eq!($T::NEG_ONE.checked_sqrt(), None);
                assert_eq!($T::ZERO.rsqrt(), $T::MAX);
                assert_eq!($T::MIN.rsqrt(), $T::MAX);
                assert_eq!($T::ZERO.checked_rsqrt(), None);
                assert_eq!(
                    $T::DELTA.checked_rsqrt().map(|v| v.is_positive()),
                    Some(true)
                );
                assert_eq!($T::MAX.hypot($T::MAX), $T::MAX);
                assert_eq!($T::MAX.checked_hypot($T::ONE), None);
                assert_eq!($T::MIN.hypot($T::ZERO), $T::MAX);
                assert_eq!($T::MIN.checked_hypot($T::ZERO), None);
                assert_eq!($T::MAX.hypot($T::ZERO), $T::MAX);
                assert_eq!($T::MAX.checked_hypot($T::ZERO), Some($T::MAX));
            }
        }
    };
}

for_each_width!(known_values!());
