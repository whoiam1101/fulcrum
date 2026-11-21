//! The angle types `Angle8` … `Angle64`: `sin` and `cos` against the
//! independent reference of `tests/common/trig.rs` (octant symmetry and the
//! full Taylor series, no table), and the conversions and wrapping arithmetic
//! against their definitions on the raw values.
//!
//! Every value of `Angle8` and `Angle16`, and of `Angle32` only with
//! `--ignored`; on these types every `sin` and `cos` is correctly rounded and
//! equals `sin_turns` and `cos_turns` of the same angle in the fixed-point
//! type. `Angle64`: edge-biased random values here and the oracle in
//! `oracle/tests/angle.rs`, which also checks `to_radians` and `from_radians`.

#![cfg(not(feature = "strict-overflow"))]

#[macro_use]
mod common;

use common::trig;
use common::*;
use fulcrum::*;

/// Checks one angle of raw value `$t` and one fixed-point value `$x`; returns
/// how many of `sin` and `cos` are correctly rounded.
macro_rules! check_angle {
    ($A:ident, $T:ident, $n:expr, $f:expr, $t:expr, $x:expr) => {{
        let a = $A::from_bits($t);
        let x = $T::from_bits($x);
        let (s, c) = (a.sin(), a.cos());
        let (rs, rc) = (
            trig::sin_turns(i128::from($t), $n),
            trig::cos_turns(i128::from($t), $n),
        );
        let (si, ci) = (i128::from(s.to_bits()), i128::from(c.to_bits()));
        assert!(trig::within_ulp(si, rs, $f), "sin {:?} = {:?}", a, s);
        assert!(trig::within_ulp(ci, rc, $f), "cos {:?} = {:?}", a, c);
        assert_eq!(a.sin_cos(), (s, c));
        assert_eq!((-a).sin(), -s, "sin odd {:?}", a);
        assert_eq!((-a).cos(), c, "cos even {:?}", a);
        assert_eq!((a + $A::QUARTER_TURN).sin(), c, "cos = sin + ¼ {:?}", a);

        let shift = $n - $f;
        let mask = (1u128 << $f) - 1;
        let turns = spec::round_shift(i128::from($t), shift) as u128 & mask;
        assert_eq!(
            a.to_turns().to_bits() as u128 & mask,
            turns,
            "to_turns {:?}",
            a
        );
        assert!(!a.to_turns().is_negative() && a.to_turns() < $T::ONE);
        let from = (($x as u128) & mask) << shift;
        assert_eq!(
            u128::from($A::from_turns(x).to_bits()),
            from,
            "from_turns {:?}",
            x
        );
        assert_eq!(
            $A::from_turns(x).to_turns().to_bits() as u128,
            ($x as u128) & mask
        );

        let r = a.to_radians();
        assert!(-$T::PI <= r && r <= $T::PI, "to_radians {:?} = {:?}", a, r);
        if a != $A::HALF_TURN {
            assert_eq!((-a).to_radians(), -r, "to_radians odd {:?}", a);
        }
        if x != $T::MIN {
            assert_eq!(
                $A::from_radians(-x),
                -$A::from_radians(x),
                "from_radians odd {:?}",
                x
            );
        }

        let signed = (((u128::from($t)) << (128 - $n)) as i128) >> (128 - $n);
        let scaled = spec::round_shift(signed * i128::from($x), $f);
        let wrap = (1u128 << $n) - 1;
        assert_eq!(
            u128::from(a.scale(x).to_bits()),
            scaled as u128 & wrap,
            "scale {:?} {:?}",
            a,
            x
        );
        assert_eq!(a * x, a.scale(x));

        let b = $A::from_bits((u128::from($t)).wrapping_mul(0x9e37_79b9_7f4a_7c15)
            as <$A as fulcrum::FixedAngle>::Bits);
        assert_eq!((a + b).to_bits(), a.to_bits().wrapping_add(b.to_bits()));
        assert_eq!((a - b).to_bits(), a.to_bits().wrapping_sub(b.to_bits()));
        let mut c2 = a;
        c2 += b;
        c2 -= b;
        assert_eq!(c2, a);

        u32::from(trig::correctly_rounded(rs, $f) == Some(si))
            + u32::from(trig::correctly_rounded(rc, $f) == Some(ci))
    }};
}

/// `from_turns(x).sin() = x.sin_turns()` and the same for `cos`, on a width
/// where both are correctly rounded.
macro_rules! check_same_as_turns {
    ($A:ident, $T:ident, $x:expr) => {{
        let x = $T::from_bits($x);
        let a = $A::from_turns(x);
        assert_eq!(a.sin(), x.sin_turns(), "sin {:?}", x);
        assert_eq!(a.cos(), x.cos_turns(), "cos {:?}", x);
    }};
}

#[test]
fn constants() {
    assert_eq!(
        Angle8::QUARTER_TURN.sin_cos(),
        (FixedFloat8::ONE, FixedFloat8::ZERO)
    );
    assert_eq!(Angle16::HALF_TURN.cos(), -FixedFloat16::ONE);
    assert_eq!(
        Angle32::ZERO.sin_cos(),
        (FixedFloat32::ZERO, FixedFloat32::ONE)
    );
    assert_eq!(Angle64::HALF_TURN.to_radians(), -FixedFloat64::PI);
    assert_eq!(Angle64::QUARTER_TURN.to_radians(), FixedFloat64::FRAC_PI_2);
    assert_eq!(Angle64::from_turns(ff64!(1.25)), Angle64::QUARTER_TURN);
    assert_eq!(Angle16::HALF_TURN + Angle16::HALF_TURN, Angle16::ZERO);
    assert_eq!(Angle8::DELTA.to_bits(), 1);
    assert_eq!(Angle64::BITS, 64);
    assert_eq!(Angle32::QUARTER_TURN.scale(ff32!(-2)), Angle32::HALF_TURN);
    assert_eq!(Angle16::QUARTER_TURN.to_turns(), ff16!(0.25));
    assert_eq!(
        (Angle8::HALF_TURN - Angle8::DELTA).to_radians(),
        FixedFloat8::PI
    );
    assert_eq!(
        (Angle64::HALF_TURN - Angle64::DELTA).to_radians(),
        FixedFloat64::PI
    );
    let mut a = Angle32::QUARTER_TURN;
    a *= ff32!(3);
    assert_eq!(a, -Angle32::QUARTER_TURN);
}

#[test]
fn angle8_all_values() {
    let mut rounded = 0;
    for t in u8::MIN..=u8::MAX {
        rounded += check_angle!(Angle8, FixedFloat8, 8, 4, t, t as i8);
        check_same_as_turns!(Angle8, FixedFloat8, t as i8);
    }
    assert_eq!(rounded, 2 * 256);
}

#[test]
fn angle16_all_values() {
    let mut rounded = 0;
    for t in u16::MIN..=u16::MAX {
        rounded += check_angle!(Angle16, FixedFloat16, 16, 8, t, t as i16);
        check_same_as_turns!(Angle16, FixedFloat16, t as i16);
    }
    assert_eq!(rounded, 2 * 65536);
}

/// Every value of `Angle32`, on every available thread.
#[test]
#[ignore = "exhaustive over 2^32 values, minutes on every core: the weekly run"]
fn angle32_all_values() {
    let rounded = parallel_sum(0, 1 << 32, |t| {
        let t = t as u32;
        let r = u64::from(check_angle!(Angle32, FixedFloat32, 32, 16, t, t as i32));
        check_same_as_turns!(Angle32, FixedFloat32, t as i32);
        r
    });
    assert_eq!(rounded, 2 << 32);
}

macro_rules! random_values {
    ($module:ident, $A:ident, $T:ident, $U:ident, $Raw:ident, $n:tt, $f:tt) => {
        #[test]
        fn $module() {
            for_random_edges!(59, 200_000, $n, $f, |t: $U, x: $Raw| check_angle!(
                $A, $T, $n, $f, t, x
            ));
        }
    };
}

random_values!(random8, Angle8, FixedFloat8, u8, i8, 8, 4);
random_values!(random16, Angle16, FixedFloat16, u16, i16, 16, 8);
random_values!(random32, Angle32, FixedFloat32, u32, i32, 32, 16);
random_values!(random64, Angle64, FixedFloat64, u64, i64, 64, 32);

fn generic_sin_cos<A: FixedAngle>(a: A) -> (A::Fixed, A::Fixed) {
    a.sin_cos()
}

fn generic_angle<T: FixedFloat>(x: T) -> T::Angle {
    T::Angle::from_radians(x) + T::Angle::from_turns(x)
}

#[test]
fn trait_angle() {
    let a = Angle32::from_bits(0x1234_5678);
    assert_eq!(generic_sin_cos(a), a.sin_cos());
    let x = ff64!(-2.5);
    assert_eq!(
        generic_angle(x),
        Angle64::from_radians(x) + Angle64::from_turns(x)
    );
    assert_eq!(FixedAngle::to_turns(a), a.to_turns());
    assert_eq!(FixedAngle::to_radians(a), a.to_radians());
    assert_eq!(FixedAngle::scale(a, ff32!(3)), a.scale(ff32!(3)));
    assert_eq!(generic_rotate(Angle16::HALF_TURN), -Angle16::QUARTER_TURN);
}

fn generic_rotate<A: FixedAngle>(a: A) -> A {
    let half = A::Fixed::HALF;
    let b = A::from_bits(A::QUARTER_TURN.to_bits()) * half + a * half;
    assert_eq!((b.sin(), b.cos()), b.sin_cos(), "sin_cos {b:?}");
    b - A::QUARTER_TURN * half + A::ZERO - A::DELTA + A::DELTA
}
