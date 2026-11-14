//! Operations on three operands, rounded once: `mul_add`, `mul_div`, `lerp`,
//! against `spec::mul_add`, `spec::mul_div` and `spec::lerp` of
//! `tests/common/reference.rs` over `i128`. Every exact intermediate
//! of these operations fits `i128` on every width up to 64 bits.
//!
//! `FixedFloat8`: every triple. Wider types: edge-biased random triples.

#![cfg(not(feature = "strict-overflow"))]

#[macro_use]
mod common;

use common::*;
use fulcrum::*;

macro_rules! check_triple {
    ($T:ident, $bits:expr, $f:expr, $a:expr, $b:expr, $c:expr) => {{
        let (ra, rb, rc): (i128, i128, i128) = ($a as i128, $b as i128, $c as i128);
        let (x, y, z) = ($T::from_bits($a), $T::from_bits($b), $T::from_bits($c));
        let ctx = || format!("{} ({:?}, {:?}, {:?})", stringify!($T), x, y, z);

        let fma = spec::mul_add(ra, rb, rc, $f);
        assert_eq!(
            x.mul_add(y, z).to_bits() as i128,
            spec::saturate(fma, $bits),
            "mul_add {}",
            ctx()
        );
        assert_eq!(
            x.checked_mul_add(y, z).map(|v| v.to_bits() as i128),
            Some(fma).filter(|&v| spec::fits(v, $bits)),
            "checked_mul_add {}",
            ctx()
        );

        if rc == 0 {
            let sign = ra.signum() * rb.signum();
            assert_eq!(
                x.mul_div(y, z).to_bits() as i128,
                spec::div_by_zero(sign, $bits),
                "mul_div0 {}",
                ctx()
            );
            assert_eq!(x.checked_mul_div(y, z), None, "checked_mul_div0 {}", ctx());
        } else {
            let q = spec::mul_div(ra, rb, rc);
            assert_eq!(
                x.mul_div(y, z).to_bits() as i128,
                spec::saturate(q, $bits),
                "mul_div {}",
                ctx()
            );
            assert_eq!(
                x.checked_mul_div(y, z).map(|v| v.to_bits() as i128),
                Some(q).filter(|&v| spec::fits(v, $bits)),
                "checked_mul_div {}",
                ctx()
            );
        }

        let lerp = spec::lerp(ra, rb, rc, $f);
        assert_eq!(
            x.lerp(y, z).to_bits() as i128,
            spec::saturate(lerp, $bits),
            "lerp {}",
            ctx()
        );
        assert_eq!(
            x.checked_lerp(y, z).map(|v| v.to_bits() as i128),
            Some(lerp).filter(|&v| spec::fits(v, $bits)),
            "checked_lerp {}",
            ctx()
        );
    }};
}

#[test]
fn fixed8_all_triples() {
    for a in i8::MIN..=i8::MAX {
        for b in i8::MIN..=i8::MAX {
            for c in i8::MIN..=i8::MAX {
                check_triple!(FixedFloat8, 8, 4, a, b, c);
            }
        }
    }
}

macro_rules! random_triples {
    (fixed8, $($rest:tt)*) => {};
    ($module:ident, $T:ident, $lit:ident, $Acc:ident, $Raw:ident, $bits:tt, $f:tt) => {{
        let mut rng = Pcg32::new(29, $bits);
        for _ in 0..200_000 {
            let a = rng.edge_bits($bits, $f) as $Raw;
            let b = rng.edge_bits($bits, $f) as $Raw;
            let c = rng.edge_bits($bits, $f) as $Raw;
            check_triple!($T, $bits, $f, a, b, c);
        }
    }};
}

#[test]
fn random_triples_on_wider_types() {
    for_each_i128_width!(random_triples!());
}

#[test]
fn mul_add_does_not_saturate_the_product() {
    type F = FixedFloat8;
    let two = F::from_bits(2 << 4);
    assert_eq!(F::MAX * two + F::MIN, F::from_bits(-1));
    assert_eq!(F::MAX.mul_add(two, F::MIN), F::from_bits(126));
    assert_eq!(F::MAX.checked_mul_add(F::MAX, F::ZERO), None);
    assert_eq!(F::MAX.mul_add(F::MAX, F::ZERO), F::MAX);
    assert_eq!(F::MIN.mul_add(F::MAX, F::ZERO), F::MIN);
}

#[test]
fn mul_div_does_not_overflow_in_between() {
    type F = FixedFloat64;
    let big = F::MAX;
    assert_eq!(big * big / big, F::MAX / F::MAX);
    assert_eq!(big.mul_div(big, big), big);
    assert_eq!(F::MIN.mul_div(F::MAX, F::MAX), F::MIN);
    assert_eq!(
        F::ONE.mul_div(F::ONE, F::from(3i8)).to_string(),
        "0.33333333325572311878204345703125"
    );
    assert_eq!(F::ONE.mul_div(-F::ONE, F::ZERO), F::MIN);
    assert_eq!(F::ZERO.mul_div(F::ONE, F::ZERO), F::ZERO);
}

#[test]
fn lerp_hits_both_ends_and_extrapolates() {
    type F = FixedFloat32;
    let (a, b) = (F::MIN, F::MAX);
    assert_eq!(a.lerp(b, F::ZERO), a);
    assert_eq!(a.lerp(b, F::ONE), b);
    assert_eq!(a.lerp(b, F::HALF), F::from_bits(0));
    assert_eq!(F::ONE.lerp(F::from(3i8), F::from(2i8)), F::from(5i8));
    assert_eq!(F::ONE.lerp(F::from(3i8), -F::ONE), -F::ONE);
    assert_eq!(a.lerp(b, F::from(2i8)), F::MAX);
    assert_eq!(a.checked_lerp(b, F::from(2i8)), None);
}
