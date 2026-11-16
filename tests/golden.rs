//! Determinism: a fixed pseudo-random sequence of operations on every width is
//! hashed, and the hash is compared to a constant committed in the repository.
//! The same constant must come out on every target, in debug and in release
//! (docs/ARCHITECTURE.md §5). Changing semantics on purpose means updating the
//! constant together with a decision log entry.

#![cfg(not(feature = "strict-overflow"))]

#[macro_use]
mod common;

use common::{Fnv, Pcg32};
use fulcrum::*;

const ROUNDS: usize = 250_000;
const GOLDEN: u64 = 0x268a_4fee_8564_c727;
const GOLDEN_VECTORS: u64 = 0x86e8_db5a_35e6_ed72;

macro_rules! mix {
    ($h:ident, $rng:ident, $module:ident, $T:ident, $lit:ident, $Acc:ident, $Raw:ident, $bits:tt, $f:tt) => {{
        let a = $T::from_bits($rng.edge_bits($bits, $T::FRAC_BITS) as _);
        let b = $T::from_bits($rng.edge_bits($bits, $T::FRAC_BITS) as _);
        for v in [
            a + b,
            a - b,
            a * b,
            a / b,
            a % b,
            a.wrapping_mul(b),
            a.wrapping_div(b),
            a.div_int(b.to_bits()),
            a.midpoint(b),
            a.round(),
            a.round_ties_even(),
            a.ceil(),
            a.recip(),
            a.mul_add(b, a),
            a.mul_div(b, a),
            a.lerp(b, a),
            a.sqrt(),
            a.rsqrt(),
            a.hypot(b),
            a.sin_turns(),
            a.cos_turns(),
            a.sin(),
            a.cos(),
            a.tan(),
            a.atan(),
            a.atan2(b),
            a.asin(),
            a.acos(),
            (a % $T::ONE).asin(),
            (a % $T::ONE).acos(),
        ] {
            $h.write(&v.to_le_bytes());
        }
        let mut acc = $T::accumulator();
        acc.add(a);
        acc.add(b);
        acc.sub(a.wrapping_mul(b));
        acc.add_product(a, b);
        $h.write(&acc.finish().to_le_bytes());
        $h.write(&[a, b, a].iter().sum::<$T>().to_le_bytes());
        let g =
            <$T as FixedFloat>::Angle::from_radians(a) + <$T as FixedFloat>::Angle::from_turns(b);
        let (s, c) = g.sin_cos();
        for v in [s, c, g.to_turns(), g.to_radians(), g.scale(b).to_turns()] {
            $h.write(&v.to_le_bytes());
        }
        let text = a.to_string();
        $h.write(text.as_bytes());
        $h.write(&text.parse::<$T>().unwrap().to_le_bytes());
    }};
}

fn compute() -> u64 {
    let mut rng = Pcg32::new(0x5eed_f00d, 54);
    let mut h = Fnv::new();
    for _ in 0..ROUNDS {
        for_each_width!(mix!(h, rng,));
    }
    h.finish()
}

#[test]
fn golden_hash() {
    let hash = compute();
    assert_eq!(
        hash, GOLDEN,
        "determinism hash changed: got {:#018x}, expected {:#018x}",
        hash, GOLDEN
    );
}

macro_rules! mix_vectors {
    ($h:ident, $rng:ident, $module:ident, $T:ident, $lit:ident, $Acc:ident, $Raw:ident, $bits:tt, $f:tt) => {{
        let mut g = || $T::from_bits($rng.edge_bits($bits, $T::FRAC_BITS) as _);
        let a = Vec3::new(g(), g(), g());
        let b = Vec3::new(g(), g(), g());
        let s = g();
        let (a2, b2) = (Vec2::new(a.x, a.y), Vec2::new(b.x, b.y));
        let angle = <$T as FixedFloat>::Angle::from_turns(s);
        for v in [
            a + b,
            a - b,
            a * b,
            a * s,
            a / s,
            a.lerp(b, s),
            a.cross(b),
            a.normalize(),
            a.clamp_length_max(s),
            a.clamp_length(s, b.x),
        ] {
            $h.write(&v.to_le_bytes());
        }
        for v in [
            a2.rotate(angle),
            a2.normalize(),
            a2.clamp_length(s, b.y),
            a2.perp(),
        ] {
            $h.write(&v.to_le_bytes());
        }
        for v in [
            a.dot(b),
            a.length(),
            a.distance(b),
            a.distance_sq(b),
            a.angle_to(b),
            a2.dot(b2),
            a2.length(),
            a2.perp_dot(b2),
            a2.angle_to(b2),
        ] {
            $h.write(&v.to_le_bytes());
        }
    }};
}

fn compute_vectors() -> u64 {
    let mut rng = Pcg32::new(0x5eed_0ec5, 55);
    let mut h = Fnv::new();
    for _ in 0..ROUNDS / 5 {
        for_each_width!(mix_vectors!(h, rng,));
    }
    h.finish()
}

/// The vectors of stage 5, hashed apart from `golden_hash` so that its
/// constant, checked on every target, stays the same.
#[test]
fn golden_hash_vectors() {
    let hash = compute_vectors();
    assert_eq!(
        hash, GOLDEN_VECTORS,
        "determinism hash of the vectors changed: got {:#018x}, expected {:#018x}",
        hash, GOLDEN_VECTORS
    );
}
