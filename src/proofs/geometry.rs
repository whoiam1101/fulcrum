//! Kani "no panic" harnesses of the vector geometry: one harness per
//! operation and width, each in its own CI job (`proofs_geometry::<name>`).
//!
//! Each one runs a loop on symbolic wide integers: the Newton iteration of
//! `kernel::isqrt` (`length8`), the 62-bit sine and cosine (`rotate`), the
//! exact products and `atan` of the angle (`vec2_angle`). The solver needs
//! far more time and memory than for the harnesses of `proofs`. Their names
//! carry the width without an underscore (`rotate16`), so the shards of
//! `proofs`, which select harnesses by the substrings `_8`, `_16`, `_32` and
//! `_64`, never pick them up.
//!
//! The rest of the geometry does not converge on a CI runner: `normalize`
//! and `clamp_length` exhausted its memory within a minute with the
//! 256-by-128-bit division of `kernel::scale_to`, which `kernel::scale_narrow`
//! replaced on 8–32 bits in stage 7 (not tried since), `length` and `distance` of 16 bits
//! and `angle_to` of `Vec3` run past five hours. Exhaustive tests in release
//! with overflow checks take their place (`tests/vec_geometry.rs`), where
//! the domain allows it.

use crate::{Angle16, Angle8, FixedFloat16, FixedFloat8, Vec2, Vec3};

/// A `Vec2` of type `$T` with symbolic components.
macro_rules! any_vec2 {
    ($T:ident) => {
        Vec2::new($T::from_bits(kani::any()), $T::from_bits(kani::any()))
    };
}

/// `length` and `distance` of `Vec2` and `Vec3` on `FixedFloat8`: the roots
/// of sums of up to three squares stay in the domain of `kernel::isqrt`.
#[kani::proof]
#[kani::unwind(130)]
fn length8() {
    let a = Vec3::new(
        FixedFloat8::from_bits(kani::any()),
        FixedFloat8::from_bits(kani::any()),
        FixedFloat8::from_bits(kani::any()),
    );
    let b = any_vec2!(FixedFloat8);
    let c = Vec3::new(b.x, b.y, FixedFloat8::from_bits(kani::any()));
    let _ = (a.length(), a.distance(c), b.length(), b.distance(b.perp()));
}

macro_rules! plane_no_panic {
    ($T:ident, $A:ident, $rotate:ident, $vec2_angle:ident) => {
        /// `rotate` of `Vec2` by any angle: the 62-bit sine and cosine.
        #[kani::proof]
        #[kani::unwind(130)]
        fn $rotate() {
            let _ = any_vec2!($T).rotate($A::from_bits(kani::any()));
        }

        /// `angle_to` of `Vec2`: the exact cross and dot products.
        #[kani::proof]
        #[kani::unwind(130)]
        fn $vec2_angle() {
            let _ = any_vec2!($T).angle_to(any_vec2!($T));
        }
    };
}

plane_no_panic!(FixedFloat8, Angle8, rotate8, vec2_angle8);
plane_no_panic!(FixedFloat16, Angle16, rotate16, vec2_angle16);
