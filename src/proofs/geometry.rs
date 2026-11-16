//! Kani "no panic" harnesses of the vector geometry on 8 and 16 bits: one
//! harness per operation and width.
//!
//! Each one runs a loop on symbolic wide integers: the Newton iteration of
//! `kernel::isqrt` (`length`), the 256-by-128-bit division of
//! `kernel::scale_to` (`normalize`, `clamp_length`), the 62-bit sine and
//! cosine (`rotate`), the exact products and `atan` of the angle
//! (`vec2_angle`, `vec3_angle`). The solver needs far more time and memory
//! than for the harnesses of `proofs`, so CI runs each in its own job
//! (`proofs_geometry::<name>`). Their names carry the width
//! without an underscore (`rotate16`), so the shards of `proofs`, which
//! select harnesses by the substrings `_8`, `_16`, `_32` and `_64`, never
//! pick them up.

use crate::{Angle16, Angle8, FixedFloat16, FixedFloat8, Vec2, Vec3};

/// A `Vec2` of type `$T` with symbolic components.
macro_rules! any_vec2 {
    ($T:ident) => {
        Vec2::new($T::from_bits(kani::any()), $T::from_bits(kani::any()))
    };
}

/// A `Vec3` of type `$T` with symbolic components.
macro_rules! any_vec3 {
    ($T:ident) => {
        Vec3::new(
            $T::from_bits(kani::any()),
            $T::from_bits(kani::any()),
            $T::from_bits(kani::any()),
        )
    };
}

macro_rules! geometry_no_panic {
    ($T:ident, $A:ident, $length:ident, $normalize:ident, $clamp:ident, $rotate:ident, $vec2_angle:ident, $vec3_angle:ident) => {
        /// `length` and `distance` of `Vec2` and `Vec3`: the roots of sums
        /// of up to three squares stay in the domain of `kernel::isqrt`.
        #[kani::proof]
        #[kani::unwind(130)]
        fn $length() {
            let a = any_vec3!($T);
            let b = any_vec2!($T);
            let c = Vec3::new(b.x, b.y, $T::from_bits(kani::any()));
            let _ = (a.length(), a.distance(c), b.length(), b.distance(b.perp()));
        }

        /// `try_normalize` of `Vec3` and `normalize` of `Vec2`: the 256-bit
        /// product and division of `kernel::scale_to` stay in range.
        #[kani::proof]
        #[kani::unwind(130)]
        fn $normalize() {
            let a = any_vec3!($T);
            let b = any_vec2!($T);
            let _ = (a.try_normalize(), b.normalize());
        }

        /// `clamp_length` of `Vec3` on any bounds, `min > max` and negative
        /// ones included.
        #[kani::proof]
        #[kani::unwind(130)]
        fn $clamp() {
            let a = any_vec3!($T);
            let _ = a.clamp_length($T::from_bits(kani::any()), $T::from_bits(kani::any()));
        }

        /// `rotate` of `Vec2` by any angle: the 62-bit sine and cosine.
        #[kani::proof]
        #[kani::unwind(130)]
        fn $rotate() {
            let b = any_vec2!($T);
            let _ = b.rotate($A::from_bits(kani::any()));
        }

        /// `angle_to` of `Vec2`: the exact cross and dot products.
        #[kani::proof]
        #[kani::unwind(130)]
        fn $vec2_angle() {
            let a = any_vec2!($T);
            let b = any_vec2!($T);
            let _ = a.angle_to(b);
        }

        /// `angle_to` of `Vec3`: the exact cross and dot products and their
        /// sums of three terms.
        #[kani::proof]
        #[kani::unwind(130)]
        fn $vec3_angle() {
            let a = any_vec3!($T);
            let b = any_vec3!($T);
            let _ = a.angle_to(b);
        }
    };
}

geometry_no_panic!(
    FixedFloat8,
    Angle8,
    length8,
    normalize8,
    clamp_length8,
    rotate8,
    vec2_angle8,
    vec3_angle8
);
geometry_no_panic!(
    FixedFloat16,
    Angle16,
    length16,
    normalize16,
    clamp_length16,
    rotate16,
    vec2_angle16,
    vec3_angle16
);
