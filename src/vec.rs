//! Vectors of two and three components over any [`FixedFloat`].
//!
//! Component-wise operations follow the scalar ones: `+`, `-`, unary `-`,
//! `*` of two vectors, `*` and `/` by a scalar saturate per component, exactly like the operators
//! of the component type (and panic under `strict-overflow`). Methods that
//! combine components never round in between: `dot`, `length_sq`,
//! `distance_sq`, `perp_dot` and `cross` sum the exact products and round
//! once; `length` and `distance` take a correctly rounded root of the exact
//! sum of squares. Each result then saturates like a scalar.

use crate::FixedFloat;
use core::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};

/// A vector of two components, `#[repr(C)]`: `x`, then `y`.
///
/// The component type is a [`FixedFloat`]; aliases name each width:
/// [`Vec2f8`], [`Vec2f16`], [`Vec2f32`], [`Vec2f64`].
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
#[repr(C)]
pub struct Vec2<T> {
    /// The first component.
    pub x: T,
    /// The second component.
    pub y: T,
}

/// A vector of three components, `#[repr(C)]`: `x`, `y`, then `z`.
///
/// The component type is a [`FixedFloat`]; aliases name each width:
/// [`Vec3f8`], [`Vec3f16`], [`Vec3f32`], [`Vec3f64`].
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
#[repr(C)]
pub struct Vec3<T> {
    /// The first component.
    pub x: T,
    /// The second component.
    pub y: T,
    /// The third component.
    pub z: T,
}

/// [`Vec2`] of [`FixedFloat8`](crate::FixedFloat8).
pub type Vec2f8 = Vec2<crate::FixedFloat8>;
/// [`Vec2`] of [`FixedFloat16`](crate::FixedFloat16).
pub type Vec2f16 = Vec2<crate::FixedFloat16>;
/// [`Vec2`] of [`FixedFloat32`](crate::FixedFloat32).
pub type Vec2f32 = Vec2<crate::FixedFloat32>;
/// [`Vec2`] of [`FixedFloat64`](crate::FixedFloat64).
pub type Vec2f64 = Vec2<crate::FixedFloat64>;
/// [`Vec3`] of [`FixedFloat8`](crate::FixedFloat8).
pub type Vec3f8 = Vec3<crate::FixedFloat8>;
/// [`Vec3`] of [`FixedFloat16`](crate::FixedFloat16).
pub type Vec3f16 = Vec3<crate::FixedFloat16>;
/// [`Vec3`] of [`FixedFloat32`](crate::FixedFloat32).
pub type Vec3f32 = Vec3<crate::FixedFloat32>;
/// [`Vec3`] of [`FixedFloat64`](crate::FixedFloat64).
pub type Vec3f64 = Vec3<crate::FixedFloat64>;

/// The parts shared by [`Vec2`] and [`Vec3`]: every method that works
/// component by component, the operators, `dot`, `length_sq` and the
/// distances.
macro_rules! impl_vec {
    ($V:ident { $($c:ident),+ }) => {
        impl<T> $V<T> {
            /// A vector from its components.
            #[inline]
            pub const fn new($($c: T),+) -> Self {
                Self { $($c),+ }
            }
        }

        impl<T: FixedFloat> $V<T> {
            /// The zero vector.
            pub const ZERO: Self = Self { $($c: T::ZERO),+ };

            /// Every component equal to `v`.
            #[inline]
            pub fn splat(v: T) -> Self {
                Self { $($c: v),+ }
            }

            /// The component-wise minimum.
            #[inline]
            #[must_use]
            pub fn min(self, other: Self) -> Self {
                Self { $($c: core::cmp::min(self.$c, other.$c)),+ }
            }

            /// The component-wise maximum.
            #[inline]
            #[must_use]
            pub fn max(self, other: Self) -> Self {
                Self { $($c: core::cmp::max(self.$c, other.$c)),+ }
            }

            /// The component-wise absolute value, saturating: `|MIN|` is `MAX`.
            #[inline]
            #[must_use]
            pub fn abs(self) -> Self {
                Self { $($c: self.$c.abs()),+ }
            }

            /// The dot product: the exact sum of the exact products, rounded
            /// once to nearest (ties toward `+∞`) and saturated.
            #[inline]
            pub fn dot(self, other: Self) -> T {
                T::__dot(&[$(self.$c),+], &[$(other.$c),+], crate::sealed::Token)
            }

            /// The squared length, `self · self`, rounded once and saturated.
            #[inline]
            pub fn length_sq(self) -> T {
                self.dot(self)
            }

            /// `self - other` when every component difference is in range.
            #[inline]
            fn checked_sub(self, other: Self) -> Option<Self> {
                Some(Self { $($c: self.$c.checked_sub(other.$c)?),+ })
            }

            /// The squared distance, rounded once from the exact differences
            /// and squares and saturated. A difference out of range is at
            /// least `2^(INT_BITS - 1)`, and its square saturates to `MAX`.
            #[inline]
            pub fn distance_sq(self, other: Self) -> T {
                self.checked_sub(other).map_or(T::MAX, Self::length_sq)
            }

            /// The distance, correctly rounded from the exact differences and
            /// saturated: a difference out of range saturates it to `MAX`.
            #[inline]
            pub fn distance(self, other: Self) -> T {
                self.checked_sub(other).map_or(T::MAX, Self::length)
            }

            /// The vector of length one in the direction of `self`, or `None`
            /// for the zero vector. Each component is `x / |v|` correctly
            /// rounded (to nearest, ties toward `+∞`) from the exact squared
            /// length, so the result depends only on the direction and the
            /// length of the rounded vector is within a few ulp of one.
            #[inline]
            pub fn try_normalize(self) -> Option<Self> {
                if self == Self::ZERO {
                    None
                } else {
                    Some(Self::from_xyz(T::__scale_to(self.to_xyz(), T::ONE, crate::sealed::Token)))
                }
            }

            /// [`Self::try_normalize`], with the zero vector for the zero
            /// vector.
            #[inline]
            #[must_use]
            pub fn normalize(self) -> Self {
                self.try_normalize().unwrap_or(Self::ZERO)
            }

            /// `self` scaled to length `max` when it is longer, unchanged
            /// otherwise; a negative `max` counts as `0`. The comparison is
            /// exact and each scaled component `x · max / |v|` is correctly
            /// rounded, never longer than `max` in any component.
            #[inline]
            #[must_use]
            pub fn clamp_length_max(self, max: T) -> Self {
                let max = core::cmp::max(max, T::ZERO);
                if T::__cmp_length(self.to_xyz(), max, crate::sealed::Token) == core::cmp::Ordering::Greater {
                    Self::from_xyz(T::__scale_to(self.to_xyz(), max, crate::sealed::Token))
                } else {
                    self
                }
            }

            /// `self` scaled to length `min` when it is shorter and to `max`
            /// when it is longer, like `glam`: `min` is checked first, so
            /// `min > max` gives length `min`. Negative bounds count as `0`;
            /// the zero vector has no direction and stays zero. Exact
            /// comparisons, correctly rounded components as in
            /// [`Self::clamp_length_max`].
            #[inline]
            #[must_use]
            pub fn clamp_length(self, min: T, max: T) -> Self {
                let min = core::cmp::max(min, T::ZERO);
                if T::__cmp_length(self.to_xyz(), min, crate::sealed::Token) == core::cmp::Ordering::Less {
                    Self::from_xyz(T::__scale_to(self.to_xyz(), min, crate::sealed::Token))
                } else {
                    self.clamp_length_max(max)
                }
            }

            /// Linear interpolation `self + (other - self) · t` per component,
            /// each rounded once like [`FixedFloat::lerp`].
            #[inline]
            #[must_use]
            pub fn lerp(self, other: Self, t: T) -> Self {
                Self { $($c: self.$c.lerp(other.$c, t)),+ }
            }
        }

        impl<T: FixedFloat> Add for $V<T> {
            type Output = Self;
            #[inline]
            fn add(self, rhs: Self) -> Self {
                Self { $($c: self.$c + rhs.$c),+ }
            }
        }

        impl<T: FixedFloat> Sub for $V<T> {
            type Output = Self;
            #[inline]
            fn sub(self, rhs: Self) -> Self {
                Self { $($c: self.$c - rhs.$c),+ }
            }
        }

        impl<T: FixedFloat> Neg for $V<T> {
            type Output = Self;
            #[inline]
            fn neg(self) -> Self {
                Self { $($c: -self.$c),+ }
            }
        }

        impl<T: FixedFloat> Mul<T> for $V<T> {
            type Output = Self;
            #[inline]
            fn mul(self, rhs: T) -> Self {
                Self { $($c: self.$c * rhs),+ }
            }
        }

        /// The component-wise product, each rounded and saturated like `*`
        /// of the components.
        impl<T: FixedFloat> Mul for $V<T> {
            type Output = Self;
            #[inline]
            fn mul(self, rhs: Self) -> Self {
                Self { $($c: self.$c * rhs.$c),+ }
            }
        }

        impl<T: FixedFloat> MulAssign for $V<T> {
            #[inline]
            fn mul_assign(&mut self, rhs: Self) {
                *self = *self * rhs;
            }
        }

        impl<T: FixedFloat> Div<T> for $V<T> {
            type Output = Self;
            #[inline]
            fn div(self, rhs: T) -> Self {
                Self { $($c: self.$c / rhs),+ }
            }
        }

        impl<T: FixedFloat> AddAssign for $V<T> {
            #[inline]
            fn add_assign(&mut self, rhs: Self) {
                *self = *self + rhs;
            }
        }

        impl<T: FixedFloat> SubAssign for $V<T> {
            #[inline]
            fn sub_assign(&mut self, rhs: Self) {
                *self = *self - rhs;
            }
        }

        impl<T: FixedFloat> MulAssign<T> for $V<T> {
            #[inline]
            fn mul_assign(&mut self, rhs: T) {
                *self = *self * rhs;
            }
        }

        impl<T: FixedFloat> DivAssign<T> for $V<T> {
            #[inline]
            fn div_assign(&mut self, rhs: T) {
                *self = *self / rhs;
            }
        }
    };
}

impl_vec!(Vec2 { x, y });
impl_vec!(Vec3 { x, y, z });

impl<T: FixedFloat> Vec2<T> {
    /// `[x, y, 0]`: the shape the hidden methods of [`FixedFloat`] take.
    #[inline]
    fn to_xyz(self) -> [T; 3] {
        [self.x, self.y, T::ZERO]
    }

    /// The vector of `[x, y, _]`.
    #[inline]
    fn from_xyz(v: [T; 3]) -> Self {
        Self { x: v[0], y: v[1] }
    }

    /// `self` turned counterclockwise by `angle`: `x·cos - y·sin`,
    /// `x·sin + y·cos` with a sine and cosine of 62 fractional bits, each
    /// component rounded once and saturated. A multiple of a quarter turn is
    /// exact; otherwise the result is within 1 ulp while
    /// `|self| < 2^(57 - FRAC_BITS)` (every vector up to `FixedFloat32`;
    /// `3.3·10^7` on `FixedFloat64`), and its error grows with the length
    /// beyond.
    #[inline]
    #[must_use]
    pub fn rotate(self, angle: T::Angle) -> Self {
        let (x, y) = T::__rotate(self.x, self.y, angle, crate::sealed::Token);
        Self { x, y }
    }

    /// The signed angle from `self` to `other` in radians, in `(-π, π]`,
    /// positive counterclockwise: `atan2` of the exact `perp_dot` and `dot`,
    /// within 1 ulp. `0` when either vector is zero.
    #[inline]
    pub fn angle_to(self, other: Self) -> T {
        T::__angle2([self.x, self.y], [other.x, other.y], crate::sealed::Token)
    }

    /// The unit vector along `x`.
    pub const X: Self = Self {
        x: T::ONE,
        y: T::ZERO,
    };
    /// The unit vector along `y`.
    pub const Y: Self = Self {
        x: T::ZERO,
        y: T::ONE,
    };

    /// The length `√(x² + y²)`, correctly rounded and saturated, like
    /// [`FixedFloat::hypot`].
    #[inline]
    pub fn length(self) -> T {
        self.x.hypot(self.y)
    }

    /// The perpendicular dot product `self.x · other.y - self.y · other.x`,
    /// the `z` of the cross product: rounded once and saturated.
    #[inline]
    pub fn perp_dot(self, other: Self) -> T {
        T::__det(self.x, self.y, other.x, other.y, crate::sealed::Token)
    }

    /// `self` turned a quarter turn counterclockwise, `(-y, x)`; `-MIN`
    /// saturates like unary `-`.
    #[inline]
    #[must_use]
    pub fn perp(self) -> Self {
        Self {
            x: -self.y,
            y: self.x,
        }
    }
}

impl<T: FixedFloat> Vec3<T> {
    /// `[x, y, z]`: the shape the hidden methods of [`FixedFloat`] take.
    #[inline]
    fn to_xyz(self) -> [T; 3] {
        [self.x, self.y, self.z]
    }

    /// The vector of `[x, y, z]`.
    #[inline]
    fn from_xyz(v: [T; 3]) -> Self {
        Self {
            x: v[0],
            y: v[1],
            z: v[2],
        }
    }

    /// The angle between `self` and `other` in radians, in `[0, π]`: `atan2`
    /// of the length of the cross product and the dot product, both from
    /// exact products, within 1 ulp. `0` when either vector is zero.
    #[inline]
    pub fn angle_to(self, other: Self) -> T {
        T::__angle3(self.to_xyz(), other.to_xyz(), crate::sealed::Token)
    }

    /// The unit vector along `x`.
    pub const X: Self = Self {
        x: T::ONE,
        y: T::ZERO,
        z: T::ZERO,
    };
    /// The unit vector along `y`.
    pub const Y: Self = Self {
        x: T::ZERO,
        y: T::ONE,
        z: T::ZERO,
    };
    /// The unit vector along `z`.
    pub const Z: Self = Self {
        x: T::ZERO,
        y: T::ZERO,
        z: T::ONE,
    };

    /// The length `√(x² + y² + z²)`, correctly rounded from the exact sum of
    /// squares and saturated.
    #[inline]
    pub fn length(self) -> T {
        T::__hypot3(self.x, self.y, self.z, crate::sealed::Token)
    }

    /// The cross product, each component rounded once from its exact value
    /// and saturated.
    #[inline]
    #[must_use]
    pub fn cross(self, other: Self) -> Self {
        Self {
            x: T::__det(self.y, self.z, other.y, other.z, crate::sealed::Token),
            y: T::__det(self.z, self.x, other.z, other.x, crate::sealed::Token),
            z: T::__det(self.x, self.y, other.x, other.y, crate::sealed::Token),
        }
    }
}

/// `scalar * vector` for each component type, the same as `vector * scalar`.
macro_rules! impl_scalar_mul {
    ($($T:ident),+) => {$(
        impl Mul<Vec2<crate::$T>> for crate::$T {
            type Output = Vec2<crate::$T>;
            #[inline]
            fn mul(self, rhs: Vec2<crate::$T>) -> Vec2<crate::$T> {
                rhs * self
            }
        }

        impl Mul<Vec3<crate::$T>> for crate::$T {
            type Output = Vec3<crate::$T>;
            #[inline]
            fn mul(self, rhs: Vec3<crate::$T>) -> Vec3<crate::$T> {
                rhs * self
            }
        }
    )+};
}

impl_scalar_mul!(FixedFloat8, FixedFloat16, FixedFloat32, FixedFloat64);

/// Copies `src` into `dst` at `at`, in a `const fn`.
macro_rules! put {
    ($dst:ident, $at:expr, $src:expr) => {{
        let src = $src;
        let mut i = 0;
        while i < src.len() {
            $dst[$at + i] = src[i];
            i += 1;
        }
    }};
}

/// The bytes of `N` components at `at` of `bytes`, in a `const fn`.
macro_rules! take {
    ($bytes:ident, $at:expr, $N:literal) => {{
        let mut out = [0u8; $N];
        let mut i = 0;
        while i < $N {
            out[i] = $bytes[$at + i];
            i += 1;
        }
        out
    }};
}

/// `to_le_bytes`, `from_le_bytes`, `to_be_bytes`, `from_be_bytes` of the
/// vectors of each component type of `N` bytes: the components in order,
/// each in the format of the component.
macro_rules! impl_vec_bytes {
    ($($T:ident: $N:literal),+ $(,)?) => {$(
        impl_vec_bytes!(
            @order $T, $N, to_le_bytes, from_le_bytes,
            "each as [`to_le_bytes`](crate::FixedFloat64::to_le_bytes) of the component: the canonical format for snapshots"
        );
        impl_vec_bytes!(@order $T, $N, to_be_bytes, from_be_bytes, "each big-endian");
    )+};
    (@order $T:ident, $N:literal, $to:ident, $from:ident, $doc:literal) => {
        impl Vec2<crate::$T> {
            #[doc = concat!("`x` then `y`, ", $doc, ".")]
            #[inline]
            pub const fn $to(self) -> [u8; 2 * $N] {
                let mut out = [0u8; 2 * $N];
                put!(out, 0, self.x.$to());
                put!(out, $N, self.y.$to());
                out
            }

            #[doc = concat!("Inverse of [`Self::", stringify!($to), "`].")]
            #[inline]
            pub const fn $from(bytes: [u8; 2 * $N]) -> Self {
                Self {
                    x: crate::$T::$from(take!(bytes, 0, $N)),
                    y: crate::$T::$from(take!(bytes, $N, $N)),
                }
            }
        }

        impl Vec3<crate::$T> {
            #[doc = concat!("`x`, `y` then `z`, ", $doc, ".")]
            #[inline]
            pub const fn $to(self) -> [u8; 3 * $N] {
                let mut out = [0u8; 3 * $N];
                put!(out, 0, self.x.$to());
                put!(out, $N, self.y.$to());
                put!(out, 2 * $N, self.z.$to());
                out
            }

            #[doc = concat!("Inverse of [`Self::", stringify!($to), "`].")]
            #[inline]
            pub const fn $from(bytes: [u8; 3 * $N]) -> Self {
                Self {
                    x: crate::$T::$from(take!(bytes, 0, $N)),
                    y: crate::$T::$from(take!(bytes, $N, $N)),
                    z: crate::$T::$from(take!(bytes, 2 * $N, $N)),
                }
            }
        }
    };
}

impl_vec_bytes! {
    FixedFloat8: 1,
    FixedFloat16: 2,
    FixedFloat32: 4,
    FixedFloat64: 8,
}
