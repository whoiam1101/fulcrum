//! Plain loops over slices, the batch operations of ROADMAP stage 7.
//!
//! [`map2`], [`map3`] and [`map_int`] are the loop shapes; the fulcrum loops
//! below are those shapes on one operation each, `#[inline(never)]`, so that
//! each is one symbol `<operation>_<width>` in the assembly that `bin/asm.rs`
//! checks for vectorization. `benches/ops.rs` times them against the same
//! shapes on `fixed` and on integers, and `benches/instr.rs` counts their
//! instructions. The scalar `mul`, `div` and `saturating_add` of two values,
//! `scalar_<operation>_<width>`, are checked by `bin/asm.rs` for calls to
//! software routines and for branches.

use fulcrum::{FixedFloat16, FixedFloat32, FixedFloat64, FixedFloat8};

/// `out[i] = f(a[i], b[i])`.
#[inline]
pub fn map2<T: Copy>(a: &[T], b: &[T], out: &mut [T], f: impl Fn(T, T) -> T) {
    for ((o, x), y) in out.iter_mut().zip(a).zip(b) {
        *o = f(*x, *y);
    }
}

/// `out[i] = f(a[i], b[i], c[i])`.
#[inline]
pub fn map3<T: Copy>(a: &[T], b: &[T], c: &[T], out: &mut [T], f: impl Fn(T, T, T) -> T) {
    for (((o, x), y), z) in out.iter_mut().zip(a).zip(b).zip(c) {
        *o = f(*x, *y, *z);
    }
}

/// `out[i] = f(a[i], n[i])` for an integer `n[i]`.
#[inline]
pub fn map_int<T: Copy, N: Copy>(a: &[T], n: &[N], out: &mut [T], f: impl Fn(T, N) -> T) {
    for ((o, x), k) in out.iter_mut().zip(a).zip(n) {
        *o = f(*x, *k);
    }
}

macro_rules! loops {
    ($T:ident, $Bits:ty, $add:ident, $sub:ident, $mul:ident, $mul_int:ident, $mul_add:ident, $lerp:ident) => {
        /// `out[i] = a[i] + b[i]`.
        #[inline(never)]
        pub fn $add(a: &[$T], b: &[$T], out: &mut [$T]) {
            map2(a, b, out, |x, y| x + y)
        }

        /// `out[i] = a[i] - b[i]`.
        #[inline(never)]
        pub fn $sub(a: &[$T], b: &[$T], out: &mut [$T]) {
            map2(a, b, out, |x, y| x - y)
        }

        /// `out[i] = a[i] * b[i]`.
        #[inline(never)]
        pub fn $mul(a: &[$T], b: &[$T], out: &mut [$T]) {
            map2(a, b, out, |x, y| x * y)
        }

        /// `out[i] = a[i].mul_int(n[i])`.
        #[inline(never)]
        pub fn $mul_int(a: &[$T], n: &[$Bits], out: &mut [$T]) {
            map_int(a, n, out, |x, k| x.mul_int(k))
        }

        /// `out[i] = a[i].mul_add(b[i], c[i])`.
        #[inline(never)]
        pub fn $mul_add(a: &[$T], b: &[$T], c: &[$T], out: &mut [$T]) {
            map3(a, b, c, out, |x, y, z| x.mul_add(y, z))
        }

        /// `out[i] = a[i].lerp(b[i], t[i])`.
        #[inline(never)]
        pub fn $lerp(a: &[$T], b: &[$T], t: &[$T], out: &mut [$T]) {
            map3(a, b, t, out, |x, y, z| x.lerp(y, z))
        }
    };
}

loops!(
    FixedFloat8,
    i8,
    add_8,
    sub_8,
    mul_8,
    mul_int_8,
    mul_add_8,
    lerp_8
);
loops!(
    FixedFloat16,
    i16,
    add_16,
    sub_16,
    mul_16,
    mul_int_16,
    mul_add_16,
    lerp_16
);
loops!(
    FixedFloat32,
    i32,
    add_32,
    sub_32,
    mul_32,
    mul_int_32,
    mul_add_32,
    lerp_32
);

macro_rules! scalar {
    ($T:ident, $mul:ident, $div:ident, $saturating_add:ident) => {
        /// `a * b`.
        #[inline(never)]
        pub fn $mul(a: $T, b: $T) -> $T {
            a * b
        }

        /// `a / b`.
        #[inline(never)]
        pub fn $div(a: $T, b: $T) -> $T {
            a / b
        }

        /// `a.saturating_add(b)`.
        #[inline(never)]
        pub fn $saturating_add(a: $T, b: $T) -> $T {
            a.saturating_add(b)
        }
    };
}

scalar!(
    FixedFloat8,
    scalar_mul_8,
    scalar_div_8,
    scalar_saturating_add_8
);
scalar!(
    FixedFloat16,
    scalar_mul_16,
    scalar_div_16,
    scalar_saturating_add_16
);
scalar!(
    FixedFloat32,
    scalar_mul_32,
    scalar_div_32,
    scalar_saturating_add_32
);
scalar!(
    FixedFloat64,
    scalar_mul_64,
    scalar_div_64,
    scalar_saturating_add_64
);
