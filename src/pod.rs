//! `bytemuck` support, behind the `bytemuck` feature: [`bytemuck::Zeroable`]
//! and [`bytemuck::Pod`], for casting slices of values to bytes and back
//! (struct-of-arrays layouts, buffers for a renderer).
//!
//! The only `unsafe` code of the crate. Every `unsafe impl` carries its own
//! `SAFETY:` doc comment, which `clippy::undocumented_unsafe_blocks` requires.

macro_rules! impl_pod {
    ($Name:ident) => {
        /// SAFETY: the type is `#[repr(transparent)]` over a signed primitive
        /// integer, so all zeros is a valid value, the number `0`.
        #[allow(unsafe_code)]
        unsafe impl bytemuck::Zeroable for $Name {}

        /// SAFETY: `#[repr(transparent)]` over a signed primitive integer: no
        /// padding, every bit pattern is a valid value, no interior
        /// mutability, and the type is `Copy` and `'static`.
        #[allow(unsafe_code)]
        unsafe impl bytemuck::Pod for $Name {}
    };
}

/// SAFETY: `#[repr(C)]` with two fields of one `Zeroable` type, so all zeros
/// is the zero vector.
#[allow(unsafe_code)]
unsafe impl<T: bytemuck::Zeroable> bytemuck::Zeroable for crate::Vec2<T> {}

/// SAFETY: `#[repr(C)]` with two fields of one `Pod` type has no padding (its
/// size is a multiple of the alignment of the field), and every bit pattern
/// of each field is valid.
#[allow(unsafe_code)]
unsafe impl<T: bytemuck::Pod> bytemuck::Pod for crate::Vec2<T> {}

/// SAFETY: `#[repr(C)]` with three fields of one `Zeroable` type, so all
/// zeros is the zero vector.
#[allow(unsafe_code)]
unsafe impl<T: bytemuck::Zeroable> bytemuck::Zeroable for crate::Vec3<T> {}

/// SAFETY: `#[repr(C)]` with three fields of one `Pod` type has no padding
/// (its size is a multiple of the alignment of the field), and every bit
/// pattern of each field is valid.
#[allow(unsafe_code)]
unsafe impl<T: bytemuck::Pod> bytemuck::Pod for crate::Vec3<T> {}
