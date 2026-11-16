//! `bytemuck` support, behind the `bytemuck` feature: [`bytemuck::Zeroable`]
//! and [`bytemuck::Pod`], for casting slices of values to bytes and back
//! (SoA arrays, buffers for a renderer).
//!
//! The only `unsafe` code of the crate. Both traits are sound for every type
//! here: it is `#[repr(transparent)]` over a signed primitive integer, so it
//! has no padding, every bit pattern is a valid value, and all zeros is `0`.

macro_rules! impl_pod {
    ($Name:ident) => {
        #[allow(unsafe_code)]
        unsafe impl bytemuck::Zeroable for $Name {}

        #[allow(unsafe_code)]
        unsafe impl bytemuck::Pod for $Name {}
    };
}

/// Both traits for the vectors of a `Pod` component: `#[repr(C)]` with two
/// or three fields of one type has no padding (its size is a multiple of the
/// alignment of the field), every bit pattern of each field is valid, and all
/// zeros is the zero vector.
#[allow(unsafe_code)]
unsafe impl<T: bytemuck::Zeroable> bytemuck::Zeroable for crate::Vec2<T> {}

#[allow(unsafe_code)]
unsafe impl<T: bytemuck::Pod> bytemuck::Pod for crate::Vec2<T> {}

#[allow(unsafe_code)]
unsafe impl<T: bytemuck::Zeroable> bytemuck::Zeroable for crate::Vec3<T> {}

#[allow(unsafe_code)]
unsafe impl<T: bytemuck::Pod> bytemuck::Pod for crate::Vec3<T> {}
