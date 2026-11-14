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
