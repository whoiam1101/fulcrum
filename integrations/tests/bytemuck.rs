//! `bytemuck`: `Pod` and `Zeroable` cast values and slices to bytes in the
//! layout of `to_le_bytes` / `to_ne_bytes` and back.

#![cfg(feature = "bytemuck")]

use fulcrum::{ff32, FixedFloat16, FixedFloat32, FixedFloat64, FixedFloat8};

#[test]
fn zeroed_is_zero() {
    assert_eq!(
        <FixedFloat8 as bytemuck::Zeroable>::zeroed(),
        FixedFloat8::ZERO
    );
    assert_eq!(
        <FixedFloat64 as bytemuck::Zeroable>::zeroed(),
        FixedFloat64::ZERO
    );
}

#[test]
fn cast_matches_native_bytes() {
    let x = ff32!(-1.25);
    assert_eq!(bytemuck::bytes_of(&x), x.to_bits().to_ne_bytes());
    assert_eq!(bytemuck::cast::<FixedFloat32, i32>(x), x.to_bits());
    assert_eq!(
        bytemuck::cast::<i16, FixedFloat16>(-256),
        FixedFloat16::NEG_ONE
    );
}

#[test]
fn slices_cast_both_ways() {
    let raw: Vec<i64> = vec![0, 1, -1, i64::MIN, i64::MAX, 1 << 32];
    let values: &[FixedFloat64] = bytemuck::cast_slice(&raw);
    assert_eq!(values.len(), raw.len());
    for (v, r) in values.iter().zip(&raw) {
        assert_eq!(v.to_bits(), *r);
    }
    let back: &[i64] = bytemuck::cast_slice(values);
    assert_eq!(back, &raw[..]);
    let bytes: &[u8] = bytemuck::cast_slice(values);
    assert_eq!(bytes.len(), 8 * raw.len());
    assert_eq!(&bytes[8..16], 1i64.to_ne_bytes());
}

#[test]
fn vectors_cast_to_their_components() {
    use fulcrum::{Vec2f32, Vec3f64};
    assert_eq!(<Vec3f64 as bytemuck::Zeroable>::zeroed(), Vec3f64::ZERO);
    let raw: Vec<i32> = vec![1 << 16, -1, i32::MIN, 7];
    let vs: &[Vec2f32] = bytemuck::cast_slice(&raw);
    assert_eq!(vs.len(), 2);
    assert_eq!(vs[0], Vec2f32::new(FixedFloat32::ONE, -FixedFloat32::DELTA));
    assert_eq!(vs[1].x, FixedFloat32::MIN);
    let v = Vec3f64::new(FixedFloat64::ONE, FixedFloat64::MIN, FixedFloat64::DELTA);
    let mut ne = Vec::new();
    for c in [v.x, v.y, v.z] {
        ne.extend_from_slice(&c.to_bits().to_ne_bytes());
    }
    assert_eq!(bytemuck::bytes_of(&v), &ne[..]);
}
