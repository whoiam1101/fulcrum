//! The macro benchmark "one tick" of ROADMAP stage 5: 5 000 units, each
//! steering toward its own target.
//!
//! Per unit: the vector to the target is normalized; the heading turns toward
//! the target's `atan2` by at most `TURN` radians (the difference wrapped to
//! `[-π, π]`); the velocity is the heading's cosine and sine times `SPEED`
//! plus the normalized direction times `ACCEL`; `pos += vel · dt`. Then each
//! unit counts the next `NEIGHBOURS` units by index within `RADIUS`, by
//! `distance_sq`. The world is `[-50, 50)²`, so every squared distance a
//! 16.16 format meets stays below its range.
//!
//! The same tick runs on fulcrum `FixedFloat32` and `FixedFloat64` through
//! `Vec2`, on `fixed` `I16F16` and `I32F32` with saturating operators, `sqrt`
//! and the `cordic` crate, and on `f32` with `glam`. Each returns the number
//! of neighbour pairs, so the work cannot be skipped.

use crate::{inputs, operand};
use fixed::types::{I16F16, I32F32};
use fulcrum::{FixedFloat, FixedFloat32, FixedFloat64, Vec2};

/// Units per tick.
pub const UNITS: usize = 5_000;
/// Units after each one checked as neighbours.
pub const NEIGHBOURS: usize = 16;

const SPEED: f64 = 1.5;
const ACCEL: f64 = 0.25;
const DT: f64 = 1.0 / 32.0;
const TURN: f64 = 0.1;
const RADIUS: f64 = 4.0;

/// A Q16.16 raw value in `[-50, 50)`.
fn coordinate(x: u64) -> i64 {
    operand(x) * 25
}

/// Q16.16 raw value of a constant.
fn q16(v: f64) -> i64 {
    (v * 65536.0).round() as i64
}

/// The state of every unit.
pub struct Units<V, S> {
    pos: Vec<V>,
    vel: Vec<V>,
    target: Vec<V>,
    heading: Vec<S>,
}

impl<V: Copy, S: Copy> Units<V, S> {
    /// The same starting state for every implementation, from Q16.16 raw
    /// values: a vector from two of them, a scalar from one.
    pub fn new(vector: impl Fn(i64, i64) -> V, scalar: impl Fn(i64) -> S) -> Self {
        let r = inputs(5 * UNITS, 99);
        let c = |i: usize| coordinate(r[i]);
        Self {
            pos: (0..UNITS).map(|i| vector(c(5 * i), c(5 * i + 1))).collect(),
            vel: (0..UNITS).map(|_| vector(0, 0)).collect(),
            target: (0..UNITS)
                .map(|i| vector(c(5 * i + 2), c(5 * i + 3)))
                .collect(),
            heading: (0..UNITS).map(|i| scalar(operand(r[5 * i + 4]))).collect(),
        }
    }
}

/// The tick on fulcrum, for any width.
pub fn fulcrum<T: FixedFloat>(u: &mut Units<Vec2<T>, T>, q: impl Fn(i64) -> T) -> u32 {
    let (speed, accel, dt, turn) = (q(q16(SPEED)), q(q16(ACCEL)), q(q16(DT)), q(q16(TURN)));
    let r2 = q(q16(RADIUS * RADIUS));
    for i in 0..UNITS {
        let to = u.target[i] - u.pos[i];
        let dir = to.normalize();
        let mut diff = to.y.atan2(to.x) - u.heading[i];
        if diff > T::PI {
            diff -= T::TAU;
        } else if diff < -T::PI {
            diff += T::TAU;
        }
        let h = u.heading[i] + diff.clamp(-turn, turn);
        u.heading[i] = h;
        let (s, c) = h.sin_cos();
        u.vel[i] = Vec2::new(c, s) * speed + dir * accel;
        u.pos[i] += u.vel[i] * dt;
    }
    let mut pairs = 0;
    for i in 0..UNITS {
        for j in i + 1..(i + 1 + NEIGHBOURS).min(UNITS) {
            pairs += (u.pos[i].distance_sq(u.pos[j]) < r2) as u32;
        }
    }
    pairs
}

/// fulcrum `FixedFloat32` units.
pub fn fulcrum32() -> Units<Vec2<FixedFloat32>, FixedFloat32> {
    let s = |v: i64| FixedFloat32::from_bits(v as i32);
    Units::new(move |x, y| Vec2::new(s(x), s(y)), s)
}

/// fulcrum `FixedFloat64` units.
pub fn fulcrum64() -> Units<Vec2<FixedFloat64>, FixedFloat64> {
    let s = |v: i64| FixedFloat64::from_bits(v << 16);
    Units::new(move |x, y| Vec2::new(s(x), s(y)), s)
}

/// The tick on `f32` with `glam`.
pub fn glam(u: &mut Units<glam::Vec2, f32>) -> u32 {
    let (speed, accel, dt, turn) = (SPEED as f32, ACCEL as f32, DT as f32, TURN as f32);
    let r2 = (RADIUS * RADIUS) as f32;
    let (pi, tau) = (std::f32::consts::PI, std::f32::consts::TAU);
    for i in 0..UNITS {
        let to = u.target[i] - u.pos[i];
        let dir = to.normalize_or_zero();
        let mut diff = to.y.atan2(to.x) - u.heading[i];
        if diff > pi {
            diff -= tau;
        } else if diff < -pi {
            diff += tau;
        }
        let h = u.heading[i] + diff.clamp(-turn, turn);
        u.heading[i] = h;
        let (s, c) = h.sin_cos();
        u.vel[i] = glam::Vec2::new(c, s) * speed + dir * accel;
        u.pos[i] += u.vel[i] * dt;
    }
    let mut pairs = 0;
    for i in 0..UNITS {
        for j in i + 1..(i + 1 + NEIGHBOURS).min(UNITS) {
            pairs += (u.pos[i].distance_squared(u.pos[j]) < r2) as u32;
        }
    }
    pairs
}

/// `f32` units for `glam`.
pub fn glam_units() -> Units<glam::Vec2, f32> {
    let s = |v: i64| v as f32 / 65536.0;
    Units::new(move |x, y| glam::Vec2::new(s(x), s(y)), s)
}

/// A vector of `fixed` numbers with saturating operators.
#[derive(Clone, Copy)]
pub struct FixedVec<F> {
    x: F,
    y: F,
}

/// The tick on a `fixed` type `$F`, with `$q` making it from Q16.16.
macro_rules! fixed_tick {
    ($name:ident, $units:ident, $F:ty, $q:expr) => {
        /// The tick on this `fixed` type: saturating operators, `sqrt` for
        /// `normalize`, `cordic` for `atan2`, `sin` and `cos`.
        pub fn $name(u: &mut Units<FixedVec<$F>, $F>) -> u32 {
            let q = $q;
            let (speed, accel, dt, turn) = (q(q16(SPEED)), q(q16(ACCEL)), q(q16(DT)), q(q16(TURN)));
            let r2 = q(q16(RADIUS * RADIUS));
            let (pi, tau) = (<$F>::PI, <$F>::TAU);
            let sub = |a: FixedVec<$F>, b: FixedVec<$F>| FixedVec {
                x: a.x.saturating_sub(b.x),
                y: a.y.saturating_sub(b.y),
            };
            let len_sq = |v: FixedVec<$F>| {
                v.x.saturating_mul(v.x)
                    .saturating_add(v.y.saturating_mul(v.y))
            };
            for i in 0..UNITS {
                let to = sub(u.target[i], u.pos[i]);
                let len = len_sq(to).sqrt();
                let dir = if len == <$F>::ZERO {
                    to
                } else {
                    FixedVec {
                        x: to.x.saturating_div(len),
                        y: to.y.saturating_div(len),
                    }
                };
                let mut diff = cordic::atan2(to.y, to.x).saturating_sub(u.heading[i]);
                if diff > pi {
                    diff -= tau;
                } else if diff < -pi {
                    diff += tau;
                }
                let h = u.heading[i].saturating_add(diff.clamp(-turn, turn));
                u.heading[i] = h;
                let (s, c) = (cordic::sin(h), cordic::cos(h));
                let v = FixedVec {
                    x: c.saturating_mul(speed)
                        .saturating_add(dir.x.saturating_mul(accel)),
                    y: s.saturating_mul(speed)
                        .saturating_add(dir.y.saturating_mul(accel)),
                };
                u.vel[i] = v;
                u.pos[i] = FixedVec {
                    x: u.pos[i].x.saturating_add(v.x.saturating_mul(dt)),
                    y: u.pos[i].y.saturating_add(v.y.saturating_mul(dt)),
                };
            }
            let mut pairs = 0;
            for i in 0..UNITS {
                for j in i + 1..(i + 1 + NEIGHBOURS).min(UNITS) {
                    pairs += (len_sq(sub(u.pos[i], u.pos[j])) < r2) as u32;
                }
            }
            pairs
        }

        /// Units of this `fixed` type.
        pub fn $units() -> Units<FixedVec<$F>, $F> {
            let q = $q;
            Units::new(move |x, y| FixedVec { x: q(x), y: q(y) }, q)
        }
    };
}

fixed_tick!(fixed16, fixed16_units, I16F16, |v: i64| I16F16::from_bits(
    v as i32
));
fixed_tick!(fixed32, fixed32_units, I32F32, |v: i64| I32F32::from_bits(
    v << 16
));

#[cfg(test)]
mod tests {
    use super::*;

    /// Every implementation runs the same simulation: after ten ticks the
    /// neighbour counts agree within 10 % (they differ by rounding only).
    #[test]
    fn implementations_agree() {
        let (mut a, mut b) = (fulcrum32(), fulcrum64());
        let (mut c, mut d, mut e) = (fixed16_units(), fixed32_units(), glam_units());
        let mut counts = [0u32; 5];
        for _ in 0..10 {
            counts = [
                fulcrum(&mut a, |v| FixedFloat32::from_bits(v as i32)),
                fulcrum(&mut b, |v| FixedFloat64::from_bits(v << 16)),
                fixed16(&mut c),
                fixed32(&mut d),
                glam(&mut e),
            ];
        }
        let reference = counts[4] as f64;
        assert!(reference > 100.0, "{:?}", counts);
        for n in counts {
            assert!(
                (n as f64 - reference).abs() < reference / 10.0,
                "{:?}",
                counts
            );
        }
    }
}
