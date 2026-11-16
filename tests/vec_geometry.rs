//! `normalize`, `try_normalize`, `clamp_length`, `clamp_length_max`,
//! `rotate` and `angle_to` of `Vec2` and `Vec3`.
//!
//! The scaled vectors are checked against the definition of rounding
//! without a root: `m` is `round(|x| · k / √s)` when
//! `(2m - 1)² · s ≤ 4x²k² < (2m + 1)² · s` (the ends swapped for a negative
//! `x`, whose tie goes toward zero), in `u128`; on `FixedFloat64` the
//! products can exceed it, and those cases are skipped. `rotate` and
//! `angle_to` are checked within 1 ulp against the independent sine,
//! cosine and `atan2` of `tests/common/trig.rs`, whose values have 64
//! fractional bits.
//!
//! Every width: edge-biased random vectors, half of them shrunk. `rotate`
//! is within 1 ulp below a raw length of `2^57`; the error bound `2^-56` of
//! the integer sine allows the check below `2^50`, and the oracle
//! (`oracle/tests/vec.rs`) takes the rest.

#![cfg(not(feature = "strict-overflow"))]

#[macro_use]
mod common;

use common::*;
use fulcrum::*;

/// `Σ x[i]²`, exact: the components of the tests are within `2^63`.
fn sum_sq(x: &[i128]) -> u128 {
    x.iter().map(|&v| v.unsigned_abs() * v.unsigned_abs()).sum()
}

/// `Σ x[i]²`, or `None` when it does not fit `u128`.
fn checked_sum_sq(x: &[i128]) -> Option<u128> {
    x.iter().try_fold(0u128, |s, &v| {
        s.checked_add(v.unsigned_abs().checked_mul(v.unsigned_abs())?)
    })
}

/// Whether `r` is `x · k / √s` rounded to nearest, ties toward `+∞`, or
/// `None` when the check does not fit `u128`. `s > 0`, `k ≥ 0`.
fn is_scaled(r: i128, x: i128, k: u128, s: u128) -> Option<bool> {
    if r != 0 && (r < 0) != (x < 0) {
        return Some(false);
    }
    let m = r.unsigned_abs();
    let n = 4u128
        .checked_mul(x.unsigned_abs().checked_mul(x.unsigned_abs())?)?
        .checked_mul(k.checked_mul(k)?)?;
    let above = (2 * m + 1).checked_mul(2 * m + 1)?.checked_mul(s)?;
    let below = if m == 0 {
        None
    } else {
        Some((2 * m - 1).checked_mul(2 * m - 1)?.checked_mul(s)?)
    };
    Some(if x >= 0 {
        below.map_or(true, |b| b <= n) && n < above
    } else {
        below.map_or(true, |b| b < n) && n <= above
    })
}

/// `⌊√n⌋` by binary search, independent of the kernel.
fn floor_sqrt(n: u128) -> u128 {
    let (mut lo, mut hi) = (0u128, 1u128 << 64);
    while hi - lo > 1 {
        let mid = lo + (hi - lo) / 2;
        if mid.checked_mul(mid).map_or(false, |q| q <= n) {
            lo = mid;
        } else {
            hi = mid;
        }
    }
    lo
}

/// `n` and `d` shifted together so that the larger has 62 or 63 bits, and
/// the error of the shift in units of the result (`0` when exact).
fn to_63_bits(n: u128, d: u128) -> (u128, u128, i128) {
    let bits = 128 - n.max(d).leading_zeros();
    if bits > 63 {
        (n >> (bits - 63), d >> (bits - 63), 1)
    } else {
        (n << (63 - bits), d << (63 - bits), 0)
    }
}

/// Whether `got` is within 1 ulp of `atan2(y, x) · 2^64`, where `y` and `x`
/// are within `err` units of the exact values after [`to_63_bits`].
fn angle_within_ulp(
    got: i128,
    y_neg: bool,
    y: u128,
    x_neg: bool,
    x: u128,
    err: i128,
    f: u32,
) -> bool {
    let (n, d, shift_err) = to_63_bits(y, x);
    let sign = |neg: bool, v: u128| if neg { -(v as i128) } else { v as i128 };
    let r = trig::atan2(n as i128, sign(x_neg, d));
    let r = if y_neg { -r } else { r };
    let slack = trig::ERROR + 8 * (err + shift_err);
    trig::within_ulp_of(got, r - slack, r + slack, f)
}

macro_rules! check_geometry {
    ($T:ident, $bits:expr, $f:expr, $a:expr, $b:expr, $s:expr, $t:expr) => {{
        type A = <$T as FixedFloat>::Angle;
        let ra: [i128; 3] = [$a[0] as i128, $a[1] as i128, $a[2] as i128];
        let rb: [i128; 3] = [$b[0] as i128, $b[1] as i128, $b[2] as i128];
        let v = |r: &[i128; 3]| {
            Vec3::new(
                $T::from_bits(r[0] as _),
                $T::from_bits(r[1] as _),
                $T::from_bits(r[2] as _),
            )
        };
        let (a3, b3) = (v(&ra), v(&rb));
        let a2 = Vec2::new(a3.x, a3.y);
        let b2 = Vec2::new(b3.x, b3.y);
        let len = $T::from_bits($s as _);
        let ctx = || format!("{} {:?} {:?} {:?}", stringify!($T), a3, b3, len);
        let raw3 = |w: Vec3<$T>| {
            [
                w.x.to_bits() as i128,
                w.y.to_bits() as i128,
                w.z.to_bits() as i128,
            ]
        };
        let one = 1u128 << $f;

        for &(n, unit, name) in &[
            (
                2,
                a2.try_normalize()
                    .map(|w| [w.x.to_bits() as i128, w.y.to_bits() as i128, 0]),
                "2",
            ),
            (3, a3.try_normalize().map(raw3), "3"),
        ] {
            let x = &ra[..n];
            let s = sum_sq(x);
            match unit {
                None => assert_eq!(s, 0, "try_normalize{} None {}", name, ctx()),
                Some(u) => {
                    for i in 0..n {
                        if let Some(ok) = is_scaled(u[i], x[i], one, s) {
                            assert!(ok, "normalize{} [{}] {}", name, i, ctx());
                        }
                    }
                }
            }
        }
        if a3 == Vec3::ZERO {
            assert_eq!(a3.normalize(), Vec3::ZERO);
        }

        let k = len.to_bits().max(0) as i128;
        let k2 = (k as u128) * (k as u128);
        for &(n, got_max, got_both, name) in &[
            (
                2,
                {
                    let w = a2.clamp_length_max(len);
                    [w.x.to_bits() as i128, w.y.to_bits() as i128, 0]
                },
                {
                    let w = a2.clamp_length(len, len);
                    [w.x.to_bits() as i128, w.y.to_bits() as i128, 0]
                },
                "2",
            ),
            (
                3,
                raw3(a3.clamp_length_max(len)),
                raw3(a3.clamp_length(len, len)),
                "3",
            ),
        ] {
            let x = &ra[..n];
            let s = sum_sq(x);
            let scaled = |got: &[i128; 3], what: &str| {
                for i in 0..n {
                    if let Some(ok) = is_scaled(got[i], x[i], k as u128, s) {
                        assert!(ok, "{}{} [{}] {}", what, name, i, ctx());
                    }
                }
            };
            if s > k2 {
                scaled(&got_max, "clamp_length_max");
            } else {
                assert_eq!(
                    &got_max[..n],
                    x,
                    "clamp_length_max{} unchanged {}",
                    name,
                    ctx()
                );
            }
            if s == 0 || s == k2 {
                assert_eq!(
                    &got_both[..n],
                    x,
                    "clamp_length{} unchanged {}",
                    name,
                    ctx()
                );
            } else {
                scaled(&got_both, "clamp_length");
            }
        }

        let t = $t;
        let angle = A::from_bits(t as _);
        let (x, y) = (ra[0], ra[1]);
        let r = a2.rotate(angle);
        let (rx, ry) = (r.x.to_bits() as i128, r.y.to_bits() as i128);
        let quarter = 1u128 << ($bits - 2);
        let tt = (t as u128) & ((quarter << 2) - 1);
        if tt % quarter == 0 {
            let sat = |w: i128| spec::saturate(w, $bits);
            let want = match tt / quarter {
                0 => [x, y],
                1 => [sat(-y), x],
                2 => [sat(-x), sat(-y)],
                _ => [y, sat(-x)],
            };
            assert_eq!([rx, ry], want, "rotate by quarters {}", ctx());
        } else if x.unsigned_abs() + y.unsigned_abs() < 1u128 << 50 {
            let c = trig::cos_turns(tt as i128, $bits);
            let s = trig::sin_turns(tt as i128, $bits);
            let err = (x.abs() + y.abs()) * trig::ERROR;
            let wx = x * c - y * s;
            let wy = x * s + y * c;
            let (lo, hi) = (
                spec::saturate(i128::MIN, $bits),
                spec::saturate(i128::MAX, $bits),
            );
            let within = |got: i128, w: i128| {
                if w - err > hi << 64 {
                    got == hi
                } else if w + err < lo << 64 {
                    got == lo
                } else {
                    ((got << 64) - w).abs() + err < 1 << 64
                }
            };
            assert!(within(rx, wx), "rotate x {} by {}", ctx(), tt);
            assert!(within(ry, wy), "rotate y {} by {}", ctx(), tt);
        }

        let cross = ra[0] * rb[1] - ra[1] * rb[0];
        if let Some(dot) = (ra[0] * rb[0]).checked_add(ra[1] * rb[1]) {
            let got = a2.angle_to(b2).to_bits() as i128;
            let ok = if cross == 0 && dot >= 0 {
                got == 0
            } else {
                angle_within_ulp(
                    got,
                    cross < 0,
                    cross.unsigned_abs(),
                    dot < 0,
                    dot.unsigned_abs(),
                    0,
                    $f,
                )
            };
            assert!(ok, "angle_to2 {}", ctx());
        }

        {
            let c = [
                ra[1] * rb[2] - ra[2] * rb[1],
                ra[2] * rb[0] - ra[0] * rb[2],
                ra[0] * rb[1] - ra[1] * rb[0],
            ];
            let dot = (ra[0] * rb[0])
                .checked_add(ra[1] * rb[1])
                .and_then(|d| d.checked_add(ra[2] * rb[2]));
            let got = a3.angle_to(b3).to_bits() as i128;
            let ok = match (checked_sum_sq(&c), dot) {
                (None, _) | (_, None) => true,
                (Some(c2), Some(dot)) if c2 == 0 && dot >= 0 => got == 0,
                (Some(c2), Some(dot)) => {
                    let m = floor_sqrt(c2).max(dot.unsigned_abs());
                    let bits = 128 - m.leading_zeros();
                    let up = 62u32.saturating_sub(bits);
                    let n = if 2 * up + 128 - c2.leading_zeros() <= 127 {
                        floor_sqrt(c2 << (2 * up))
                    } else {
                        floor_sqrt(c2) << up
                    };
                    angle_within_ulp(got, false, n, dot < 0, dot.unsigned_abs() << up, 2, $f)
                }
            };
            assert!(ok, "angle_to3 {}", ctx());
        }
    }};
}

macro_rules! random_geometry {
    ($m:ident, $T:ident, $lit:ident, $Acc:ident, $Raw:ty, $bits:expr, $f:expr) => {
        #[test]
        fn $m() {
            let mut rng = Pcg32::new(0x5eed_0006, $bits);
            for i in 0..100_000 {
                let mut g = || rng.edge_bits($bits, $f) as $Raw;
                let (mut a, b) = ([g(), g(), g()], [g(), g(), g()]);
                let s = g();
                if i % 2 == 0 {
                    for c in a.iter_mut() {
                        *c >>= ($bits / 3) as u32;
                    }
                }
                let t = rng.next_u64();
                check_geometry!($T, $bits, $f, a, b, s, t);
            }
        }
    };
}

for_each_width!(random_geometry!());

#[test]
fn worked_examples() {
    let v = Vec2::new(ff32!(3), ff32!(4));
    assert_eq!(v.normalize(), Vec2::new(ff32!(0.6), ff32!(0.8)));
    assert_eq!(Vec2f32::ZERO.try_normalize(), None);
    assert_eq!(Vec2f32::ZERO.normalize(), Vec2f32::ZERO);
    assert_eq!(v.clamp_length_max(ff32!(10)), v);
    assert_eq!(
        v.clamp_length_max(ff32!(2.5)),
        Vec2::new(ff32!(1.5), ff32!(2))
    );
    assert_eq!(
        v.clamp_length(ff32!(10), ff32!(20)),
        Vec2::new(ff32!(6), ff32!(8))
    );
    assert_eq!(v.clamp_length_max(ff32!(-1)), Vec2f32::ZERO);
    assert_eq!(
        v.clamp_length(ff32!(10), ff32!(2.5)),
        Vec2::new(ff32!(6), ff32!(8))
    );
    assert_eq!(
        v.clamp_length(ff32!(1), ff32!(2.5)),
        Vec2::new(ff32!(1.5), ff32!(2))
    );
    assert_eq!(v.clamp_length(ff32!(-3), ff32!(-1)), Vec2f32::ZERO);
    assert_eq!(
        Vec2f32::ZERO.clamp_length(ff32!(1), ff32!(2)),
        Vec2f32::ZERO
    );
    assert_eq!(
        Vec3::new(ff64!(2), ff64!(3), ff64!(6)).normalize().z,
        FixedFloat64::from_bits(3681400539)
    );
    assert_eq!(Vec2f32::X.rotate(Angle32::QUARTER_TURN), Vec2f32::Y);
    assert_eq!(Vec2f32::X.angle_to(Vec2f32::Y), FixedFloat32::FRAC_PI_2);
    assert_eq!(Vec2f32::Y.angle_to(Vec2f32::X), -FixedFloat32::FRAC_PI_2);
    assert_eq!(Vec2f32::X.angle_to(-Vec2f32::X), FixedFloat32::PI);
    assert_eq!(Vec3f32::X.angle_to(Vec3f32::Z), FixedFloat32::FRAC_PI_2);
    assert_eq!(Vec3f32::X.angle_to(-Vec3f32::X), FixedFloat32::PI);
    assert_eq!(Vec3f32::X.angle_to(Vec3f32::ZERO), FixedFloat32::ZERO);
    let tiny = Vec3::new(FixedFloat64::DELTA, FixedFloat64::DELTA, FixedFloat64::ZERO);
    let huge = Vec3::new(FixedFloat64::MIN, FixedFloat64::ZERO, FixedFloat64::ZERO);
    assert!((tiny.angle_to(huge) - FixedFloat64::PI * ff64!(0.75)).abs() <= FixedFloat64::DELTA);
    let h = Angle64::from_turns(ff64!(0.125));
    let r = Vec2f64::X.rotate(h);
    assert_eq!(r.x, r.y);
    assert_eq!(r.x, FixedFloat64::SQRT_2 / ff64!(2));
}
