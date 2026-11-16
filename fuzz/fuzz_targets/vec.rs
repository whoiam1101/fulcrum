//! Arbitrary vectors: no method of `Vec2` or `Vec3` panics; `dot`,
//! `length_sq`, `perp_dot`, `cross` and the lengths equal the exact rational
//! oracle; `normalize` and `clamp_length_max` are correctly rounded by the
//! definition of rounding on big integers; `angle_to` of `Vec2` is within 1
//! ulp of the interval oracle.

#![no_main]

#[macro_use]
#[path = "../../tests/common/widths.rs"]
mod widths;

use fulcrum::*;
use fulcrum_oracle::{atan2_int, Format, TRIG_SCALE};
use libfuzzer_sys::fuzz_target;
use num_bigint::BigInt;
use num_rational::BigRational;

/// Whether `r` is `x · k / √s` rounded to nearest, ties toward `+∞`:
/// `(2|r| - 1)² · s ≤ 4x²k² < (2|r| + 1)² · s`, the ends swapped for a
/// negative `x`.
fn is_scaled(r: i128, x: i128, k: i128, s: &BigInt) -> bool {
    if r != 0 && (r < 0) != (x < 0) {
        return false;
    }
    let m = BigInt::from(r.unsigned_abs());
    let n = BigInt::from(4) * BigInt::from(x) * BigInt::from(x) * BigInt::from(k) * BigInt::from(k);
    let above = (&m * 2 + 1) * (&m * 2 + 1) * s;
    let below = (&m * 2 - 1) * (&m * 2 - 1) * s;
    let low_ok = m == BigInt::from(0) || if x >= 0 { below <= n } else { below < n };
    let high_ok = if x >= 0 { n < above } else { n <= above };
    low_ok && high_ok
}

macro_rules! check {
    ($data:ident, $module:ident, $T:ident, $lit:ident, $Acc:ident, $Bits:ty, $bits:tt, $frac:tt) => {{
        const N: usize = core::mem::size_of::<$Bits>();
        if $data.len() >= 7 * N {
            let r: Vec<i128> = (0..7)
                .map(|i| {
                    <$Bits>::from_le_bytes($data[i * N..(i + 1) * N].try_into().unwrap()) as i128
                })
                .collect();
            let fmt = Format {
                bits: $bits,
                frac: $frac,
            };
            let f = |i: usize| $T::from_bits(r[i] as $Bits);
            let raw = |x: $T| x.to_bits() as i128;
            let (a3, b3, len) = (
                Vec3::new(f(0), f(1), f(2)),
                Vec3::new(f(3), f(4), f(5)),
                f(6),
            );
            let (a2, b2) = (Vec2::new(a3.x, a3.y), Vec2::new(b3.x, b3.y));
            let (a, b) = (&r[..3], &r[3..6]);

            assert_eq!(raw(a2.dot(b2)), fmt.dot(&a[..2], &b[..2]).0);
            assert_eq!(raw(a3.dot(b3)), fmt.dot(a, b).0);
            assert_eq!(raw(a3.length_sq()), fmt.dot(a, a).0);
            assert_eq!(raw(a2.length_sq()), fmt.dot(&a[..2], &a[..2]).0);
            let det = |p: i128, q: i128, u: i128, w: i128| {
                let e = fmt.exact(p) * fmt.exact(w) - fmt.exact(q) * fmt.exact(u);
                fmt.settle(fmt.round(&e)).0
            };
            assert_eq!(raw(a2.perp_dot(b2)), det(a[0], a[1], b[0], b[1]));
            let c = a3.cross(b3);
            assert_eq!(raw(c.x), det(a[1], a[2], b[1], b[2]));
            assert_eq!(raw(c.y), det(a[2], a[0], b[2], b[0]));
            assert_eq!(raw(c.z), det(a[0], a[1], b[0], b[1]));
            for n in [2, 3] {
                let sum = a[..n]
                    .iter()
                    .fold(BigRational::from_integer(BigInt::from(0)), |s, &v| {
                        s + fmt.exact(v) * fmt.exact(v)
                    });
                let want = fmt.settle(fmt.round_sqrt(&sum)).0;
                let got = if n == 2 {
                    raw(a2.length())
                } else {
                    raw(a3.length())
                };
                assert_eq!(got, want);
            }

            let s2: BigInt = a[..2]
                .iter()
                .map(|&v| BigInt::from(v) * BigInt::from(v))
                .sum();
            let s3: BigInt = &s2 + BigInt::from(a[2]) * BigInt::from(a[2]);
            let k = r[6].max(0);
            let one = 1i128 << $frac;
            if let Some(u) = a3.try_normalize() {
                for (i, got) in [u.x, u.y, u.z].into_iter().enumerate() {
                    assert!(is_scaled(raw(got), a[i], one, &s3));
                }
            }
            if let Some(u) = a2.try_normalize() {
                for (i, got) in [u.x, u.y].into_iter().enumerate() {
                    assert!(is_scaled(raw(got), a[i], one, &s2));
                }
            }
            let w = a3.clamp_length_max(len);
            if s3 > BigInt::from(k) * BigInt::from(k) {
                for (i, got) in [w.x, w.y, w.z].into_iter().enumerate() {
                    assert!(is_scaled(raw(got), a[i], k, &s3));
                }
            } else {
                assert_eq!(w, a3);
            }

            let cross =
                BigInt::from(a[0]) * BigInt::from(b[1]) - BigInt::from(a[1]) * BigInt::from(b[0]);
            let dot =
                BigInt::from(a[0]) * BigInt::from(b[0]) + BigInt::from(a[1]) * BigInt::from(b[1]);
            let (lo, hi) = atan2_int(&cross, &dot);
            let shift = TRIG_SCALE - $frac;
            let got = BigInt::from(raw(a2.angle_to(b2))) << shift;
            let ulp = BigInt::from(1) << shift;
            assert!(&got - lo < ulp && hi - &got < ulp);

            let angle = <<$T as FixedFloat>::Angle>::from_bits(r[6] as _);
            let _ = (
                a2.rotate(angle),
                a3.angle_to(b3),
                a3.clamp_length(len, b3.x),
                a2.clamp_length(len, b3.x),
                a3.distance(b3),
                a3.distance_sq(b3),
                a2.lerp(b2, len),
                a3 * b3,
                a3 / len,
                a3.normalize(),
            );
        }
    }};
}

fuzz_target!(|data: &[u8]| {
    for_each_width!(check!(data,));
});
