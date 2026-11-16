//! `Vec2` and `Vec3` against the exact rational oracle on every width,
//! including the 64-bit sums beyond `i128`:
//! `dot`, `length_sq`, `distance_sq`, `perp_dot`, `cross` and the lengths
//! bit for bit; `normalize`, `clamp_length_max` and `clamp_length` (with
//! `min > max` and negative bounds) correctly rounded by the
//! definition of rounding on big integers; `rotate` and `angle_to` within
//! 1 ulp of the 256-bit interval series.

#[macro_use]
#[path = "../../tests/common/widths.rs"]
mod widths;

use fulcrum::*;
use fulcrum_oracle::{atan2_int, sin_turns, Format, TRIG_SCALE};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use proptest::prelude::*;

fn edge(bits: u32, frac: u32) -> impl Strategy<Value = i128> {
    let min = i128::MIN >> (128 - bits);
    let max = i128::MAX >> (128 - bits);
    let one = 1i128 << frac;
    prop_oneof![
        1 => Just(0i128),
        1 => Just(1i128),
        1 => Just(-1i128),
        1 => Just(one),
        1 => Just(-one),
        1 => Just(min),
        1 => Just(max),
        1 => Just(min + 1),
        2 => (0..bits - 1, any::<bool>()).prop_map(|(k, n)| if n { -(1i128 << k) } else { 1i128 << k }),
        2 => -4 * one..=4 * one,
        8 => min..=max,
    ]
}

/// `got / 2^frac` is within one ulp of every value of `[lo, hi] / 2^TRIG_SCALE`.
fn within_ulp(got: i128, (lo, hi): (BigInt, BigInt), frac: u32) -> bool {
    let shift = TRIG_SCALE - frac;
    let got = BigInt::from(got) << shift;
    let ulp = BigInt::one() << shift;
    &got - &lo < ulp && &hi - &got < ulp
}

/// Whether `r` is `x · k / √s` rounded to nearest, ties toward `+∞`:
/// `(2|r| - 1)² · s ≤ 4x²k² < (2|r| + 1)² · s` with the sign of `x`, the
/// ends swapped for a negative `x`.
fn is_scaled(r: i128, x: i128, k: i128, s: &BigInt) -> bool {
    if r != 0 && (r < 0) != (x < 0) {
        return false;
    }
    let m = BigInt::from(r.unsigned_abs());
    let n = BigInt::from(4) * BigInt::from(x) * BigInt::from(x) * BigInt::from(k) * BigInt::from(k);
    let above = (&m * 2 + 1) * (&m * 2 + 1) * s;
    let below = (&m * 2 - 1) * (&m * 2 - 1) * s;
    let low_ok = m.is_zero() || if x >= 0 { below <= n } else { below < n };
    let high_ok = if x >= 0 { n < above } else { n <= above };
    low_ok && high_ok
}

fn sum_sq(x: &[i128]) -> BigInt {
    x.iter().map(|&v| BigInt::from(v) * BigInt::from(v)).sum()
}

macro_rules! vec_suite {
    ($module:ident, $T:ident, $lit:ident, $Acc:ident, $Bits:ty, $bits:tt, $frac:tt) => {
        mod $module {
            use super::*;

            const FMT: Format = Format { bits: $bits, frac: $frac };

            fn v3(r: &[i128]) -> Vec3<$T> {
                Vec3::new($T::from_bits(r[0] as $Bits), $T::from_bits(r[1] as $Bits), $T::from_bits(r[2] as $Bits))
            }

            fn raw(x: $T) -> i128 {
                x.to_bits() as i128
            }

            fn det(a: i128, b: i128, c: i128, d: i128) -> i128 {
                let e = FMT.exact(a) * FMT.exact(d) - FMT.exact(b) * FMT.exact(c);
                FMT.settle(FMT.round(&e)).0
            }

            fn root_sum(x: &[i128]) -> i128 {
                let s = x.iter().fold(BigRational::zero(), |s, &v| s + FMT.exact(v) * FMT.exact(v));
                FMT.settle(FMT.round_sqrt(&s)).0
            }

            proptest! {
                #![proptest_config(ProptestConfig { cases: 5_000, ..ProptestConfig::default() })]

                #[test]
                fn exact_once(a in proptest::collection::vec(edge($bits, $frac), 3), b in proptest::collection::vec(edge($bits, $frac), 3)) {
                    let (a3, b3) = (v3(&a), v3(&b));
                    let (a2, b2) = (Vec2::new(a3.x, a3.y), Vec2::new(b3.x, b3.y));
                    prop_assert_eq!(raw(a2.dot(b2)), FMT.dot(&a[..2], &b[..2]).0);
                    prop_assert_eq!(raw(a3.dot(b3)), FMT.dot(&a, &b).0);
                    prop_assert_eq!(raw(a3.length_sq()), FMT.dot(&a, &a).0);
                    prop_assert_eq!(raw(a2.perp_dot(b2)), det(a[0], a[1], b[0], b[1]));
                    let c = a3.cross(b3);
                    prop_assert_eq!([raw(c.x), raw(c.y), raw(c.z)], [det(a[1], a[2], b[1], b[2]), det(a[2], a[0], b[2], b[0]), det(a[0], a[1], b[0], b[1])]);
                    prop_assert_eq!(raw(a2.length()), root_sum(&a[..2]));
                    prop_assert_eq!(raw(a3.length()), root_sum(&a));
                    let d: Vec<BigRational> = a.iter().zip(&b).map(|(&x, &y)| FMT.exact(x) - FMT.exact(y)).collect();
                    for &(n, sq, len) in &[(2, raw(a2.distance_sq(b2)), raw(a2.distance(b2))), (3, raw(a3.distance_sq(b3)), raw(a3.distance(b3)))] {
                        let s = d[..n].iter().fold(BigRational::zero(), |s, x| s + x * x);
                        prop_assert_eq!(sq, FMT.settle(FMT.round(&s)).0);
                        prop_assert_eq!(len, FMT.settle(FMT.round_sqrt(&s)).0);
                    }
                }

                #[test]
                fn scaled(a in proptest::collection::vec(edge($bits, $frac), 3), len in edge($bits, $frac)) {
                    let a3 = v3(&a);
                    let a2 = Vec2::new(a3.x, a3.y);
                    let one = 1i128 << $frac;
                    let k = len.max(0);
                    for &(n, unit, clamped) in &[
                        (2, a2.try_normalize().map(|u| [raw(u.x), raw(u.y), 0]), { let w = a2.clamp_length_max($T::from_bits(len as $Bits)); [raw(w.x), raw(w.y), 0] }),
                        (3, a3.try_normalize().map(|u| [raw(u.x), raw(u.y), raw(u.z)]), { let w = a3.clamp_length_max($T::from_bits(len as $Bits)); [raw(w.x), raw(w.y), raw(w.z)] }),
                    ] {
                        let s = sum_sq(&a[..n]);
                        match unit {
                            None => prop_assert!(s.is_zero()),
                            Some(u) => for i in 0..n {
                                prop_assert!(is_scaled(u[i], a[i], one, &s), "normalize {} {:?}", i, a3);
                            },
                        }
                        if s > BigInt::from(k) * BigInt::from(k) {
                            for i in 0..n {
                                prop_assert!(is_scaled(clamped[i], a[i], k, &s), "clamp {} {:?} {}", i, a3, len);
                            }
                        } else {
                            prop_assert_eq!(&clamped[..n], &a[..n]);
                        }
                    }
                }

                #[test]
                fn clamp_length(a in proptest::collection::vec(edge($bits, $frac), 3), lo in edge($bits, $frac), hi in edge($bits, $frac)) {
                    let a3 = v3(&a);
                    let a2 = Vec2::new(a3.x, a3.y);
                    let (kmin, kmax) = (lo.max(0), hi.max(0));
                    let (tmin, tmax) = ($T::from_bits(lo as $Bits), $T::from_bits(hi as $Bits));
                    for &(n, got) in &[
                        (2, { let w = a2.clamp_length(tmin, tmax); [raw(w.x), raw(w.y), 0] }),
                        (3, { let w = a3.clamp_length(tmin, tmax); [raw(w.x), raw(w.y), raw(w.z)] }),
                    ] {
                        let s = sum_sq(&a[..n]);
                        let sq = |k: i128| BigInt::from(k) * BigInt::from(k);
                        let target = if s < sq(kmin) && !s.is_zero() {
                            Some(kmin)
                        } else if s >= sq(kmin) && s > sq(kmax) {
                            Some(kmax)
                        } else {
                            None
                        };
                        match target {
                            Some(k) => for i in 0..n {
                                prop_assert!(is_scaled(got[i], a[i], k, &s), "clamp_length {} {:?} {} {}", i, a3, lo, hi);
                            },
                            None => prop_assert_eq!(&got[..n], &a[..n]),
                        }
                    }
                }

                #[test]
                fn rotate(x in edge($bits, $frac), y in edge($bits, $frac), t in any::<u64>()) {
                    let (x, y) = if x.unsigned_abs() + y.unsigned_abs() < 1 << 56 { (x, y) } else { (x >> 9, y >> 9) };
                    let n = $bits;
                    let t = t & (u64::MAX >> (64 - n));
                    let angle = <$T as FixedFloat>::Angle::from_bits(t as _);
                    let r = Vec2::new($T::from_bits(x as $Bits), $T::from_bits(y as $Bits)).rotate(angle);
                    let s = sin_turns(t as i128, n);
                    let c = sin_turns((t as i128) + (1 << (n - 2)), n);
                    let mul = |v: i128, (lo, hi): &(BigInt, BigInt)| {
                        let (p, q) = (BigInt::from(v) * lo, BigInt::from(v) * hi);
                        if v >= 0 { (p, q) } else { (q, p) }
                    };
                    let (xc, xs, yc, ys) = (mul(x, &c), mul(x, &s), mul(y, &c), mul(y, &s));
                    let rx = (&xc.0 - &ys.1, &xc.1 - &ys.0);
                    let ry = (&xs.0 + &yc.0, &xs.1 + &yc.1);
                    let ulp = BigInt::one() << TRIG_SCALE;
                    let lim = BigInt::one() << ($bits - 1 + TRIG_SCALE);
                    let within = |got: i128, (lo, hi): &(BigInt, BigInt)| {
                        let got = BigInt::from(got) << TRIG_SCALE;
                        &got - lo < ulp && hi - &got < ulp
                    };
                    if rx.0.abs() < lim && rx.1.abs() < lim {
                        prop_assert!(within(raw(r.x), &rx), "x {} {} {}", x, y, t);
                    }
                    if ry.0.abs() < lim && ry.1.abs() < lim {
                        prop_assert!(within(raw(r.y), &ry), "y {} {} {}", x, y, t);
                    }
                }

                #[test]
                fn angle_to(a in proptest::collection::vec(edge($bits, $frac), 3), b in proptest::collection::vec(edge($bits, $frac), 3)) {
                    let (a3, b3) = (v3(&a), v3(&b));
                    let (a2, b2) = (Vec2::new(a3.x, a3.y), Vec2::new(b3.x, b3.y));
                    let big = |i: usize, r: &[i128]| BigInt::from(r[i]);
                    let cross2 = big(0, &a) * big(1, &b) - big(1, &a) * big(0, &b);
                    let dot2 = big(0, &a) * big(0, &b) + big(1, &a) * big(1, &b);
                    prop_assert!(within_ulp(raw(a2.angle_to(b2)), atan2_int(&cross2, &dot2), $frac), "angle2 {:?} {:?}", a2, b2);

                    let c = [
                        big(1, &a) * big(2, &b) - big(2, &a) * big(1, &b),
                        big(2, &a) * big(0, &b) - big(0, &a) * big(2, &b),
                        cross2,
                    ];
                    let dot3 = dot2 + big(2, &a) * big(2, &b);
                    let c2: BigInt = c.iter().map(|v| v * v).sum();
                    let got = raw(a3.angle_to(b3));
                    if c2.is_zero() && !dot3.is_negative() {
                        prop_assert_eq!(got, 0);
                    } else {
                        let sh = 200u32;
                        let n = (c2 << (2 * sh)).sqrt();
                        let d = dot3 << sh;
                        let (lo, _) = atan2_int(&n, &d);
                        let (_, hi) = atan2_int(&(n + 1), &d);
                        prop_assert!(within_ulp(got, (lo, hi), $frac), "angle3 {:?} {:?}", a3, b3);
                    }
                }
            }
        }
    };
}

for_each_width!(vec_suite!());
