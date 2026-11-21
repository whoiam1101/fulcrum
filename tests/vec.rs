//! `Vec2` and `Vec3` against `spec` of `tests/common/reference.rs` over
//! `i128`: the component-wise operators against the scalar reference, and
//! `dot`, `length_sq`, `distance_sq`, `perp_dot`, `cross` as the exact sum of
//! exact products rounded once, `length` and `distance` as the correctly
//! rounded root of the exact sum of squares.
//!
//! `FixedFloat8`: the length of every `Vec2` and every `Vec3`. Every width:
//! edge-biased random pairs of vectors, and the vectors whose exact sums
//! exceed `i128` on `FixedFloat64`. Sums of products are taken in two 64-bit
//! halves and roots are checked by the bounds of rounding, so neither leaves
//! `i128`.

#![cfg(not(feature = "strict-overflow"))]

#[macro_use]
mod common;

use common::*;
use fulcrum::*;

/// The raw value of an exact sum at scale `2^-2f`, rounded once and
/// saturated to `bits`.
fn round2(sum: i128, f: u32, bits: u32) -> i128 {
    spec::saturate(spec::round_shift(sum, f), bits)
}

/// `Σ a[i] · b[i]` at scale `2^-2f`, rounded once ([`exact_dot`]) and
/// saturated to `bits`.
fn dot_raw(a: &[i128], b: &[i128], f: u32, bits: u32) -> i128 {
    spec::saturate(exact_dot(a, b, |v| v, f), bits)
}

/// `Σ x[i]²`, exact: at most `3 · 2^126`.
fn sum_sq(x: &[i128]) -> u128 {
    x.iter().map(|&v| v.unsigned_abs() * v.unsigned_abs()).sum()
}

/// Whether `got` is `round(√n)` saturated to `bits`, by the bounds of
/// rounding instead of a root: `s` is the rounded root when
/// `s² - s < n ≤ s² + s` (no lower bound for `s = 0`), and the result
/// saturates to `max` exactly when `n > max² - max`.
fn is_root(got: i128, n: u128, bits: u32) -> bool {
    let max = (1u128 << (bits - 1)) - 1;
    if got as u128 == max {
        return n > max * max - max;
    }
    let s = got as u128;
    got >= 0 && n <= s * s + s && (s == 0 || n > s * s - s)
}

macro_rules! check_vectors {
    ($T:ident, $bits:expr, $f:expr, $a:expr, $b:expr, $s:expr) => {{
        let ra: [i128; 3] = [i128::from($a[0]), i128::from($a[1]), i128::from($a[2])];
        let rb: [i128; 3] = [i128::from($b[0]), i128::from($b[1]), i128::from($b[2])];
        let rs = i128::from($s);
        let v = |r: &[i128; 3]| {
            Vec3::new(
                $T::from_bits(r[0] as <$T as fulcrum::FixedFloat>::Bits),
                $T::from_bits(r[1] as <$T as fulcrum::FixedFloat>::Bits),
                $T::from_bits(r[2] as <$T as fulcrum::FixedFloat>::Bits),
            )
        };
        let (a3, b3, s) = (
            v(&ra),
            v(&rb),
            $T::from_bits(rs as <$T as fulcrum::FixedFloat>::Bits),
        );
        let (a2, b2) = (Vec2::new(a3.x, a3.y), Vec2::new(b3.x, b3.y));
        let ctx = || format!("{} {:?} {:?} {:?}", stringify!($T), a3, b3, s);
        let raw3 = |w: Vec3<$T>| {
            [
                i128::from(w.x.to_bits()),
                i128::from(w.y.to_bits()),
                i128::from(w.z.to_bits()),
            ]
        };
        let raw2 = |w: Vec2<$T>| [i128::from(w.x.to_bits()), i128::from(w.y.to_bits())];
        let sat = |x: i128| spec::saturate(x, $bits);
        let bits_of = |x: $T| i128::from(x.to_bits());

        let each = |op: &dyn Fn(i128, i128) -> i128| {
            [op(ra[0], rb[0]), op(ra[1], rb[1]), op(ra[2], rb[2])]
        };
        assert_eq!(raw3(a3 + b3), each(&|x, y| sat(x + y)), "+ {}", ctx());
        assert_eq!(raw3(a3 - b3), each(&|x, y| sat(x - y)), "- {}", ctx());
        assert_eq!(raw3(-a3), each(&|x, _| sat(-x)), "neg {}", ctx());
        assert_eq!(
            raw3(a3 * b3),
            each(&|x, y| sat(spec::mul(x, y, $f))),
            "* {}",
            ctx()
        );
        assert_eq!(
            raw3(a3 * s),
            each(&|x, _| sat(spec::mul(x, rs, $f))),
            "* scalar {}",
            ctx()
        );
        assert_eq!(raw3(s * a3), raw3(a3 * s), "scalar * {}", ctx());
        let div = |x: i128| {
            if rs == 0 {
                spec::div_by_zero(x, $bits)
            } else {
                sat(spec::div(x, rs, $f))
            }
        };
        assert_eq!(raw3(a3 / s), each(&|x, _| div(x)), "/ scalar {}", ctx());
        assert_eq!(raw3(a3.min(b3)), each(&|x, y| x.min(y)), "min {}", ctx());
        assert_eq!(raw3(a3.max(b3)), each(&|x, y| x.max(y)), "max {}", ctx());
        assert_eq!(raw3(a3.abs()), each(&|x, _| sat(x.abs())), "abs {}", ctx());
        assert_eq!(
            raw3(a3.lerp(b3, s)),
            each(&|x, y| sat(spec::lerp(x, y, rs, $f))),
            "lerp {}",
            ctx()
        );

        let mut m = a3;
        m += b3;
        m -= b3;
        m *= s;
        m /= s;
        m *= b3;
        assert_eq!(m, ((a3 + b3 - b3) * s / s) * b3, "assign {}", ctx());

        let first2 = |w: Vec3<$T>| [i128::from(w.x.to_bits()), i128::from(w.y.to_bits())];
        assert_eq!(raw2(a2 + b2), first2(a3 + b3), "+2 {}", ctx());
        assert_eq!(raw2(a2 - b2), first2(a3 - b3), "-2 {}", ctx());
        assert_eq!(raw2(-a2), first2(-a3), "neg2 {}", ctx());
        assert_eq!(raw2(a2 * b2), first2(a3 * b3), "*2 {}", ctx());
        assert_eq!(raw2(a2 * s), first2(a3 * s), "* scalar2 {}", ctx());
        assert_eq!(raw2(s * a2), first2(a3 * s), "scalar *2 {}", ctx());
        assert_eq!(raw2(a2 / s), first2(a3 / s), "/ scalar2 {}", ctx());
        assert_eq!(raw2(a2.min(b2)), first2(a3.min(b3)), "min2 {}", ctx());
        assert_eq!(raw2(a2.max(b2)), first2(a3.max(b3)), "max2 {}", ctx());
        assert_eq!(raw2(a2.abs()), first2(a3.abs()), "abs2 {}", ctx());
        assert_eq!(
            raw2(a2.lerp(b2, s)),
            first2(a3.lerp(b3, s)),
            "lerp2 {}",
            ctx()
        );
        let mut m2 = a2;
        m2 += b2;
        m2 -= b2;
        m2 *= s;
        m2 /= s;
        m2 *= b2;
        assert_eq!(m2, ((a2 + b2 - b2) * s / s) * b2, "assign2 {}", ctx());

        let dots = [
            (dot_raw(&ra[..2], &rb[..2], $f, $bits), a2.dot(b2), "dot2"),
            (dot_raw(&ra, &rb, $f, $bits), a3.dot(b3), "dot3"),
            (
                dot_raw(&ra[..2], &ra[..2], $f, $bits),
                a2.length_sq(),
                "length_sq2",
            ),
            (dot_raw(&ra, &ra, $f, $bits), a3.length_sq(), "length_sq3"),
        ];
        for &(want, got, name) in &dots {
            assert_eq!(bits_of(got), want, "{} {}", name, ctx());
        }

        let det = |p: usize, q: usize| round2(ra[p] * rb[q] - ra[q] * rb[p], $f, $bits);
        assert_eq!(bits_of(a2.perp_dot(b2)), det(0, 1), "perp_dot {}", ctx());
        assert_eq!(
            raw3(a3.cross(b3)),
            [det(1, 2), det(2, 0), det(0, 1)],
            "cross {}",
            ctx()
        );
        assert_eq!(raw2(a2.perp()), [sat(-ra[1]), ra[0]], "perp {}", ctx());

        assert!(
            is_root(bits_of(a2.length()), sum_sq(&ra[..2]), $bits),
            "length2 {}",
            ctx()
        );
        assert!(
            is_root(bits_of(a3.length()), sum_sq(&ra), $bits),
            "length3 {}",
            ctx()
        );

        let diff = [ra[0] - rb[0], ra[1] - rb[1], ra[2] - rb[2]];
        let max = spec::saturate(i128::MAX, $bits);
        for &(n, got_sq, got_len, name) in &[
            (2, a2.distance_sq(b2), a2.distance(b2), "distance2"),
            (3, a3.distance_sq(b3), a3.distance(b3), "distance3"),
        ] {
            let d = &diff[..n];
            if d.iter().any(|&x| !spec::fits(x, $bits)) {
                assert_eq!(bits_of(got_sq), max, "{}_sq out of range {}", name, ctx());
                assert_eq!(bits_of(got_len), max, "{} out of range {}", name, ctx());
                continue;
            }
            assert_eq!(
                bits_of(got_sq),
                dot_raw(d, d, $f, $bits),
                "{}_sq {}",
                name,
                ctx()
            );
            assert!(
                is_root(bits_of(got_len), sum_sq(d), $bits),
                "{} {}",
                name,
                ctx()
            );
        }
    }};
}

macro_rules! random_vectors {
    ($m:ident, $T:ident, $lit:ident, $Acc:ident, $Raw:ty, $bits:expr, $f:expr) => {
        #[test]
        fn $m() {
            let mut rng = Pcg32::new(0x5eed_0005, $bits);
            for _ in 0..200_000 {
                let mut g = || rng.edge_bits($bits, $f) as $Raw;
                let a = [g(), g(), g()];
                let b = [g(), g(), g()];
                let s = g();
                check_vectors!($T, $bits, $f, a, b, s);
            }
        }
    };
}

for_each_width!(random_vectors!());

#[test]
fn fixed8_every_length() {
    let mut seen = 0u64;
    for x in i8::MIN..=i8::MAX {
        for y in i8::MIN..=i8::MAX {
            let n2 = i128::from(x).pow(2) + i128::from(y).pow(2);
            let v2 = Vec2::new(FixedFloat8::from_bits(x), FixedFloat8::from_bits(y));
            assert_eq!(
                i128::from(v2.length().to_bits()),
                spec::saturate(spec::sqrt(n2), 8),
                "{v2:?}"
            );
            for z in i8::MIN..=i8::MAX {
                let n = n2 + i128::from(z).pow(2);
                let v = Vec3::new(v2.x, v2.y, FixedFloat8::from_bits(z));
                let got = i128::from(v.length().to_bits());
                if got < i128::from(i8::MAX) {
                    assert!(spec::is_sqrt_ratio(got, n, 1), "{v:?}");
                } else {
                    assert!(spec::sqrt(n) >= i128::from(i8::MAX), "{v:?}");
                }
                seen += 1;
            }
        }
    }
    assert_eq!(seen, 1 << 24);
}

#[test]
fn constants_and_generic_use() {
    fn generic<T: FixedFloat>(a: Vec2<T>, b: Vec2<T>) -> T {
        (a - b).length_sq()
    }
    type F = FixedFloat32;
    assert_eq!(Vec2f32::ZERO, Vec2::new(F::ZERO, F::ZERO));
    assert_eq!(Vec2f32::X + Vec2f32::Y, Vec2f32::splat(F::ONE));
    assert_eq!(Vec3f32::X.cross(Vec3f32::Y), Vec3f32::Z);
    assert_eq!(Vec3f32::Y.cross(Vec3f32::Z), Vec3f32::X);
    assert_eq!(Vec3f32::Z.cross(Vec3f32::X), Vec3f32::Y);
    assert_eq!(Vec2f32::X.perp(), Vec2f32::Y);
    assert_eq!(Vec2f32::X.perp_dot(Vec2f32::Y), F::ONE);
    let v = Vec2::new(ff32!(3), ff32!(4));
    assert_eq!(v.length(), ff32!(5));
    assert_eq!(v.length_sq(), ff32!(25));
    assert_eq!(Vec3::new(ff32!(2), ff32!(3), ff32!(6)).length(), ff32!(7));
    assert_eq!(Vec2f32::default(), Vec2f32::ZERO);
    assert_eq!(Vec3f64::default(), Vec3f64::ZERO);
    assert_eq!(generic(v, Vec2f32::ZERO), ff32!(25));
}

#[test]
fn dot_rounds_once() {
    let a = Vec2::new(ff8!(0.25), ff8!(0.25));
    let b = Vec2::new(ff8!(0.125), ff8!(0.125));
    assert_eq!(a.x * b.x + a.y * b.y, ff8!(0.125));
    assert_eq!(a.dot(b), FixedFloat8::DELTA);
    let c = Vec3::new(ff8!(0.25), ff8!(0.25), ff8!(0.25));
    let e = Vec3::new(ff8!(0.125), ff8!(-0.125), ff8!(0.125));
    assert_eq!(
        c.cross(e),
        Vec3::new(FixedFloat8::DELTA, FixedFloat8::ZERO, ff8!(-0.0625))
    );
}

#[test]
fn fixed64_beyond_i128() {
    let (min, max) = (
        Vec3f64::splat(FixedFloat64::MIN),
        Vec3f64::splat(FixedFloat64::MAX),
    );
    assert_eq!(min.length_sq(), FixedFloat64::MAX);
    assert_eq!(min.dot(max), FixedFloat64::MIN);
    assert_eq!(min.length(), FixedFloat64::MAX);
    assert_eq!(
        Vec2::new(FixedFloat64::MIN, FixedFloat64::MIN)
            .dot(Vec2::new(FixedFloat64::MIN, FixedFloat64::MIN)),
        FixedFloat64::MAX
    );
    let big = FixedFloat64::from_bits(1 << 61);
    let v = Vec3f64::splat(big);
    assert_eq!(v.length_sq(), FixedFloat64::MAX);
    let l = i128::from(v.length().to_bits());
    assert!(is_root(l, 3 << 122, 64), "{}", l);
    assert!(l < i128::from(i64::MAX));
}

#[test]
fn bytes_round_trip() {
    let mut rng = Pcg32::new(7, 7);
    for _ in 0..10_000 {
        let v = Vec3::new(
            FixedFloat64::from_bits(rng.next_u64() as i64),
            FixedFloat64::from_bits(rng.next_u64() as i64),
            FixedFloat64::from_bits(rng.next_u64() as i64),
        );
        let le = v.to_le_bytes();
        assert_eq!(&le[..8], &v.x.to_le_bytes());
        assert_eq!(&le[8..16], &v.y.to_le_bytes());
        assert_eq!(&le[16..], &v.z.to_le_bytes());
        assert_eq!(Vec3f64::from_le_bytes(le), v);
        let be = v.to_be_bytes();
        assert_eq!(&be[16..], &v.z.to_be_bytes());
        assert_eq!(Vec3f64::from_be_bytes(be), v);
        let w = Vec2::new(v.x, v.y);
        assert_eq!(&w.to_le_bytes()[..], &le[..16]);
        assert_eq!(Vec2f64::from_le_bytes(w.to_le_bytes()), w);
        assert_eq!(Vec2f64::from_be_bytes(w.to_be_bytes()), w);
    }
    let v = Vec2::new(ff8!(1), ff8!(-0.5));
    assert_eq!(v.to_le_bytes(), [0x10, 0xf8]);
    assert_eq!(
        Vec3::new(ff16!(1), ff16!(0), ff16!(-1)).to_be_bytes(),
        [1, 0, 0, 0, 0xff, 0]
    );
    assert_eq!(
        Vec2::new(ff32!(1), ff32!(0)).to_le_bytes(),
        [0, 0, 1, 0, 0, 0, 0, 0]
    );
    assert_eq!(
        Vec3f8::from_le_bytes([0x10, 0x20, 0x30]),
        Vec3::new(ff8!(1), ff8!(2), ff8!(3))
    );
    assert_eq!(
        Vec2f16::from_le_bytes([0, 1, 0, 2]),
        Vec2::new(ff16!(1), ff16!(2))
    );
    assert_eq!(
        Vec3f32::from_be_bytes([0, 1, 0, 0, 0, 2, 0, 0, 0, 3, 0, 0]),
        Vec3::new(ff32!(1), ff32!(2), ff32!(3))
    );
}
