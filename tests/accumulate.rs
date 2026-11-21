//! Exact accumulators: the total does not depend on the order of terms, on how
//! they are split into parts, or on the order in which parts are merged.

#![cfg(not(feature = "strict-overflow"))]

#[macro_use]
mod common;

use common::{exact_dot, spec, Pcg32};
use fulcrum::*;

fn shuffle<T>(rng: &mut Pcg32, v: &mut [T]) {
    for i in (1..v.len()).rev() {
        let j = rng.below(i as u32 + 1) as usize;
        v.swap(i, j);
    }
}

macro_rules! order_suite {
    ($module:ident, $T:ident, $lit:ident, $Acc:ident, $Raw:ident, $bits:tt, $f:tt) => {
        mod $module {
            use super::*;

            #[test]
            fn sum_is_order_and_partition_independent() {
                let mut rng = Pcg32::new(11, $bits);
                for round in 0..200 {
                    let n = 1 + rng.below(300) as usize;
                    let mut v: Vec<$T> = (0..n)
                        .map(|_| {
                            $T::from_bits(rng.edge_bits($bits, $T::FRAC_BITS)
                                as <$T as fulcrum::FixedFloat>::Bits)
                        })
                        .collect();
                    let exact: i128 = v.iter().map(|x| i128::from(x.to_bits())).sum();
                    let expected = $T::from_bits(
                        spec::saturate(exact, $bits) as <$T as fulcrum::FixedFloat>::Bits
                    );

                    let sequential: $Acc =
                        v.iter().collect::<Vec<_>>().into_iter().copied().collect();
                    assert_eq!(sequential.finish(), expected, "round {}", round);
                    assert_eq!(v.iter().sum::<$T>(), expected);

                    for _ in 0..8 {
                        shuffle(&mut rng, &mut v);
                        let mut parts: Vec<$Acc> = Vec::new();
                        let mut i = 0;
                        while i < v.len() {
                            let len = 1 + rng.below(40) as usize;
                            let end = (i + len).min(v.len());
                            parts.push(v[i..end].iter().copied().collect());
                            i = end;
                        }
                        shuffle(&mut rng, &mut parts);
                        while parts.len() > 1 {
                            let a = parts.swap_remove(rng.below(parts.len() as u32) as usize);
                            let b = parts.swap_remove(rng.below(parts.len() as u32) as usize);
                            parts.push(if rng.next_u32() & 1 == 0 {
                                a.merge(b)
                            } else {
                                b.merge(a)
                            });
                        }
                        assert_eq!(parts[0], sequential);
                        assert_eq!(parts[0].finish(), expected);
                        assert_eq!(v.iter().sum::<$T>(), expected);
                    }
                }
            }

            #[test]
            fn saturation_happens_once_at_the_end() {
                let terms = [$T::MAX, $T::DELTA, -$T::DELTA];
                let orders = [
                    [0, 1, 2],
                    [0, 2, 1],
                    [1, 0, 2],
                    [1, 2, 0],
                    [2, 0, 1],
                    [2, 1, 0],
                ];
                for o in orders {
                    let s: $T = o.iter().map(|&i| terms[i]).sum();
                    assert_eq!(s, $T::MAX);
                }
                let mut acc = $T::accumulator();
                acc.add($T::MAX);
                acc.add($T::MAX);
                assert_eq!(acc.checked_finish(), None);
                assert_eq!(acc.finish(), $T::MAX);
                acc.sub($T::MAX);
                assert_eq!(acc.checked_finish(), Some($T::MAX));
            }

            #[test]
            fn dot_product_rounds_once() {
                let mut rng = Pcg32::new(12, $bits);
                for _ in 0..2000 {
                    let n = 1 + rng.below(64) as usize;
                    let a: Vec<$T> = (0..n)
                        .map(|_| {
                            $T::from_bits(rng.edge_bits($bits, $T::FRAC_BITS)
                                as <$T as fulcrum::FixedFloat>::Bits)
                        })
                        .collect();
                    let b: Vec<$T> = (0..n)
                        .map(|_| {
                            $T::from_bits(rng.edge_bits($bits, $T::FRAC_BITS)
                                as <$T as fulcrum::FixedFloat>::Bits)
                        })
                        .collect();
                    let expected =
                        spec::saturate(exact_dot(&a, &b, |x| i128::from(x.to_bits()), $f), $bits);
                    let mut forward = $Acc::new();
                    let mut backward = $Acc::new();
                    for i in 0..n {
                        forward.add_product(a[i], b[i]);
                        backward.add_product(b[n - 1 - i], a[n - 1 - i]);
                    }
                    assert_eq!(i128::from(forward.finish().to_bits()), expected);
                    assert_eq!(forward, backward);
                }
            }
        }
    };
}

for_each_width!(order_suite!());

#[test]
fn accumulator64_holds_more_than_i128() {
    type F = FixedFloat64;
    let mut acc = F::accumulator();
    for _ in 0..4 {
        acc.add_product(F::MAX, F::MAX);
    }
    assert_eq!(acc.checked_finish(), None);
    assert_eq!(acc.finish(), F::MAX);
    for _ in 0..4 {
        acc.add_product(F::MAX, -F::MAX);
    }
    acc.add_product(F::HALF, F::DELTA);
    assert_eq!(acc.checked_finish(), Some(F::DELTA));
    let mut neg = F::accumulator();
    for _ in 0..8 {
        neg.add_product(F::MIN, F::MAX);
    }
    assert_eq!(neg.finish(), F::MIN);
    neg.add(F::MAX);
    assert_eq!(neg.merge(neg).finish(), F::MIN);
}

#[test]
fn multiplication_is_commutative_but_not_associative() {
    let a = FixedFloat8::HALF;
    let b = FixedFloat8::HALF;
    let c = FixedFloat8::DELTA;
    assert_eq!(a * b, b * a);
    assert_eq!((a * b) * c, FixedFloat8::ZERO);
    assert_eq!(a * (b * c), FixedFloat8::DELTA);
    let four = FixedFloat8::from_bits(64);
    let quarter = FixedFloat8::from_bits(4);
    assert_eq!((four * four) * quarter, FixedFloat8::from_bits(32));
    assert_eq!(four * (four * quarter), four);
}

macro_rules! thread_safe {
    ($module:ident, $T:ident, $lit:ident, $Acc:ident, $Raw:ident, $bits:tt, $f:tt) => {
        assert_traits::<$T>();
        assert_traits::<$Acc>();
    };
}

fn assert_traits<T: Send + Sync + Unpin + Copy + 'static>() {}

#[test]
fn types_are_thread_safe_values() {
    for_each_width!(thread_safe!());
}

#[test]
fn accumulator8_product_plus_value_on_every_triple() {
    for a in i8::MIN..=i8::MAX {
        for b in i8::MIN..=i8::MAX {
            for c in i8::MIN..=i8::MAX {
                let (x, y, z) = (
                    FixedFloat8::from_bits(a),
                    FixedFloat8::from_bits(b),
                    FixedFloat8::from_bits(c),
                );
                let mut acc = FixedFloat8::accumulator();
                acc.add_product(x, y);
                acc.add(z);
                let exact = spec::mul_add(i128::from(a), i128::from(b), i128::from(c), 4);
                let expected = spec::saturate(exact, 8);
                assert_eq!(i128::from(acc.finish().to_bits()), expected, "{a} {b} {c}");
                assert_eq!(acc.checked_finish().is_some(), expected == exact);
                assert_eq!(acc.finish(), x.mul_add(y, z));
            }
        }
    }
}
