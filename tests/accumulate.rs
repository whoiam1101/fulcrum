//! Exact accumulators: the total does not depend on the order of terms, on how
//! they are split into parts, or on the order in which parts are merged.

#![cfg(not(feature = "strict-overflow"))]

mod common;

use common::{ref_round_div, Pcg32};
use fulcrum::{
    Accumulator16, Accumulator32, Accumulator64, Accumulator8, FixedFloat16, FixedFloat32,
    FixedFloat64, FixedFloat8,
};

fn shuffle<T>(rng: &mut Pcg32, v: &mut [T]) {
    for i in (1..v.len()).rev() {
        let j = rng.below(i as u32 + 1) as usize;
        v.swap(i, j);
    }
}

macro_rules! order_suite {
    ($module:ident, $T:ident, $Acc:ident, $bits:expr, $products:expr) => {
        mod $module {
            use super::*;

            fn clamp(v: i128) -> i128 {
                v.max(-(1i128 << ($bits - 1)))
                    .min((1i128 << ($bits - 1)) - 1)
            }

            #[test]
            fn sum_is_order_and_partition_independent() {
                let mut rng = Pcg32::new(11, $bits);
                for round in 0..200 {
                    let n = 1 + rng.below(300) as usize;
                    let mut v: Vec<$T> = (0..n)
                        .map(|_| $T::from_bits(rng.edge_bits($bits, $T::FRAC_BITS) as _))
                        .collect();
                    let exact: i128 = v.iter().map(|x| x.to_bits() as i128).sum();
                    let expected = $T::from_bits(clamp(exact) as _);

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
                if !$products {
                    return;
                }
                let mut rng = Pcg32::new(12, $bits);
                for _ in 0..2000 {
                    let n = 1 + rng.below(64) as usize;
                    let a: Vec<$T> = (0..n)
                        .map(|_| $T::from_bits(rng.edge_bits($bits, $T::FRAC_BITS) as _))
                        .collect();
                    let b: Vec<$T> = (0..n)
                        .map(|_| $T::from_bits(rng.edge_bits($bits, $T::FRAC_BITS) as _))
                        .collect();
                    let exact: i128 = a
                        .iter()
                        .zip(&b)
                        .map(|(x, y)| x.to_bits() as i128 * y.to_bits() as i128)
                        .sum();
                    let expected = clamp(ref_round_div(exact, 1i128 << $T::FRAC_BITS));
                    let mut forward = $Acc::new();
                    let mut backward = $Acc::new();
                    for i in 0..n {
                        dot_add(&mut forward, a[i], b[i]);
                        dot_add(&mut backward, b[n - 1 - i], a[n - 1 - i]);
                    }
                    assert_eq!(forward.finish().to_bits() as i128, expected);
                    assert_eq!(forward, backward);
                }
            }
        }
    };
}

trait DotAdd<T> {
    fn dot(&mut self, a: T, b: T);
}

macro_rules! dot_impl {
    ($Acc:ident, $T:ident) => {
        impl DotAdd<$T> for $Acc {
            fn dot(&mut self, a: $T, b: $T) {
                self.add_product(a, b);
            }
        }
    };
}

dot_impl!(Accumulator8, FixedFloat8);
dot_impl!(Accumulator16, FixedFloat16);
dot_impl!(Accumulator32, FixedFloat32);

impl DotAdd<FixedFloat64> for Accumulator64 {
    fn dot(&mut self, _: FixedFloat64, _: FixedFloat64) {
        unreachable!("add_product for FixedFloat64 needs U256 (stage 2)");
    }
}

fn dot_add<T, A: DotAdd<T>>(acc: &mut A, a: T, b: T) {
    acc.dot(a, b);
}

order_suite!(fixed8, FixedFloat8, Accumulator8, 8, true);
order_suite!(fixed16, FixedFloat16, Accumulator16, 16, true);
order_suite!(fixed32, FixedFloat32, Accumulator32, 32, true);
order_suite!(fixed64, FixedFloat64, Accumulator64, 64, false);

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

#[test]
fn types_are_thread_safe_values() {
    fn assert_traits<T: Send + Sync + Unpin + Copy + 'static>() {}
    assert_traits::<FixedFloat8>();
    assert_traits::<FixedFloat16>();
    assert_traits::<FixedFloat32>();
    assert_traits::<FixedFloat64>();
    assert_traits::<Accumulator8>();
    assert_traits::<Accumulator16>();
    assert_traits::<Accumulator32>();
    assert_traits::<Accumulator64>();
}
