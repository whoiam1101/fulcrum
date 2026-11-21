//! Strategies shared by the property tests of the oracle.

use proptest::prelude::*;

/// A raw value of `bits` bits with `frac` fractional bits, biased toward
/// edge cases: 0, ±1 ulp, ±1, ½, MIN, MAX and their neighbours, powers of
/// two and small values.
pub fn edge(bits: u32, frac: u32) -> impl Strategy<Value = i128> {
    let min = i128::MIN >> (128 - bits);
    let max = i128::MAX >> (128 - bits);
    let one = 1i128 << frac;
    let full = (min..=max).boxed();
    prop_oneof![
        1 => Just(0i128),
        1 => Just(1i128),
        1 => Just(-1i128),
        1 => Just(one),
        1 => Just(-one),
        1 => Just(one / 2),
        1 => Just(min),
        1 => Just(max),
        1 => Just(min + 1),
        1 => Just(max - 1),
        2 => (0..bits - 1, any::<bool>()).prop_map(|(k, n)| if n { -(1i128 << k) } else { 1i128 << k }),
        2 => -4 * one..=4 * one,
        8 => full,
    ]
}
