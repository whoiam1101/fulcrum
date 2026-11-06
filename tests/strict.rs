//! `strict-overflow`: operators panic instead of saturating, explicit methods
//! keep their semantics. Run with `cargo test --features strict-overflow --test strict`.

#![cfg(feature = "strict-overflow")]

use fulcrum::{FixedFloat64, FixedFloat8};

#[test]
#[should_panic(expected = "strict-overflow")]
fn add_overflow_panics() {
    let _ = FixedFloat8::MAX + FixedFloat8::DELTA;
}

#[test]
#[should_panic(expected = "strict-overflow")]
fn mul_overflow_panics() {
    let _ = FixedFloat64::MAX * FixedFloat64::MAX;
}

#[test]
#[should_panic(expected = "strict-overflow")]
fn division_by_zero_panics() {
    let _ = FixedFloat64::ONE / FixedFloat64::ZERO;
}

#[test]
#[should_panic(expected = "strict-overflow")]
fn remainder_by_zero_panics() {
    let _ = FixedFloat64::ONE % FixedFloat64::ZERO;
}

#[test]
#[should_panic(expected = "strict-overflow")]
fn neg_min_panics() {
    let _ = -FixedFloat8::MIN;
}

#[test]
#[should_panic(expected = "strict-overflow")]
fn assign_overflow_panics() {
    let mut x = FixedFloat8::MIN;
    x -= FixedFloat8::DELTA;
}

#[test]
#[should_panic(expected = "strict-overflow")]
fn sum_overflow_panics() {
    let _: FixedFloat8 = [FixedFloat8::MAX, FixedFloat8::MAX].iter().sum();
}

#[test]
fn in_range_operations_and_explicit_methods_do_not_panic() {
    let x = FixedFloat64::from_bits(3 << 31);
    assert_eq!(x + x, FixedFloat64::from_bits(3 << 32));
    assert_eq!(
        FixedFloat64::MAX.saturating_add(FixedFloat64::ONE),
        FixedFloat64::MAX
    );
    assert_eq!(
        FixedFloat64::ONE.saturating_div(FixedFloat64::ZERO),
        FixedFloat64::MAX
    );
    assert_eq!(
        FixedFloat64::MAX.wrapping_add(FixedFloat64::DELTA),
        FixedFloat64::MIN
    );
    let s: FixedFloat8 = [FixedFloat8::MAX, FixedFloat8::DELTA, -FixedFloat8::DELTA]
        .iter()
        .sum();
    assert_eq!(s, FixedFloat8::MAX);
}
