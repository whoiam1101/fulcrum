//! Determinism: a fixed pseudo-random sequence of operations on every width is
//! hashed, and the hash is compared to a constant committed in the repository.
//! The same constant must come out on every target, in debug and in release
//! (docs/ARCHITECTURE.md §5). Changing semantics on purpose means updating the
//! constant together with a decision log entry.

#![cfg(not(feature = "strict-overflow"))]

#[macro_use]
mod common;

use common::{Fnv, Pcg32};
use fulcrum::*;

const ROUNDS: usize = 250_000;
const GOLDEN: u64 = 0xf591_0583_d96b_51bd;

macro_rules! mix {
    ($h:ident, $rng:ident, $module:ident, $T:ident, $lit:ident, $Acc:ident, $Raw:ident, $bits:tt, $f:tt) => {{
        let a = $T::from_bits($rng.edge_bits($bits, $T::FRAC_BITS) as _);
        let b = $T::from_bits($rng.edge_bits($bits, $T::FRAC_BITS) as _);
        for v in [
            a + b,
            a - b,
            a * b,
            a / b,
            a % b,
            a.wrapping_mul(b),
            a.wrapping_div(b),
            a.div_int(b.to_bits()),
            a.midpoint(b),
            a.round(),
            a.round_ties_even(),
            a.ceil(),
            a.recip(),
            a.mul_add(b, a),
            a.mul_div(b, a),
            a.lerp(b, a),
        ] {
            $h.write(&v.to_le_bytes());
        }
        let mut acc = $T::accumulator();
        acc.add(a);
        acc.add(b);
        acc.sub(a.wrapping_mul(b));
        acc.add_product(a, b);
        $h.write(&acc.finish().to_le_bytes());
        $h.write(&[a, b, a].iter().sum::<$T>().to_le_bytes());
        let text = a.to_string();
        $h.write(text.as_bytes());
        $h.write(&text.parse::<$T>().unwrap().to_le_bytes());
    }};
}

fn compute() -> u64 {
    let mut rng = Pcg32::new(0x5eed_f00d, 54);
    let mut h = Fnv::new();
    for _ in 0..ROUNDS {
        for_each_width!(mix!(h, rng,));
    }
    h.finish()
}

#[test]
fn golden_hash() {
    let hash = compute();
    assert_eq!(
        hash, GOLDEN,
        "determinism hash changed: got {:#018x}, expected {:#018x}",
        hash, GOLDEN
    );
}
