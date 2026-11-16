//! Shared inputs for the benchmarks: deterministic pseudo-random operands,
//! and the accuracy tables of the square roots and of trigonometry.

pub mod accuracy;
pub mod tick;
pub mod trig_accuracy;

/// `n` pseudo-random `u64` values from a fixed seed (SplitMix64).
pub fn inputs(n: usize, seed: u64) -> Vec<u64> {
    let mut s = seed;
    (0..n)
        .map(|_| {
            s = s.wrapping_add(0x9e37_79b9_7f4a_7c15);
            let mut z = s;
            z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            z ^ (z >> 31)
        })
        .collect()
}

/// A Q16.16 raw operand in `[-2, 2)`.
pub fn operand(x: u64) -> i64 {
    ((x >> 40) as i64 & ((1 << 18) - 1)) - (1 << 17)
}

/// A Q16.16 raw divisor in `±[0.5, 2)`.
pub fn divisor(x: u64) -> i64 {
    let m = (1 << 15) + ((x >> 40) as i64 % (3 << 15));
    if x & 1 == 0 {
        m
    } else {
        -m
    }
}

/// A Q16.16 raw operand in `(0, 256)`.
pub fn radicand(x: u64) -> i64 {
    ((x >> 40) as i64 & ((1 << 24) - 1)) | 1
}

/// A Q16.16 raw operand as a `FixedFloat8` (Q4.4).
pub fn ff8(q: i64) -> fulcrum::FixedFloat8 {
    fulcrum::FixedFloat8::from_bits((q >> 12) as i8)
}

/// A Q16.16 raw operand as a `FixedFloat16` (Q8.8).
pub fn ff16(q: i64) -> fulcrum::FixedFloat16 {
    fulcrum::FixedFloat16::from_bits((q >> 8) as i16)
}

/// A Q16.16 raw operand as a `FixedFloat32` (Q16.16).
pub fn ff32(q: i64) -> fulcrum::FixedFloat32 {
    fulcrum::FixedFloat32::from_bits(q as i32)
}

/// A Q16.16 raw operand as a Q32.32 raw value.
pub fn q32_32(q: i64) -> i64 {
    q << 16
}

/// A Q16.16 raw operand as a `FixedFloat64` (Q32.32).
pub fn ff64(q: i64) -> fulcrum::FixedFloat64 {
    fulcrum::FixedFloat64::from_bits(q32_32(q))
}
