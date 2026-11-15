//! Reference sine and cosine in turns, written independently of the library:
//! octant symmetry to `φ ∈ [0, π/4]` and the full Taylor series of `sin φ` or
//! `cos φ` at 64 fractional bits on `u128`, without the quarter-circle table
//! and the short series of `src/trig.rs`.
//!
//! [`sin_turns`] returns `sin(2π·t) · 2^64` within [`ERROR`] of the true value,
//! where `t = raw / 2^f`; the rational oracle checks the bound
//! (`oracle/tests/trig.rs`).

/// Fractional bits of the reference values.
pub const SCALE: u32 = 64;

/// Bound on the error of [`sin_turns`] and [`cos_turns`], in units of `2^-64`.
pub const ERROR: i128 = 1 << 8;

/// `⌊π/4 · 2^64⌋`.
const FRAC_PI_4: u128 = 0xC90F_DAA2_2168_C234;

const ONE: u128 = 1 << 64;

fn mul(a: u128, b: u128) -> u128 {
    (a * b) >> 64
}

fn sin_series(phi: u128) -> u128 {
    let phi2 = mul(phi, phi);
    let mut term = phi;
    let mut sum = phi as i128;
    let mut n = 1u128;
    let mut negative = true;
    loop {
        term = mul(term, phi2) / ((n + 1) * (n + 2));
        n += 2;
        if term == 0 {
            return sum as u128;
        }
        sum += if negative {
            -(term as i128)
        } else {
            term as i128
        };
        negative = !negative;
    }
}

fn cos_series(phi: u128) -> u128 {
    let phi2 = mul(phi, phi);
    let mut term = phi2 / 2;
    let mut sum = ONE as i128 - term as i128;
    let mut n = 2u128;
    let mut negative = false;
    loop {
        term = mul(term, phi2) / ((n + 1) * (n + 2));
        n += 2;
        if term == 0 {
            return sum as u128;
        }
        sum += if negative {
            -(term as i128)
        } else {
            term as i128
        };
        negative = !negative;
    }
}

/// `sin(u·π/2) · 2^64` for `u = w / 2^62 ∈ [0, 1]`.
fn sin_quarter(w: u128) -> u128 {
    let half = 1u128 << 61;
    let angle = |w: u128| mul(w << 3, FRAC_PI_4);
    if w <= half {
        sin_series(angle(w))
    } else {
        cos_series(angle((1 << 62) - w))
    }
}

/// `sin(2π · raw / 2^f) · 2^64`, within [`ERROR`]. `1 ≤ f ≤ 64`.
pub fn sin_turns(raw: i128, f: u32) -> i128 {
    let t = (raw as u128) & ((1u128 << f) - 1);
    let t64 = t << (64 - f);
    let quadrant = t64 >> 62;
    let u = t64 & ((1 << 62) - 1);
    let m = match quadrant {
        0 | 2 => sin_quarter(u),
        _ => sin_quarter((1 << 62) - u),
    } as i128;
    if quadrant < 2 {
        m
    } else {
        -m
    }
}

/// `cos(2π · raw / 2^f) · 2^64`, within [`ERROR`]. `2 ≤ f ≤ 64`.
pub fn cos_turns(raw: i128, f: u32) -> i128 {
    sin_turns(raw + (1 << (f - 2)), f)
}

/// The value with `f` fractional bits nearest to `r / 2^64`, if every value
/// within [`ERROR`] of `r` rounds to it.
pub fn correctly_rounded(r: i128, f: u32) -> Option<i128> {
    let s = SCALE - f;
    let round = |v: i128| (v + (1 << (s - 1))) >> s;
    let lo = round(r - ERROR);
    if lo == round(r + ERROR) {
        Some(lo)
    } else {
        None
    }
}

/// `|got / 2^f - true value| < 2^-f` for every true value within [`ERROR`]
/// of `r`.
pub fn within_ulp(got: i128, r: i128, f: u32) -> bool {
    let ulp = 1i128 << (SCALE - f);
    ((got << (SCALE - f)) - r).abs() + ERROR < ulp
}
