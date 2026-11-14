//! The one integer reference of the spec (docs/INTERNALS.md §6): rounding to
//! nearest with ties toward `+∞`, saturation, wrapping, division by zero,
//! rescaling and the rounded operations, written independently of the
//! library kernels: exact quotient and remainder instead of a shifted sum.
//!
//! `reference!(m, R)` defines the module `m` with every function over the
//! integer type `R`. Tests use `i128`; the Kani proofs also use `i32` and
//! `i64`, where the solver is faster. The rational oracle checks this file
//! (`oracle/tests/reference.rs`), and this file checks the library.
//!
//! Plain `core` integer arithmetic only, so the `no_std` crate can include it.
//! Every function states its domain; outside it the reference itself may
//! overflow. Crates and modules outside `tests/` include this file with
//! `#[macro_use] #[path = "…/tests/common/reference.rs"] mod reference;`.

#![allow(unused_macros)]

/// Defines module `$m` with the reference functions over the integer `$R`.
macro_rules! reference {
    ($m:ident, $R:ty) => {
        /// The reference functions over one integer type.
        #[allow(dead_code)]
        pub mod $m {
            /// `round(n / d)`, ties toward `+∞`, via the exact quotient and
            /// remainder. `d ≠ 0`, `n > MIN` when `d < 0`, `|d| ≤ MAX / 2`.
            pub fn round_div(n: $R, d: $R) -> $R {
                assert!(d != 0);
                let (n, d) = if d < 0 { (-n, -d) } else { (n, d) };
                let q = n.div_euclid(d);
                let r = n.rem_euclid(d);
                if 2 * r >= d {
                    q + 1
                } else {
                    q
                }
            }

            /// `round(n / 2^f)`, ties toward `+∞`, via the exact quotient and
            /// the dropped bits. `f ≤ BITS - 2`; `f = 0` gives `n`.
            pub fn round_shift(n: $R, f: u32) -> $R {
                if f == 0 {
                    return n;
                }
                let q = n >> f;
                let r = n & ((1 << f) - 1);
                if r >= 1 << (f - 1) {
                    q + 1
                } else {
                    q
                }
            }

            /// `raw / 2^src` rescaled to `dst` fractional bits: rounded when bits
            /// are dropped, exact otherwise; `None` when the exact value does
            /// not fit `R`. `src - dst ≤ BITS - 2`.
            pub fn rescale(raw: $R, src: u32, dst: u32) -> Option<$R> {
                if src >= dst {
                    Some(round_shift(raw, src - dst))
                } else {
                    raw.checked_mul(1 << (dst - src))
                }
            }

            /// The raw product `round(a · b / 2^f)`, before saturation.
            pub fn mul(a: $R, b: $R, f: u32) -> $R {
                round_shift(a * b, f)
            }

            /// The raw quotient `round(a · 2^f / b)`, before saturation; `b ≠ 0`.
            pub fn div(a: $R, b: $R, f: u32) -> $R {
                round_div(a << f, b)
            }

            /// `round((a · b + c · 2^f) / 2^f)`: `mul_add` rounded once, before
            /// saturation.
            pub fn mul_add(a: $R, b: $R, c: $R, f: u32) -> $R {
                round_shift(a * b + (c << f), f)
            }

            /// `round(a · b / c)`: `mul_div` rounded once, before saturation;
            /// `c ≠ 0`.
            pub fn mul_div(a: $R, b: $R, c: $R) -> $R {
                round_div(a * b, c)
            }

            /// `a + round((b - a) · t / 2^f)`: `lerp` rounded once, before
            /// saturation.
            pub fn lerp(a: $R, b: $R, t: $R, f: u32) -> $R {
                a + round_shift((b - a) * t, f)
            }

            /// `round(√(num / den))`, ties toward `+∞` (a square root of a
            /// rational has none: `(2s + 1)² · den = 4 · num` needs an odd
            /// square dividing a power of two times `num`, checked exactly
            /// all the same). The floor is the largest `s` with
            /// `s² · den ≤ num`, found by binary search with checked
            /// products, not by Newton's iteration. `num ≥ 0`, `den > 0`,
            /// `4 · num` and `(2s + 1)² · den` fit `R`.
            pub fn sqrt_ratio(num: $R, den: $R) -> $R {
                assert!(num >= 0 && den > 0);
                let le = |s: $R| match s.checked_mul(s).and_then(|q| q.checked_mul(den)) {
                    Some(q) => q <= num,
                    None => false,
                };
                let mut lo: $R = 0;
                let mut hi: $R = 1;
                while le(hi) {
                    lo = hi;
                    hi *= 2;
                }
                while hi - lo > 1 {
                    let mid = lo + (hi - lo) / 2;
                    if le(mid) {
                        lo = mid;
                    } else {
                        hi = mid;
                    }
                }
                let up = (2 * lo + 1) * (2 * lo + 1) * den;
                if up <= 4 * num {
                    lo + 1
                } else {
                    lo
                }
            }

            /// `round(√n)` for `n ≥ 0`: [`sqrt_ratio`] with `den = 1`.
            pub fn sqrt(n: $R) -> $R {
                sqrt_ratio(n, 1)
            }

            /// Whether `s` is `round(√(num / den))`, ties toward `+∞`:
            /// `s - ½ ≤ √(num / den) < s + ½`, that is
            /// `(2s - 1)² · den ≤ 4 · num < (2s + 1)² · den`, the lower
            /// bound dropped for `s = 0`. A check without a search, for
            /// exhaustive runs. `s ≥ 0`, `num ≥ 0`, `den > 0`, and
            /// `(2s + 1)² · den` and `4 · num` fit `R`.
            pub fn is_sqrt_ratio(s: $R, num: $R, den: $R) -> bool {
                let below = (2 * s + 1) * (2 * s + 1) * den;
                let above = (2 * s - 1) * (2 * s - 1) * den;
                s >= 0 && 4 * num < below && (s == 0 || above <= 4 * num)
            }

            /// `v` clamped to the range of a signed `bits`-bit integer;
            /// `bits < BITS`.
            pub fn saturate(v: $R, bits: u32) -> $R {
                let min = -(1 << (bits - 1));
                let max = (1 << (bits - 1)) - 1;
                if v > max {
                    max
                } else if v < min {
                    min
                } else {
                    v
                }
            }

            /// Whether `v` is in the range of a signed `bits`-bit integer.
            pub fn fits(v: $R, bits: u32) -> bool {
                saturate(v, bits) == v
            }

            /// The low `bits` bits of `v`, sign-extended.
            pub fn wrap(v: $R, bits: u32) -> $R {
                let shift = <$R>::BITS - bits;
                (v << shift) >> shift
            }

            /// The result of dividing a value of sign `sign` by zero: `MAX`,
            /// `MIN` or `0` of a signed `bits`-bit integer.
            pub fn div_by_zero(sign: $R, bits: u32) -> $R {
                if sign > 0 {
                    (1 << (bits - 1)) - 1
                } else if sign < 0 {
                    -(1 << (bits - 1))
                } else {
                    0
                }
            }
        }
    };
}
