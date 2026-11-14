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
