//! Per-width arithmetic kernels: everything that depends on the width of the
//! storage type or of its wide intermediate.
//!
//! `define_fixed!` names one module per type (`k8` … `k64`), and every module
//! has the same functions. Arithmetic outside the kernel does not cast to or
//! from the wide type `Wide`: it receives wide values from one kernel function
//! and hands them to another (`narrow`, `saturate`, `wrap`, `fits`).
//!
//! A second currency, independent of the width, is an `i128` with an explicit
//! scale. Conversions between widths, parsing, floats and the accumulators
//! produce it, and `checked_from_scaled_bits` or `wrapping_from_scaled_bits`
//! narrows it through [`rescale`]. For `k64` the wide type is `i128` as well;
//! there the two share a Rust type but not a meaning: a scaled `i128` carries
//! its own number of fractional bits.
//!
//! Every kernel that drops bits of an exact result rounds to nearest with ties
//! toward `+∞`, the rule of [`shr_round`]: `mul` and `midpoint` are
//! `shr_round` of the exact sum or product, `div` and `div_int` the same rule
//! for a quotient, `shr` the same rule on the storage type. The exceptions are
//! the named integer roundings of `round.rs`: `ceil`, `round_half_away` and
//! `round_ties_even`; `to_int` is exact on their results. Saturation and
//! wrapping are decided by the caller, so one kernel serves the checked,
//! wrapping, saturating and overflowing variants.
//!
//! Widths 8..64 use the next native integer. Headroom: for `2N`-bit storage and
//! `N` fractional bits the wide type has `4N` bits, while the largest
//! intermediate below needs at most `3N + 1` bits for division and `4N - 1`
//! bits for multiplication.
//!
//! Written in the Rust subset that Aeneas understands (free functions over
//! primitives, no generic traits, no closures), so that it can be translated
//! for the Lean proofs of later stages.

/// `round(n / 2^s)`, to nearest with ties toward `+∞`, for any `n` and `s`:
/// `⌊n / 2^s⌋` plus the first dropped bit, so nothing overflows. The one
/// rounding rule of the crate; [`magnitude_rounds_up`] is the same rule stated
/// on a sign and a magnitude.
#[inline]
pub(crate) const fn shr_round(n: i128, s: u32) -> i128 {
    if s == 0 {
        n
    } else if s >= 128 {
        0
    } else {
        (n >> s) + ((n >> (s - 1)) & 1)
    }
}

/// Whether a magnitude rounds up, to nearest with ties toward `+∞`, given its
/// first dropped bit `half` and whether any later dropped bit is set
/// (`sticky`). A tie rounds a positive magnitude up and a negative one down.
#[inline]
pub(crate) const fn magnitude_rounds_up(negative: bool, half: bool, sticky: bool) -> bool {
    half && (!negative || sticky)
}

/// `raw / 2^src_frac` rescaled to `dst_frac` fractional bits: [`shr_round`]
/// when bits are dropped, an exact shift otherwise. The second value is
/// whether the exact shift overflowed `i128`; the first is then its low bits.
#[inline]
pub(crate) const fn rescale(raw: i128, src_frac: u32, dst_frac: u32) -> (i128, bool) {
    if src_frac >= dst_frac {
        (shr_round(raw, src_frac - dst_frac), false)
    } else {
        let s = dst_frac - src_frac;
        (
            raw.wrapping_shl(s),
            raw > (i128::MAX >> s) || raw < (i128::MIN >> s),
        )
    }
}

macro_rules! kernel {
    (
        $k:ident, $Bits:ty, $Wide:ty, $UWide:ty, $Int:ty, $Frac:ty, $F:expr
    ) => {
        pub(crate) mod $k {
            /// The wide intermediate: room for every result before it is
            /// narrowed to the storage type.
            pub(crate) type Wide = $Wide;

            const ONE: $Wide = 1 << $F;
            const MASK: $Wide = ONE - 1;
            const HALF: $Wide = 1 << ($F - 1);

            /// `true` when `w` is a raw value of the storage type.
            #[inline]
            pub(crate) const fn fits(w: $Wide) -> bool {
                w >= <$Bits>::MIN as $Wide && w <= <$Bits>::MAX as $Wide
            }

            /// `w` as a raw value, or `None` when it is out of range.
            #[inline]
            pub(crate) const fn narrow(w: $Wide) -> Option<$Bits> {
                if fits(w) {
                    Some(w as $Bits)
                } else {
                    None
                }
            }

            /// `w` clamped to the range of the storage type.
            #[inline]
            pub(crate) const fn saturate(w: $Wide) -> $Bits {
                if w > <$Bits>::MAX as $Wide {
                    <$Bits>::MAX
                } else if w < <$Bits>::MIN as $Wide {
                    <$Bits>::MIN
                } else {
                    w as $Bits
                }
            }

            /// `w` modulo `2^BITS`, as a raw value.
            #[inline]
            pub(crate) const fn wrap(w: $Wide) -> $Bits {
                w as $Bits
            }

            /// `w` as an integer: `⌊w / 2^F⌋`, for `w` a multiple of `2^F`
            /// whose integer fits the storage type.
            #[inline]
            pub(crate) const fn to_int(w: $Wide) -> $Bits {
                (w >> $F) as $Bits
            }

            /// The raw value of `int + frac / 2^F`.
            #[inline]
            pub(crate) const fn from_parts(int: $Int, frac: $Frac) -> $Wide {
                ((int as $Wide) << $F) + frac as $Wide
            }

            /// `round(a · b / 2^F)` for raw operands. Equal to
            /// `shr_round(a · b, F)`; the headroom lets the half be added first.
            #[inline]
            pub(crate) const fn mul(a: $Bits, b: $Bits) -> $Wide {
                ((a as $Wide) * (b as $Wide) + HALF) >> $F
            }

            /// `round(n / d)`; `d` must be non-zero and `2·|n| + |d|` must fit
            /// the unsigned wide type.
            ///
            /// One unsigned division of the magnitudes: a positive result is
            /// `⌊(2|n| + |d|) / 2|d|⌋ = ⌊x + ½⌋`; a negative one, whose tie goes
            /// toward zero in magnitude, is `⌊(2|n| + |d| − 1) / 2|d|⌋ = ⌈x − ½⌉`.
            #[inline]
            const fn round_div(n: $Wide, d: $Wide) -> $Wide {
                let negative = (n < 0) != (d < 0);
                let un = n.unsigned_abs();
                let ud = d.unsigned_abs();
                let m = ((un << 1) + ud - negative as $UWide) / (ud << 1);
                let m = m as $Wide;
                if negative {
                    -m
                } else {
                    m
                }
            }

            /// `round(a · 2^F / b)` for raw operands; `b` must be non-zero.
            #[inline]
            pub(crate) const fn div(a: $Bits, b: $Bits) -> $Wide {
                round_div((a as $Wide) << $F, b as $Wide)
            }

            /// `round(a / n)` for a raw `a` and an integer `n`; `n` must be non-zero.
            #[inline]
            pub(crate) const fn div_int(a: $Bits, n: $Bits) -> $Wide {
                round_div(a as $Wide, n as $Wide)
            }

            /// `⌈(a + b) / 2⌉ = shr_round(a + b, 1)` without overflow.
            #[inline]
            pub(crate) const fn midpoint(a: $Bits, b: $Bits) -> $Bits {
                (a | b) - ((a ^ b) >> 1)
            }

            /// `round(a / 2^n)` for any `n`: `shr_round` on the storage type,
            /// so `a >> n` agrees with `a / 2^n`. Never overflows.
            #[inline]
            pub(crate) const fn shr(a: $Bits, n: u32) -> $Bits {
                if n == 0 {
                    a
                } else if n >= <$Bits>::BITS {
                    0
                } else {
                    (a >> n) + ((a >> (n - 1)) & 1)
                }
            }

            /// `a · 2^n` and whether it overflowed the storage type; the value
            /// is the low bits of the exact product (`0` when `n ≥ BITS`).
            #[inline]
            pub(crate) const fn shl(a: $Bits, n: u32) -> ($Bits, bool) {
                if n >= <$Bits>::BITS {
                    (0, a != 0)
                } else {
                    let r = a << n;
                    (r, (r >> n) != a)
                }
            }

            /// Smallest multiple of `2^F` that is `≥ a`.
            #[inline]
            pub(crate) const fn ceil(a: $Bits) -> $Wide {
                ((a as $Wide) + MASK) & !MASK
            }

            /// Nearest multiple of `2^F`, ties away from zero.
            #[inline]
            pub(crate) const fn round_half_away(a: $Bits) -> $Wide {
                let w = a as $Wide;
                if w >= 0 {
                    (w + HALF) & !MASK
                } else {
                    -((HALF - w) & !MASK)
                }
            }

            /// Nearest multiple of `2^F`, ties to even.
            #[inline]
            pub(crate) const fn round_ties_even(a: $Bits) -> $Wide {
                let w = a as $Wide;
                let floor = w & !MASK;
                let frac = w & MASK;
                let odd = (w >> $F) & 1 == 1;
                if frac > HALF || (frac == HALF && odd) {
                    floor + ONE
                } else {
                    floor
                }
            }
        }
    };
}

kernel!(k8, i8, i16, u16, i8, u8, 4);
kernel!(k16, i16, i32, u32, i8, u8, 8);
kernel!(k32, i32, i64, u64, i16, u16, 16);
kernel!(k64, i64, i128, u128, i32, u32, 32);
