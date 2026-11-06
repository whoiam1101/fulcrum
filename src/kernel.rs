//! Per-width arithmetic kernels.
//!
//! Every kernel returns the exact result, rounded to nearest with ties toward
//! `+∞`, as a value of the wide type. Saturation and wrapping are decided by
//! the caller, so one kernel serves the checked, wrapping, saturating and
//! overflowing variants.
//!
//! Widths 8..64 use the next native integer. Headroom: for `2N`-bit storage and
//! `N` fractional bits the wide type has `4N` bits, while the largest
//! intermediate below needs at most `3N + 1` bits for division and `4N - 1`
//! bits for multiplication.
//!
//! Written in the Rust subset that Aeneas understands (free functions over
//! primitives, no generic traits, no closures), see docs/ARCHITECTURE.md §6.1.4.

macro_rules! kernel {
    ($mul:ident, $div:ident, $round_div:ident, $Bits:ty, $Wide:ty, $UWide:ty, $F:expr) => {
        /// `round(a · b / 2^F)` for raw operands.
        #[inline]
        pub(crate) const fn $mul(a: $Bits, b: $Bits) -> $Wide {
            ((a as $Wide) * (b as $Wide) + (1 << ($F - 1))) >> $F
        }

        /// `round(n / d)`; `d` must be non-zero and `2·|n| + |d|` must fit
        /// the unsigned wide type.
        ///
        /// One unsigned division of the magnitudes: a positive result is
        /// `⌊(2|n| + |d|) / 2|d|⌋ = ⌊x + ½⌋`; a negative one, whose tie goes
        /// toward zero in magnitude, is `⌊(2|n| + |d| − 1) / 2|d|⌋ = ⌈x − ½⌉`.
        #[inline]
        pub(crate) const fn $round_div(n: $Wide, d: $Wide) -> $Wide {
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
        pub(crate) const fn $div(a: $Bits, b: $Bits) -> $Wide {
            $round_div((a as $Wide) << $F, b as $Wide)
        }
    };
}

kernel!(mul8, div8, round_div8, i8, i16, u16, 4);
kernel!(mul16, div16, round_div16, i16, i32, u32, 8);
kernel!(mul32, div32, round_div32, i32, i64, u64, 16);
kernel!(mul64, div64, round_div64, i64, i128, u128, 32);
