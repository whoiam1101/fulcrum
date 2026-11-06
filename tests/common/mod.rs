//! Shared test helpers without external crates: a PCG32 generator and
//! edge-biased value generators.

#![allow(dead_code)]

/// PCG-XSH-RR 64/32 (O'Neill, 2014).
pub struct Pcg32 {
    state: u64,
    inc: u64,
}

impl Pcg32 {
    pub fn new(seed: u64, stream: u64) -> Self {
        let mut rng = Self {
            state: 0,
            inc: (stream << 1) | 1,
        };
        rng.next_u32();
        rng.state = rng.state.wrapping_add(seed);
        rng.next_u32();
        rng
    }

    pub fn next_u32(&mut self) -> u32 {
        let old = self.state;
        self.state = old
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(self.inc);
        let xorshifted = (((old >> 18) ^ old) >> 27) as u32;
        let rot = (old >> 59) as u32;
        xorshifted.rotate_right(rot)
    }

    pub fn next_u64(&mut self) -> u64 {
        ((self.next_u32() as u64) << 32) | self.next_u32() as u64
    }

    pub fn below(&mut self, n: u32) -> u32 {
        ((self.next_u32() as u64 * n as u64) >> 32) as u32
    }

    /// Raw value of `bits` bits, biased toward edge cases: 0, ±1 ulp, ±1,
    /// MIN, MAX, MIN + 1, powers of two, small values and sign changes.
    pub fn edge_bits(&mut self, bits: u32, frac_bits: u32) -> i64 {
        let min = if bits == 64 {
            i64::MIN
        } else {
            -(1i64 << (bits - 1))
        };
        let max = if bits == 64 {
            i64::MAX
        } else {
            (1i64 << (bits - 1)) - 1
        };
        let one = 1i64 << frac_bits;
        let sign = |r: &mut Self, v: i64| {
            if r.next_u32() & 1 == 0 {
                v
            } else {
                v.wrapping_neg()
            }
        };
        let v = match self.below(12) {
            0 => 0,
            1 => sign(self, 1),
            2 => sign(self, one),
            3 => min,
            4 => max,
            5 => min + 1,
            6 => max - 1,
            7 => {
                let p = 1i64 << self.below(bits - 1);
                sign(self, p)
            }
            8 => {
                let small = (self.next_u32() as i64) & (one * 4 - 1);
                sign(self, small)
            }
            9 => sign(self, one / 2),
            _ => self.next_u64() as i64,
        };
        let shift = 64 - bits;
        (v << shift) >> shift
    }
}

/// FNV-1a, 64 bit.
pub struct Fnv(u64);

impl Fnv {
    pub fn new() -> Self {
        Self(0xcbf2_9ce4_8422_2325)
    }

    pub fn write(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.0 ^= b as u64;
            self.0 = self.0.wrapping_mul(0x0100_0000_01b3);
        }
    }

    pub fn finish(&self) -> u64 {
        self.0
    }
}

/// Reference rounding `floor(n / d + 1/2)` written independently of the
/// library kernels: via the exact quotient and remainder.
pub fn ref_round_div(n: i128, d: i128) -> i128 {
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

pub fn clamp(v: i128, bits: u32) -> i128 {
    let min = -(1i128 << (bits - 1));
    let max = (1i128 << (bits - 1)) - 1;
    v.max(min).min(max)
}

pub fn fits(v: i128, bits: u32) -> bool {
    clamp(v, bits) == v
}

pub fn wrap(v: i128, bits: u32) -> i128 {
    let shift = 128 - bits;
    (v << shift) >> shift
}

pub fn div_by_zero(a: i128, bits: u32) -> i128 {
    match a.signum() {
        1 => (1i128 << (bits - 1)) - 1,
        -1 => -(1i128 << (bits - 1)),
        _ => 0,
    }
}

pub fn exact_decimal(raw: i128, frac_bits: u32) -> String {
    let neg = raw < 0;
    let mag = raw.unsigned_abs();
    let int = mag >> frac_bits;
    let frac = mag & ((1u128 << frac_bits) - 1);
    let scaled = frac * 5u128.pow(frac_bits);
    let mut digits = format!("{:0w$}", scaled, w = frac_bits as usize);
    while digits.ends_with('0') {
        digits.pop();
    }
    let sign = if neg { "-" } else { "" };
    if digits.is_empty() {
        format!("{}{}", sign, int)
    } else {
        format!("{}{}.{}", sign, int, digits)
    }
}

pub fn rounded_decimal(raw: i128, frac_bits: u32, precision: u32) -> String {
    let neg = raw < 0;
    let mag = raw.unsigned_abs() as i128;
    let n = mag * 10i128.pow(precision);
    let d = 1i128 << frac_bits;
    let q = n / d;
    let r = n % d;
    let q = if 2 * r > d || (2 * r == d && q % 2 == 1) {
        q + 1
    } else {
        q
    };
    let p = 10i128.pow(precision);
    let sign = if neg { "-" } else { "" };
    if precision == 0 {
        format!("{}{}", sign, q)
    } else {
        format!("{}{}.{:0w$}", sign, q / p, q % p, w = precision as usize)
    }
}

#[allow(unused_macros)]
macro_rules! check_pair {
    ($T:ident, $bits:expr, $f:expr, $a:expr, $b:expr) => {{
        let (ra, rb): (i128, i128) = ($a as i128, $b as i128);
        let x = $T::from_bits($a);
        let y = $T::from_bits($b);
        let ctx = || format!("{} {} ({:?}, {:?})", stringify!($T), "", x, y);

        let sum = ra + rb;
        assert_eq!(
            x.saturating_add(y).to_bits() as i128,
            clamp(sum, $bits),
            "add {}",
            ctx()
        );
        assert_eq!(
            x.wrapping_add(y).to_bits() as i128,
            wrap(sum, $bits),
            "wrapping_add {}",
            ctx()
        );
        assert_eq!(
            x.checked_add(y).is_some(),
            fits(sum, $bits),
            "checked_add {}",
            ctx()
        );

        let diff = ra - rb;
        assert_eq!(
            (x - y).to_bits() as i128,
            clamp(diff, $bits),
            "sub {}",
            ctx()
        );
        assert_eq!(
            x.overflowing_sub(y),
            ($T::from_bits(wrap(diff, $bits) as _), !fits(diff, $bits)),
            "overflowing_sub {}",
            ctx()
        );

        let prod = crate::common::ref_round_div(ra * rb, 1i128 << $f);
        assert_eq!(
            (x * y).to_bits() as i128,
            clamp(prod, $bits),
            "mul {}",
            ctx()
        );
        assert_eq!(
            x.wrapping_mul(y).to_bits() as i128,
            wrap(prod, $bits),
            "wrapping_mul {}",
            ctx()
        );
        assert_eq!(
            x.overflowing_mul(y).1,
            !fits(prod, $bits),
            "overflowing_mul {}",
            ctx()
        );
        assert_eq!(
            x.checked_mul(y).map(|v| v.to_bits() as i128),
            Some(prod).filter(|p| fits(*p, $bits)),
            "checked_mul {}",
            ctx()
        );

        if rb == 0 {
            assert_eq!(
                (x / y).to_bits() as i128,
                div_by_zero(ra, $bits),
                "div0 {}",
                ctx()
            );
            assert_eq!(x.checked_div(y), None, "checked_div0 {}", ctx());
            assert_eq!(
                x.overflowing_div(y),
                (x / y, true),
                "overflowing_div0 {}",
                ctx()
            );
            assert_eq!((x % y).to_bits(), 0, "rem0 {}", ctx());
            assert_eq!(x.checked_rem(y), None, "checked_rem0 {}", ctx());
        } else {
            let quot = crate::common::ref_round_div(ra << $f, rb);
            assert_eq!(
                (x / y).to_bits() as i128,
                clamp(quot, $bits),
                "div {}",
                ctx()
            );
            assert_eq!(
                x.wrapping_div(y).to_bits() as i128,
                wrap(quot, $bits),
                "wrapping_div {}",
                ctx()
            );
            assert_eq!(
                x.checked_div(y).map(|v| v.to_bits() as i128),
                Some(quot).filter(|q| fits(*q, $bits)),
                "checked_div {}",
                ctx()
            );
            let rem = ra - rb * (ra / rb);
            assert_eq!((x % y).to_bits() as i128, rem, "rem {}", ctx());
            let int_quot = crate::common::ref_round_div(ra, rb);
            assert_eq!(
                x.div_int($b).to_bits() as i128,
                clamp(int_quot, $bits),
                "div_int {}",
                ctx()
            );
        }

        let mul_int = ra * rb;
        assert_eq!(
            x.mul_int($b).to_bits() as i128,
            clamp(mul_int, $bits),
            "mul_int {}",
            ctx()
        );

        let mid = crate::common::ref_round_div(ra + rb, 2);
        assert_eq!(x.midpoint(y).to_bits() as i128, mid, "midpoint {}", ctx());
        assert_eq!(x.min(y).to_bits() as i128, ra.min(rb), "min {}", ctx());
        assert_eq!(x.max(y).to_bits() as i128, ra.max(rb), "max {}", ctx());
        assert_eq!(
            x.abs_diff(y).to_bits() as i128,
            clamp((ra - rb).abs(), $bits),
            "abs_diff {}",
            ctx()
        );
        assert_eq!(x.cmp(&y), ra.cmp(&rb), "cmp {}", ctx());
    }};
}

#[allow(unused_macros)]
macro_rules! check_unary {
    ($T:ident, $bits:expr, $f:expr, $a:expr) => {
        check_unary!($T, $bits, $f, $a, $f + 1)
    };
    ($T:ident, $bits:expr, $f:expr, $a:expr, $max_precision:expr) => {{
        let ra = $a as i128;
        let x = $T::from_bits($a);
        let one = 1i128 << $f;
        let floor = ra.div_euclid(one) * one;
        let ceil = -((-ra).div_euclid(one) * one);
        let trunc = if ra < 0 { ceil } else { floor };
        let away = if ra >= 0 {
            (ra + one / 2).div_euclid(one) * one
        } else {
            -((-ra + one / 2).div_euclid(one) * one)
        };
        let q = ra.div_euclid(one);
        let r = ra.rem_euclid(one);
        let even = if 2 * r > one || (2 * r == one && q % 2 != 0) {
            (q + 1) * one
        } else {
            q * one
        };

        assert_eq!(x.floor().to_bits() as i128, floor, "floor {:?}", x);
        assert_eq!(
            x.ceil().to_bits() as i128,
            clamp(ceil, $bits),
            "ceil {:?}",
            x
        );
        assert_eq!(
            x.checked_ceil().is_some(),
            fits(ceil, $bits),
            "checked_ceil {:?}",
            x
        );
        assert_eq!(x.trunc().to_bits() as i128, trunc, "trunc {:?}", x);
        assert_eq!(x.fract().to_bits() as i128, ra - trunc, "fract {:?}", x);
        assert_eq!(
            x.round().to_bits() as i128,
            clamp(away, $bits),
            "round {:?}",
            x
        );
        assert_eq!(
            x.round_ties_even().to_bits() as i128,
            clamp(even, $bits),
            "round_ties_even {:?}",
            x
        );
        assert_eq!(
            x.to_int_floor() as i128,
            floor / one,
            "to_int_floor {:?}",
            x
        );
        assert_eq!(x.to_int_ceil() as i128, ceil / one, "to_int_ceil {:?}", x);
        assert_eq!(
            x.to_int_trunc() as i128,
            trunc / one,
            "to_int_trunc {:?}",
            x
        );
        assert_eq!(x.to_int_round() as i128, away / one, "to_int_round {:?}", x);
        assert_eq!(
            x.to_int_round_ties_even() as i128,
            even / one,
            "to_int_round_ties_even {:?}",
            x
        );

        assert_eq!((-x).to_bits() as i128, clamp(-ra, $bits), "neg {:?}", x);
        assert_eq!(
            x.wrapping_neg().to_bits() as i128,
            wrap(-ra, $bits),
            "wrapping_neg {:?}",
            x
        );
        assert_eq!(
            x.checked_neg().is_some(),
            fits(-ra, $bits),
            "checked_neg {:?}",
            x
        );
        assert_eq!(
            x.abs().to_bits() as i128,
            clamp(ra.abs(), $bits),
            "abs {:?}",
            x
        );
        assert_eq!(
            x.signum().to_bits() as i128,
            ra.signum() * one,
            "signum {:?}",
            x
        );
        let recip = if ra == 0 {
            div_by_zero(one, $bits)
        } else {
            clamp(crate::common::ref_round_div(one << $f, ra), $bits)
        };
        assert_eq!(x.recip().to_bits() as i128, recip, "recip {:?}", x);

        assert_eq!(x.int_part() as i128, ra.div_euclid(one), "int_part {:?}", x);
        assert_eq!(
            x.frac_part() as i128,
            ra.rem_euclid(one),
            "frac_part {:?}",
            x
        );
        assert_eq!(
            $T::from_parts(x.int_part(), x.frac_part()),
            x,
            "from_parts {:?}",
            x
        );
        assert_eq!($T::from_le_bytes(x.to_le_bytes()), x, "le bytes {:?}", x);
        assert_eq!($T::from_be_bytes(x.to_be_bytes()), x, "be bytes {:?}", x);
        assert_eq!(x.to_le_bytes(), ($a).to_le_bytes(), "le layout {:?}", x);

        let text = x.to_string();
        assert_eq!(text, exact_decimal(ra, $f), "display {:?}", x);
        assert_eq!(text.parse::<$T>(), Ok(x), "parse(display) {:?}", x);
        for p in 0..=$max_precision {
            assert_eq!(
                format!("{:.*}", p as usize, x),
                rounded_decimal(ra, $f, p),
                "display .{} {:?}",
                p,
                x
            );
        }
    }};
}
