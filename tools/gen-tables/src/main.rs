//! Table and constant generator for fulcrum.
//!
//! Every constant and table entry is computed with exact integer arithmetic as an interval
//! `[lo, hi] / 2^P` that provably contains the true value. A constant is
//! emitted for a type only if both ends of the interval round to the same raw
//! value, so the emitted value is the correctly rounded one. No floating point
//! is involved anywhere.
//!
//! Usage (from the repository root):
//!
//! ```text
//! cargo run --manifest-path tools/gen-tables/Cargo.toml            # writes src/tables/consts.rs, trig.rs and exp.rs
//! cargo run --manifest-path tools/gen-tables/Cargo.toml -- --check # fails if a file is stale
//! ```

use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Signed, Zero};
use std::fmt::Write as _;
use std::path::PathBuf;

const P: u32 = 384;

#[derive(Clone, Debug)]
struct Interval {
    lo: BigInt,
    hi: BigInt,
}

/// A decimal literal with `_` between groups of three digits from the right,
/// as `clippy::unreadable_literal` asks of numbers of five digits and more.
fn lit(v: &BigInt) -> String {
    let digits = v.abs().to_string();
    if digits.len() < 5 {
        return v.to_string();
    }
    let mut out = String::new();
    if v.is_negative() {
        out.push('-');
    }
    for (i, d) in digits.chars().enumerate() {
        if i > 0 && (digits.len() - i) % 3 == 0 {
            out.push('_');
        }
        out.push(d);
    }
    out
}

fn one() -> BigInt {
    BigInt::one() << P
}

impl Interval {
    fn exact(v: BigInt) -> Self {
        Self {
            lo: v.clone(),
            hi: v,
        }
    }

    fn widen(v: BigInt, err: u64) -> Self {
        Self {
            lo: &v - err,
            hi: &v + err,
        }
    }

    fn add(&self, o: &Self) -> Self {
        Self {
            lo: &self.lo + &o.lo,
            hi: &self.hi + &o.hi,
        }
    }

    fn sub(&self, o: &Self) -> Self {
        Self {
            lo: &self.lo - &o.hi,
            hi: &self.hi - &o.lo,
        }
    }

    fn mul_int(&self, k: u64) -> Self {
        Self {
            lo: &self.lo * k,
            hi: &self.hi * k,
        }
    }

    fn div_int(&self, k: u64) -> Self {
        let k = BigInt::from(k);
        Self {
            lo: self.lo.div_floor(&k),
            hi: div_ceil(&self.hi, &k),
        }
    }

    fn div(&self, o: &Self) -> Self {
        assert!(o.lo.is_positive() && self.lo.is_positive());
        Self {
            lo: (&self.lo << P).div_floor(&o.hi),
            hi: div_ceil(&(&self.hi << P), &o.lo),
        }
    }

    fn recip(&self) -> Self {
        Self::exact(one()).div(self)
    }

    fn round_to(&self, frac_bits: u32) -> BigInt {
        let a = round_raw(&self.lo, frac_bits);
        let b = round_raw(&self.hi, frac_bits);
        assert_eq!(
            a, b,
            "precision too low to round correctly to {} bits",
            frac_bits
        );
        a
    }
}

fn div_ceil(a: &BigInt, b: &BigInt) -> BigInt {
    -((-a).div_floor(b))
}

fn round_raw(v: &BigInt, frac_bits: u32) -> BigInt {
    let s = P - frac_bits;
    (v + (BigInt::one() << (s - 1))) >> s
}

fn atan_inv(x: u64) -> Interval {
    let x = BigInt::from(x);
    let x2 = &x * &x;
    let mut power = one().div_floor(&x);
    let mut sum = BigInt::zero();
    let mut k = 0u64;
    let mut terms = 0u64;
    while !power.is_zero() {
        let term = power.div_floor(&BigInt::from(2 * k + 1));
        if k % 2 == 0 {
            sum += term;
        } else {
            sum -= term;
        }
        power = power.div_floor(&x2);
        k += 1;
        terms += 1;
    }
    Interval::widen(sum, 2 * terms + 2)
}

fn atanh_inv(x: u64) -> Interval {
    let x = BigInt::from(x);
    let x2 = &x * &x;
    let mut power = one().div_floor(&x);
    let mut sum = BigInt::zero();
    let mut k = 0u64;
    let mut terms = 0u64;
    while !power.is_zero() {
        sum += power.div_floor(&BigInt::from(2 * k + 1));
        power = power.div_floor(&x2);
        k += 1;
        terms += 1;
    }
    Interval {
        lo: sum.clone(),
        hi: sum + 2 * terms + 2,
    }
}

fn pi() -> Interval {
    atan_inv(5).mul_int(16).sub(&atan_inv(239).mul_int(4))
}

fn e() -> Interval {
    let mut term = one();
    let mut sum = BigInt::zero();
    let mut k = 1u64;
    let mut terms = 0u64;
    while !term.is_zero() {
        sum += &term;
        term = term.div_floor(&BigInt::from(k));
        k += 1;
        terms += 1;
    }
    Interval {
        lo: sum.clone(),
        hi: sum + 2 * terms + 2,
    }
}

fn ln2() -> Interval {
    atanh_inv(3).mul_int(2)
}

fn ln10() -> Interval {
    ln2().mul_int(3).add(&atanh_inv(9).mul_int(2))
}

fn sqrt_int(n: u64) -> Interval {
    let s = (BigInt::from(n) << (2 * P)).sqrt();
    Interval {
        lo: s.clone(),
        hi: s + 1,
    }
}

struct Constant {
    name: &'static str,
    doc: &'static str,
    value: Interval,
}

fn constants() -> Vec<Constant> {
    let pi = pi();
    let ln2 = ln2();
    let ln10 = ln10();
    let sqrt2 = sqrt_int(2);
    let sqrt3 = sqrt_int(3);
    let c = |name, doc, value| Constant { name, doc, value };
    vec![
        c("PI", "π", pi.clone()),
        c("TAU", "τ = 2π", pi.mul_int(2)),
        c("FRAC_PI_2", "π/2", pi.div_int(2)),
        c("FRAC_PI_3", "π/3", pi.div_int(3)),
        c("FRAC_PI_4", "π/4", pi.div_int(4)),
        c("FRAC_PI_6", "π/6", pi.div_int(6)),
        c("FRAC_PI_8", "π/8", pi.div_int(8)),
        c("FRAC_1_PI", "1/π", pi.recip()),
        c("FRAC_2_PI", "2/π", pi.recip().mul_int(2)),
        c(
            "DEG_TO_RAD",
            "π/180: one degree in radians",
            pi.div_int(180),
        ),
        c(
            "RAD_TO_DEG",
            "180/π: one radian in degrees",
            pi.recip().mul_int(180),
        ),
        c("SQRT_2", "√2", sqrt2.clone()),
        c("FRAC_1_SQRT_2", "1/√2", sqrt2.div_int(2)),
        c("SQRT_3", "√3", sqrt3.clone()),
        c("FRAC_1_SQRT_3", "1/√3", sqrt3.div_int(3)),
        c("E", "Euler's number e", e()),
        c("LN_2", "ln 2", ln2.clone()),
        c("LN_10", "ln 10", ln10.clone()),
        c("LOG2_E", "log₂ e", ln2.recip()),
        c("LOG2_10", "log₂ 10", ln10.div(&ln2)),
        c("LOG10_2", "log₁₀ 2", ln2.div(&ln10)),
        c("LOG10_E", "log₁₀ e", ln10.recip()),
        c(
            "GOLDEN_RATIO",
            "golden ratio φ = (1 + √5)/2",
            Interval::exact(one()).add(&sqrt_int(5)).div_int(2),
        ),
    ]
}

struct Type {
    name: &'static str,
    bits: u32,
    frac: u32,
}

const TYPES: [Type; 4] = [
    Type {
        name: "FixedFloat8",
        bits: 8,
        frac: 4,
    },
    Type {
        name: "FixedFloat16",
        bits: 16,
        frac: 8,
    },
    Type {
        name: "FixedFloat32",
        bits: 32,
        frac: 16,
    },
    Type {
        name: "FixedFloat64",
        bits: 64,
        frac: 32,
    },
];

fn render() -> String {
    let consts = constants();
    let mut out = String::new();
    out.push_str("//! Mathematical constants, correctly rounded to each type.\n");
    out.push_str("//!\n");
    out.push_str("//! Generated by `tools/gen-tables`. Do not edit by hand: CI regenerates\n");
    out.push_str("//! this file and fails on any diff. A constant is absent from a type when\n");
    out.push_str("//! it is outside its range or rounds to zero.\n\n");
    for t in &TYPES {
        let max = (BigInt::one() << (t.bits - 1)) - 1;
        writeln!(out, "define_consts! {{").unwrap();
        writeln!(out, "    {} {{", t.name).unwrap();
        for c in &consts {
            let raw = c.value.round_to(t.frac);
            if raw > max || raw.is_zero() {
                continue;
            }
            writeln!(out, "        {} = {}, \"{}\";", c.name, lit(&raw), c.doc).unwrap();
        }
        writeln!(out, "    }}").unwrap();
        writeln!(out, "}}\n").unwrap();
    }
    out.truncate(out.trim_end().len());
    out.push('\n');
    out
}

/// Fractional bits of the trigonometric table and of the internal values of
/// `src/trig.rs`.
const TRIG_FRAC: u32 = 62;

/// Bits of `2/π` for the range reduction in radians.
const TRIG_REDUCTION_BITS: u32 = 192;

/// Points of the quarter-circle table: `sin(k/2^TRIG_STEPS · π/2)` for
/// `k = 0 ..= 2^TRIG_STEPS`.
const TRIG_STEPS: u32 = 8;

/// `sin x` for `x ∈ [0, π/2]`: the Taylor series at both ends, widened by the
/// truncation of every term and the tail. `sin` grows on the interval.
fn sin(x: &Interval) -> Interval {
    let series = |x: &BigInt| {
        let x2 = (x * x) >> P;
        let mut term = x.clone();
        let mut sum = x.clone();
        let mut n = 1u64;
        let mut terms = 1u64;
        while !term.is_zero() {
            term = ((&term * &x2) >> P).div_floor(&BigInt::from((n + 1) * (n + 2)));
            n += 2;
            terms += 1;
            if n % 4 == 3 {
                sum -= &term;
            } else {
                sum += &term;
            }
        }
        (sum, 2 * terms + 2)
    };
    let (lo, lo_err) = series(&x.lo);
    let (hi, hi_err) = series(&x.hi);
    Interval {
        lo: lo - lo_err,
        hi: hi + hi_err,
    }
}

/// `atan(p/q)` for `0 ≤ p ≤ q`: the Taylor series of `atan` at `p/q ≤ ½`,
/// and `π/4 - atan((q - p)/(q + p))` above, where the argument is at most
/// `⅓`. Every power is floored, so its error stays below `4/3` (the
/// ratio `p²/q²` is at most `¼`), each term adds one more, and the tail of the
/// alternating series is below the first power that floors to zero.
fn atan_ratio(p: u64, q: u64, pi: &Interval) -> Interval {
    if 2 * p > q {
        return pi.div_int(4).sub(&atan_ratio(q - p, q + p, pi));
    }
    let (p, q) = (BigInt::from(p), BigInt::from(q));
    let (p2, q2) = (&p * &p, &q * &q);
    let mut power = (one() * &p).div_floor(&q);
    let mut sum = BigInt::zero();
    let mut k = 0u64;
    while !power.is_zero() {
        let term = power.div_floor(&BigInt::from(2 * k + 1));
        if k % 2 == 0 {
            sum += term;
        } else {
            sum -= term;
        }
        power = (power * &p2).div_floor(&q2);
        k += 1;
    }
    Interval::widen(sum, 3 * k + 3)
}

fn render_trig() -> String {
    let pi = pi();
    let steps = 1u64 << TRIG_STEPS;
    let mut out = String::new();
    out.push_str("//! Tables of the trigonometric functions of `src/trig.rs`.\n");
    out.push_str("//!\n");
    out.push_str("//! Generated by `tools/gen-tables`. Do not edit by hand: CI regenerates\n");
    out.push_str("//! this file and fails on any diff.\n\n");
    writeln!(out, "/// Fractional bits of every value below.").unwrap();
    writeln!(out, "pub(crate) const FRAC: u32 = {};\n", TRIG_FRAC).unwrap();
    writeln!(
        out,
        "/// `log₂` of the number of steps of [`SIN_QUARTER`] per quarter circle\n/// and of [`ATAN`] on `[0, 1]`."
    )
    .unwrap();
    writeln!(out, "pub(crate) const STEPS: u32 = {};\n", TRIG_STEPS).unwrap();
    writeln!(out, "/// π, correctly rounded.").unwrap();
    writeln!(
        out,
        "pub(crate) const PI: u64 = {};\n",
        lit(&pi.round_to(TRIG_FRAC))
    )
    .unwrap();
    writeln!(
        out,
        "/// π · 2^126, correctly rounded: `to_radians` of the angle types."
    )
    .unwrap();
    writeln!(
        out,
        "pub(crate) const PI_126: u128 = {};\n",
        lit(&pi.round_to(126))
    )
    .unwrap();
    writeln!(out, "/// π/2, correctly rounded.").unwrap();
    writeln!(
        out,
        "pub(crate) const FRAC_PI_2: u64 = {};\n",
        lit(&pi.div_int(2).round_to(TRIG_FRAC))
    )
    .unwrap();
    let two_over_pi = pi.recip().mul_int(2).round_to(TRIG_REDUCTION_BITS);
    let mask = (BigInt::one() << 64u32) - 1;
    let words: Vec<String> = (0..3u32)
        .rev()
        .map(|i| lit(&((&two_over_pi >> (64 * i)) & &mask)))
        .collect();
    writeln!(
        out,
        "/// `2/π · 2^{}`, correctly rounded, most significant word first: the\n/// range reduction of the functions in radians.",
        TRIG_REDUCTION_BITS
    )
    .unwrap();
    out.push_str("pub(crate) const FRAC_2_PI: [u64; 3] = [\n");
    for w in &words {
        writeln!(out, "    {},", w).unwrap();
    }
    out.push_str("];\n\n");
    writeln!(
        out,
        "/// `sin(k/2^STEPS · π/2)` for `k = 0 ..= 2^STEPS`, correctly rounded."
    )
    .unwrap();
    writeln!(
        out,
        "pub(crate) const SIN_QUARTER: [u64; {}] = [",
        steps + 1
    )
    .unwrap();
    for k in 0..=steps {
        let x = pi.mul_int(k).div_int(2 * steps);
        writeln!(out, "    {},", lit(&sin(&x).round_to(TRIG_FRAC))).unwrap();
    }
    out.push_str("];\n\n");
    writeln!(
        out,
        "/// `atan(k/2^STEPS)` for `k = 0 ..= 2^STEPS`, correctly rounded."
    )
    .unwrap();
    writeln!(out, "pub(crate) const ATAN: [u64; {}] = [", steps + 1).unwrap();
    for k in 0..=steps {
        writeln!(
            out,
            "    {},",
            lit(&atan_ratio(k, steps, &pi).round_to(TRIG_FRAC))
        )
        .unwrap();
    }
    out.push_str("];\n");
    out
}

/// Fractional bits of [`EXP2`] in `src/tables/exp.rs`: the mantissa of
/// `exp2` keeps 72 bits after its series, more than the 63 significant bits
/// of the largest `FixedFloat64` result.
const EXP2_FRAC: u32 = 126;

/// Fractional bits of `ln 2` for the series argument of `exp2`: the product
/// with a remainder of at most 24 bits stays below `2^128`.
const EXP2_LN_2_FRAC: u32 = 104;

/// Fractional bits of the logarithm table and of the internal values of
/// `log2`.
const LOG_FRAC: u32 = 62;

/// `log₂` of the number of points of both tables: `2^(k/2^EXP_STEPS)` for
/// `k/2^EXP_STEPS ∈ [0, 1)`, `log₂ c` for `c = 1 + k/2^EXP_STEPS ∈ [1, 2)`.
const EXP_STEPS: u32 = 8;

/// `2^(k/2^EXP_STEPS) = e^(k · ln 2 / 2^EXP_STEPS)`: the Taylor series at
/// both ends of the interval of the argument (below 1, every term positive,
/// `e^x` grows), each term floored from the one before, so it is low by less
/// than `2`; the tail after the term that floors to zero is below `2`.
fn exp2_step(k: u64, ln2: &Interval) -> Interval {
    let x = ln2.mul_int(k).div_int(1 << EXP_STEPS);
    let series = |x: &BigInt| {
        let mut term = one();
        let mut sum = BigInt::zero();
        let mut n = 1u64;
        while !term.is_zero() {
            sum += &term;
            term = ((term * x) >> P).div_floor(&BigInt::from(n));
            n += 1;
        }
        (sum, 2 * n + 2)
    };
    let (lo, _) = series(&x.lo);
    let (hi, err) = series(&x.hi);
    Interval { lo, hi: hi + err }
}

/// `ln(1 + p/q) = 2·atanh(p/(2q + p))` for `0 < p ≤ q`: the argument is at
/// most `⅓`, so the ratio of the series is at most `1/9`. Every power is
/// floored, its error stays below `9/8`; each term adds one more, and the
/// tail after the power that floors to zero is below `1.3`.
fn ln_1p_ratio(p: u64, q: u64) -> Interval {
    let (a, b) = (BigInt::from(p), BigInt::from(2 * q + p));
    let (a2, b2) = (&a * &a, &b * &b);
    let mut power = (one() * &a).div_floor(&b);
    let mut sum = BigInt::zero();
    let mut k = 0u64;
    while !power.is_zero() {
        sum += power.div_floor(&BigInt::from(2 * k + 1));
        power = (power * &a2).div_floor(&b2);
        k += 1;
    }
    Interval {
        lo: (&sum - 3 * k - 3) * 2,
        hi: (sum + 3 * k + 3) * 2,
    }
}

fn render_exp() -> String {
    let ln2 = ln2();
    let steps = 1u64 << EXP_STEPS;
    let mut out = String::new();
    out.push_str("//! Tables of the binary exponential and logarithm of `src/exp.rs`.\n");
    out.push_str("//!\n");
    out.push_str("//! Generated by `tools/gen-tables`. Do not edit by hand: CI regenerates\n");
    out.push_str("//! this file and fails on any diff.\n\n");
    writeln!(
        out,
        "/// Fractional bits of [`LOG2`], [`TWO_LOG2_E`] and the internal values of\n/// `log2`."
    )
    .unwrap();
    writeln!(out, "pub(crate) const FRAC: u32 = {};\n", LOG_FRAC).unwrap();
    writeln!(out, "/// Fractional bits of [`EXP2`].").unwrap();
    writeln!(out, "pub(crate) const EXP2_FRAC: u32 = {};\n", EXP2_FRAC).unwrap();
    writeln!(
        out,
        "/// `log₂` of the number of points of [`EXP2`] (on `[0, 1)`) and [`LOG2`]\n/// (on `[1, 2)`)."
    )
    .unwrap();
    writeln!(out, "pub(crate) const STEPS: u32 = {};\n", EXP_STEPS).unwrap();
    writeln!(
        out,
        "/// `ln 2 · 2^{}`, correctly rounded: the series argument of `exp2`.",
        EXP2_LN_2_FRAC
    )
    .unwrap();
    writeln!(
        out,
        "pub(crate) const LN_2: u128 = {};\n",
        lit(&ln2.round_to(EXP2_LN_2_FRAC))
    )
    .unwrap();
    writeln!(out, "/// Fractional bits of [`LN_2`].").unwrap();
    writeln!(
        out,
        "pub(crate) const LN_2_FRAC: u32 = {};\n",
        EXP2_LN_2_FRAC
    )
    .unwrap();
    writeln!(
        out,
        "/// `2 · log₂ e = 2 / ln 2`, correctly rounded: the factor of the\n/// `atanh` series of `log2`."
    )
    .unwrap();
    writeln!(
        out,
        "pub(crate) const TWO_LOG2_E: u64 = {};\n",
        lit(&ln2.recip().mul_int(2).round_to(LOG_FRAC))
    )
    .unwrap();
    writeln!(
        out,
        "/// `2^(k/2^STEPS)` for `k = 0 .. 2^STEPS`, correctly rounded."
    )
    .unwrap();
    writeln!(out, "pub(crate) const EXP2: [u128; {}] = [", steps).unwrap();
    for k in 0..steps {
        writeln!(out, "    {},", lit(&exp2_step(k, &ln2).round_to(EXP2_FRAC))).unwrap();
    }
    out.push_str("];\n\n");
    writeln!(
        out,
        "/// `log₂(1 + k/2^STEPS)` for `k = 0 .. 2^STEPS`, correctly rounded."
    )
    .unwrap();
    writeln!(out, "pub(crate) const LOG2: [u64; {}] = [", steps).unwrap();
    for k in 0..steps {
        let v = if k == 0 {
            Interval::exact(BigInt::zero())
        } else {
            ln_1p_ratio(k, steps).div(&ln2)
        };
        writeln!(out, "    {},", lit(&v.round_to(LOG_FRAC))).unwrap();
    }
    out.push_str("];\n");
    out
}

fn main() {
    let dir: PathBuf = [env!("CARGO_MANIFEST_DIR"), "..", "..", "src", "tables"]
        .iter()
        .collect();
    let check = std::env::args().any(|a| a == "--check");
    let mut stale = false;
    for (name, text) in [
        ("consts.rs", render()),
        ("trig.rs", render_trig()),
        ("exp.rs", render_exp()),
    ] {
        let path = dir.join(name);
        if check {
            let current = std::fs::read_to_string(&path).unwrap_or_default();
            if current != text {
                eprintln!("{} is stale: run tools/gen-tables", path.display());
                stale = true;
            } else {
                eprintln!("{} is up to date", path.display());
            }
        } else {
            std::fs::write(&path, text).expect("write table");
            eprintln!("wrote {}", path.display());
        }
    }
    if stale {
        std::process::exit(1);
    }
}
