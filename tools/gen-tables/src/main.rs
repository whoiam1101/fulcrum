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
//! cargo run --manifest-path tools/gen-tables/Cargo.toml            # writes src/tables/consts.rs and trig.rs
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
            writeln!(out, "        {} = {}, \"{}\";", c.name, raw, c.doc).unwrap();
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
        "/// `log₂` of the number of steps of [`SIN_QUARTER`] per quarter circle."
    )
    .unwrap();
    writeln!(out, "pub(crate) const STEPS: u32 = {};\n", TRIG_STEPS).unwrap();
    writeln!(out, "/// π/2, correctly rounded.").unwrap();
    writeln!(
        out,
        "pub(crate) const FRAC_PI_2: u64 = {};\n",
        pi.div_int(2).round_to(TRIG_FRAC)
    )
    .unwrap();
    let two_over_pi = pi.recip().mul_int(2).round_to(TRIG_REDUCTION_BITS);
    let mask = (BigInt::one() << 64u32) - 1;
    let words: Vec<String> = (0..3u32)
        .rev()
        .map(|i| ((&two_over_pi >> (64 * i)) & &mask).to_string())
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
        writeln!(out, "    {},", sin(&x).round_to(TRIG_FRAC)).unwrap();
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
    for (name, text) in [("consts.rs", render()), ("trig.rs", render_trig())] {
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
