//! Shared test helpers without external crates: a PCG32 generator,
//! edge-biased value generators and `spec`, the integer reference of
//! `reference.rs` over `i128`.

#![allow(dead_code)]

#[macro_use]
mod widths;

#[macro_use]
mod reference;

reference!(spec, i128);

pub mod exp;
pub mod trig;

/// Runs `body` `count` times on operands of `bits` bits with `f` fractional
/// bits from `Pcg32::new(seed, bits)`, each drawn by `edge_bits` and cast to
/// its type.
#[allow(unused_macros)]
macro_rules! for_random_edges {
    ($seed:expr, $count:expr, $bits:tt, $f:tt, |$($v:ident: $V:ty),+| $body:expr) => {{
        let mut rng = Pcg32::new($seed, $bits);
        for _ in 0..$count {
            $(let $v = rng.edge_bits($bits, $f) as $V;)+
            let _ = $body;
        }
    }};
}

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
        (u64::from(self.next_u32()) << 32) | u64::from(self.next_u32())
    }

    pub fn below(&mut self, n: u32) -> u32 {
        ((u64::from(self.next_u32()) * u64::from(n)) >> 32) as u32
    }

    /// Raw value of `bits` bits, biased toward edge cases: 0, ±1 ulp, ±1,
    /// MIN, MAX, MIN + 1, powers of two, small values and sign changes.
    pub fn edge_bits(&mut self, bits: u32, frac_bits: u32) -> i64 {
        let min = i64::MIN >> (64 - bits);
        let max = i64::MAX >> (64 - bits);
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
                let small = i64::from(self.next_u32()) & (one * 4 - 1);
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
            self.0 ^= u64::from(b);
            self.0 = self.0.wrapping_mul(0x0100_0000_01b3);
        }
    }

    pub fn finish(&self) -> u64 {
        self.0
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
        format!("{sign}{int}")
    } else {
        format!("{sign}{int}.{digits}")
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
        format!("{sign}{q}")
    } else {
        format!("{}{}.{:0w$}", sign, q / p, q % p, w = precision as usize)
    }
}

#[allow(unused_macros)]
macro_rules! check_pair {
    ($T:ident, $bits:expr, $f:expr, $a:expr, $b:expr) => {{
        let (ra, rb): (i128, i128) = (i128::from($a), i128::from($b));
        let x = $T::from_bits($a);
        let y = $T::from_bits($b);
        let ctx = || format!("{} {} ({:?}, {:?})", stringify!($T), "", x, y);

        let sum = ra + rb;
        assert_eq!(
            i128::from(x.saturating_add(y).to_bits()),
            crate::common::spec::saturate(sum, $bits),
            "add {}",
            ctx()
        );
        assert_eq!(
            i128::from(x.wrapping_add(y).to_bits()),
            crate::common::spec::wrap(sum, $bits),
            "wrapping_add {}",
            ctx()
        );
        assert_eq!(
            x.checked_add(y).is_some(),
            crate::common::spec::fits(sum, $bits),
            "checked_add {}",
            ctx()
        );

        let diff = ra - rb;
        assert_eq!(
            i128::from((x - y).to_bits()),
            crate::common::spec::saturate(diff, $bits),
            "sub {}",
            ctx()
        );
        assert_eq!(
            x.overflowing_sub(y),
            (
                $T::from_bits(
                    crate::common::spec::wrap(diff, $bits) as <$T as fulcrum::FixedFloat>::Bits
                ),
                !crate::common::spec::fits(diff, $bits)
            ),
            "overflowing_sub {}",
            ctx()
        );

        let prod = crate::common::spec::mul(ra, rb, $f);
        assert_eq!(
            i128::from((x * y).to_bits()),
            crate::common::spec::saturate(prod, $bits),
            "mul {}",
            ctx()
        );
        assert_eq!(
            i128::from(x.wrapping_mul(y).to_bits()),
            crate::common::spec::wrap(prod, $bits),
            "wrapping_mul {}",
            ctx()
        );
        assert_eq!(
            x.overflowing_mul(y).1,
            !crate::common::spec::fits(prod, $bits),
            "overflowing_mul {}",
            ctx()
        );
        assert_eq!(
            x.checked_mul(y).map(|v| i128::from(v.to_bits())),
            Some(prod).filter(|p| crate::common::spec::fits(*p, $bits)),
            "checked_mul {}",
            ctx()
        );

        if rb == 0 {
            assert_eq!(
                i128::from((x / y).to_bits()),
                crate::common::spec::div_by_zero(ra, $bits),
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
            let quot = crate::common::spec::div(ra, rb, $f);
            assert_eq!(
                i128::from((x / y).to_bits()),
                crate::common::spec::saturate(quot, $bits),
                "div {}",
                ctx()
            );
            assert_eq!(
                i128::from(x.wrapping_div(y).to_bits()),
                crate::common::spec::wrap(quot, $bits),
                "wrapping_div {}",
                ctx()
            );
            assert_eq!(
                x.checked_div(y).map(|v| i128::from(v.to_bits())),
                Some(quot).filter(|q| crate::common::spec::fits(*q, $bits)),
                "checked_div {}",
                ctx()
            );
            let rem = ra - rb * (ra / rb);
            assert_eq!(i128::from((x % y).to_bits()), rem, "rem {}", ctx());
            let int_quot = crate::common::spec::round_div(ra, rb);
            assert_eq!(
                i128::from(x.div_int($b).to_bits()),
                crate::common::spec::saturate(int_quot, $bits),
                "div_int {}",
                ctx()
            );
        }

        let mul_int = ra * rb;
        assert_eq!(
            i128::from(x.mul_int($b).to_bits()),
            crate::common::spec::saturate(mul_int, $bits),
            "mul_int {}",
            ctx()
        );

        let mid = crate::common::spec::round_div(ra + rb, 2);
        assert_eq!(
            i128::from(x.midpoint(y).to_bits()),
            mid,
            "midpoint {}",
            ctx()
        );
        assert_eq!(i128::from(x.min(y).to_bits()), ra.min(rb), "min {}", ctx());
        assert_eq!(i128::from(x.max(y).to_bits()), ra.max(rb), "max {}", ctx());
        assert_eq!(
            i128::from(x.abs_diff(y).to_bits()),
            crate::common::spec::saturate((ra - rb).abs(), $bits),
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
        let ra = i128::from($a);
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

        assert_eq!(i128::from(x.floor().to_bits()), floor, "floor {:?}", x);
        assert_eq!(
            i128::from(x.ceil().to_bits()),
            crate::common::spec::saturate(ceil, $bits),
            "ceil {:?}",
            x
        );
        assert_eq!(
            x.checked_ceil().is_some(),
            crate::common::spec::fits(ceil, $bits),
            "checked_ceil {:?}",
            x
        );
        assert_eq!(i128::from(x.trunc().to_bits()), trunc, "trunc {:?}", x);
        assert_eq!(i128::from(x.fract().to_bits()), ra - trunc, "fract {:?}", x);
        assert_eq!(
            i128::from(x.round().to_bits()),
            crate::common::spec::saturate(away, $bits),
            "round {:?}",
            x
        );
        assert_eq!(
            x.checked_round().map(|v| i128::from(v.to_bits())),
            Some(away).filter(|&v| crate::common::spec::fits(v, $bits)),
            "checked_round {:?}",
            x
        );
        assert_eq!(
            i128::from(x.round_ties_even().to_bits()),
            crate::common::spec::saturate(even, $bits),
            "round_ties_even {:?}",
            x
        );
        assert_eq!(
            x.checked_round_ties_even().map(|v| i128::from(v.to_bits())),
            Some(even).filter(|&v| crate::common::spec::fits(v, $bits)),
            "checked_round_ties_even {:?}",
            x
        );
        assert_eq!(
            i128::from(x.to_int_floor()),
            floor / one,
            "to_int_floor {:?}",
            x
        );
        assert_eq!(
            i128::from(x.to_int_ceil()),
            ceil / one,
            "to_int_ceil {:?}",
            x
        );
        assert_eq!(
            i128::from(x.to_int_trunc()),
            trunc / one,
            "to_int_trunc {:?}",
            x
        );
        assert_eq!(
            i128::from(x.to_int_round()),
            away / one,
            "to_int_round {:?}",
            x
        );
        assert_eq!(
            i128::from(x.to_int_round_ties_even()),
            even / one,
            "to_int_round_ties_even {:?}",
            x
        );

        assert_eq!(
            i128::from((-x).to_bits()),
            crate::common::spec::saturate(-ra, $bits),
            "neg {:?}",
            x
        );
        assert_eq!(
            i128::from(x.wrapping_neg().to_bits()),
            crate::common::spec::wrap(-ra, $bits),
            "wrapping_neg {:?}",
            x
        );
        assert_eq!(
            x.checked_neg().is_some(),
            crate::common::spec::fits(-ra, $bits),
            "checked_neg {:?}",
            x
        );
        assert_eq!(
            x.overflowing_neg(),
            (
                $T::from_bits(
                    crate::common::spec::wrap(-ra, $bits) as <$T as fulcrum::FixedFloat>::Bits
                ),
                !crate::common::spec::fits(-ra, $bits)
            ),
            "overflowing_neg {:?}",
            x
        );
        assert_eq!(
            i128::from(x.abs().to_bits()),
            crate::common::spec::saturate(ra.abs(), $bits),
            "abs {:?}",
            x
        );
        assert_eq!(
            i128::from(x.saturating_abs().to_bits()),
            crate::common::spec::saturate(ra.abs(), $bits),
            "saturating_abs {:?}",
            x
        );
        assert_eq!(
            x.checked_abs().map(|v| i128::from(v.to_bits())),
            Some(ra.abs()).filter(|&v| crate::common::spec::fits(v, $bits)),
            "checked_abs {:?}",
            x
        );
        assert_eq!(
            i128::from(x.wrapping_abs().to_bits()),
            crate::common::spec::wrap(ra.abs(), $bits),
            "wrapping_abs {:?}",
            x
        );
        assert_eq!(
            x.overflowing_abs(),
            (
                $T::from_bits(
                    crate::common::spec::wrap(ra.abs(), $bits) as <$T as fulcrum::FixedFloat>::Bits
                ),
                !crate::common::spec::fits(ra.abs(), $bits)
            ),
            "overflowing_abs {:?}",
            x
        );
        assert_eq!(
            i128::from(x.signum().to_bits()),
            ra.signum() * one,
            "signum {:?}",
            x
        );
        let recip = if ra == 0 {
            crate::common::spec::div_by_zero(one, $bits)
        } else {
            crate::common::spec::saturate(crate::common::spec::round_div(one << $f, ra), $bits)
        };
        assert_eq!(i128::from(x.recip().to_bits()), recip, "recip {:?}", x);

        assert_eq!(
            i128::from(x.int_part()),
            ra.div_euclid(one),
            "int_part {:?}",
            x
        );
        assert_eq!(
            i128::from(x.frac_part()),
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

/// Unsigned integer from the environment variable `name`, if it is set.
///
/// Panics when the variable is set but is not a decimal `u64`: silently
/// falling back to a default would make a mistyped replay seed look like a
/// passing replay.
pub fn env_u64(name: &str) -> Option<u64> {
    match std::env::var(name) {
        Ok(v) => Some(
            v.parse()
                .unwrap_or_else(|_| panic!("{name}={v:?} is not a decimal unsigned integer")),
        ),
        Err(std::env::VarError::NotPresent) => None,
        Err(e) => panic!("{name}: {e}"),
    }
}

/// Seed from the environment variable `name`, or from the clock when it is
/// not set, so that a run can always be replayed from the printed value.
pub fn seed_from_env(name: &str) -> u64 {
    env_u64(name).unwrap_or_else(|| {
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map_or(1, |d| d.as_nanos() as u64)
    })
}

/// Items each stream runs between checks of the deadline and the stop flag.
pub const BATCH: u64 = 4096;

/// What [`run_streams`] did: items run by all streams together and the sum of
/// the values the body returned.
pub struct Totals {
    pub seed: u64,
    pub items: u64,
    pub tally: u64,
}

struct StreamGuard {
    stop: std::sync::Arc<std::sync::atomic::AtomicBool>,
    name: &'static str,
    prefix: &'static str,
    seed: u64,
    stream: u64,
    batch: u64,
}

impl Drop for StreamGuard {
    fn drop(&mut self) {
        if std::thread::panicking() {
            self.stop.store(true, std::sync::atomic::Ordering::Relaxed);
            eprintln!(
                "{}: stream {} failed in batch {}; replay exactly with {p}_SEED={} {p}_STREAM={} {p}_BATCHES={}",
                self.name,
                self.stream,
                self.batch,
                self.seed,
                self.stream,
                self.batch + 1,
                p = self.prefix,
            );
        }
    }
}

/// Runs `body` on independent [`Pcg32`] streams, one thread each, in batches
/// of [`BATCH`] items. Settings come from the environment, `P` = `prefix`:
///
/// * `P_SEED`: seed (default: the clock, printed);
/// * `P_THREADS`: number of streams `0..n` (default: available cores);
/// * `P_STREAM`: run only this stream, on one thread;
/// * `P_BATCHES`: run exactly this many batches per stream, which makes the
///   run independent of machine speed;
/// * `P_SECS`: otherwise run until this deadline (default `default_secs`).
///
/// A failing stream prints the exact replay settings and stops the others.
pub fn run_streams<F>(
    name: &'static str,
    prefix: &'static str,
    default_secs: u64,
    body: F,
) -> Totals
where
    F: Fn(&mut Pcg32) -> u64 + Send + Sync + 'static,
{
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::Arc;
    use std::time::{Duration, Instant};

    let var = |s: &str| env_u64(&format!("{prefix}_{s}"));
    let seed = seed_from_env(&format!("{prefix}_SEED"));
    let streams: Vec<u64> = if let Some(k) = var("STREAM") {
        vec![k]
    } else {
        let n = var("THREADS")
            .unwrap_or_else(|| std::thread::available_parallelism().map_or(4, |n| n.get() as u64));
        (0..n).collect()
    };
    let batches = var("BATCHES");
    let secs = var("SECS").unwrap_or(default_secs);
    let limit = match batches {
        Some(b) => format!("{b} batches per stream"),
        None => format!("{secs} s"),
    };
    eprintln!(
        "{name}: seed {seed}, streams {streams:?}, {limit}; replay with {prefix}_SEED={seed}"
    );

    let deadline = Instant::now() + Duration::from_secs(secs);
    let stop = Arc::new(AtomicBool::new(false));
    let body = Arc::new(body);
    let handles: Vec<_> = streams
        .into_iter()
        .map(|stream| {
            let stop = Arc::clone(&stop);
            let body = Arc::clone(&body);
            std::thread::spawn(move || {
                let mut guard = StreamGuard {
                    stop: Arc::clone(&stop),
                    name,
                    prefix,
                    seed,
                    stream,
                    batch: 0,
                };
                let mut rng = Pcg32::new(seed, stream);
                let mut tally = 0u64;
                loop {
                    let more = match batches {
                        Some(b) => guard.batch < b,
                        None => Instant::now() < deadline,
                    };
                    if !more || stop.load(Ordering::Relaxed) {
                        break;
                    }
                    for _ in 0..BATCH {
                        tally += body(&mut rng);
                    }
                    guard.batch += 1;
                }
                (guard.batch * BATCH, tally)
            })
        })
        .collect();

    let mut totals = Totals {
        seed,
        items: 0,
        tally: 0,
    };
    let mut failed = false;
    for h in handles {
        match h.join() {
            Ok((items, tally)) => {
                totals.items += items;
                totals.tally += tally;
            }
            Err(_) => failed = true,
        }
    }
    assert!(!failed, "{name} failed, see the replay line above");
    totals
}

/// Calls `f` on every value of `lo..hi` on every available thread and
/// returns the sum of its results. The threads take blocks of 2^12 values
/// from a shared counter, so a thread that drew cheap values (the negative
/// half of a logarithm or a root) takes more blocks instead of idling.
pub fn parallel_sum<F: Fn(i64) -> u64 + Send + Sync + 'static>(lo: i64, hi: i64, f: F) -> u64 {
    const BLOCK: i64 = 1 << 12;
    let threads = std::thread::available_parallelism().map_or(4, std::num::NonZeroUsize::get);
    let next = std::sync::Arc::new(std::sync::atomic::AtomicI64::new(lo));
    let f = std::sync::Arc::new(f);
    let handles: Vec<_> = (0..threads)
        .map(|_| {
            let (next, f) = (std::sync::Arc::clone(&next), std::sync::Arc::clone(&f));
            std::thread::spawn(move || {
                let mut sum = 0;
                loop {
                    let start = next.fetch_add(BLOCK, std::sync::atomic::Ordering::Relaxed);
                    if start >= hi {
                        return sum;
                    }
                    for v in start..(start + BLOCK).min(hi) {
                        sum += f(v);
                    }
                }
            })
        })
        .collect();
    handles.into_iter().map(|h| h.join().unwrap()).sum()
}

/// Calls `f` on every value of `lo..hi` on every available thread, as
/// [`parallel_sum`].
pub fn parallel<F: Fn(i64) + Send + Sync + 'static>(lo: i64, hi: i64, f: F) {
    parallel_sum(lo, hi, move |v| {
        f(v);
        0
    });
}

/// Runs `check` on every value of `FixedFloat32` on every available thread
/// and returns the number of values for which it returned `true`.
pub fn every_fixed32(check: fn(i32) -> bool) -> u64 {
    parallel_sum(i64::from(i32::MIN), i64::from(i32::MAX) + 1, move |a| {
        u64::from(check(a as i32))
    })
}

/// `round(Σ a·b / 2^f)` for raw values of at most 64 bits and at most 2^62
/// terms, without overflowing `i128`: every product `p` is split into
/// `p = h·2^64 + l` with `0 ≤ l < 2^64`, and the two halves are summed
/// separately. `h·2^(64 - f)` is an integer, so only the low sum is rounded.
pub fn exact_dot<T: Copy>(a: &[T], b: &[T], raw: impl Fn(T) -> i128, f: u32) -> i128 {
    let (mut hi, mut lo) = (0i128, 0i128);
    for (&x, &y) in a.iter().zip(b) {
        let p = raw(x) * raw(y);
        hi += p >> 64;
        lo += p & ((1i128 << 64) - 1);
    }
    (hi << (64 - f)) + spec::round_div(lo, 1i128 << f)
}
