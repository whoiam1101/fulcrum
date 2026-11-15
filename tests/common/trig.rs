//! Reference sine and cosine in turns, written independently of the library:
//! octant symmetry to `φ ∈ [0, π/4]` and the full Taylor series of `sin φ` or
//! `cos φ` at 64 fractional bits on `u128`, without the quarter-circle table
//! and the short series of `src/trig.rs`.
//!
//! [`sin_turns`] returns `sin(2π·t) · 2^64` within [`ERROR`] of the true value,
//! where `t = raw / 2^f`; the rational oracle checks the bound
//! (`oracle/tests/trig.rs`).
//!
//! In radians, [`sin`] and [`cos`] subtract the nearest multiple `k·π/2`
//! with `π/2` at `127 - f` fractional bits (not the multiplication by `2/π`
//! of `src/trig.rs`) and take the same series of the remainder; [`tan`] is
//! the interval of their quotient.
//!
//! The inverse functions halve the argument of `atan` three times instead
//! of the table of `src/trig.rs`, and [`asin`] is `2·atan(x / (1 + √(1 - x²)))`
//! instead of `atan2(x, √(1 - x²))`.

/// Fractional bits of the reference values.
pub const SCALE: u32 = 64;

/// Bound on the error of [`sin_turns`] and [`cos_turns`], in units of `2^-64`.
pub const ERROR: i128 = 1 << 8;

/// `⌊π/4 · 2^64⌋`.
const FRAC_PI_4: u128 = 0xC90F_DAA2_2168_C234;

const ONE: u128 = 1 << 64;

/// `π/2 · 2^126`, rounded to nearest.
const FRAC_PI_2_126: u128 = 0x6487_ED51_10B4_611A_6263_3145_C06E_0E69;

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

/// `raw / 2^f = k·π/2 + r` with `|r| ≤ π/4` (up to the error of `π/2`, at
/// most `2^(2f-128)`) for `|raw|`: `k mod 4` and `|r| · 2^64` with the sign
/// of `r`.
fn reduce(raw: i128, f: u32) -> (u32, u128, bool) {
    let s = 127 - f;
    let shift = 126 - s;
    let pi_2 = (FRAC_PI_2_126 + (1 << (shift - 1))) >> shift;
    let x = raw.unsigned_abs() << (s - f);
    let k = (x + pi_2 / 2) / pi_2;
    let r = x as i128 - (k * pi_2) as i128;
    ((k % 4) as u32, r.unsigned_abs() >> (s - SCALE), r < 0)
}

/// `sin r · 2^64` and `cos r · 2^64` for the remainder of [`reduce`].
fn sin_cos_rest(phi: u128, negative: bool) -> (i128, i128) {
    let s = sin_series(phi) as i128;
    let c = cos_series(phi) as i128;
    (if negative { -s } else { s }, c)
}

/// `sin(raw / 2^f) · 2^64`, within [`ERROR`]. `2 ≤ f ≤ 32`,
/// `|raw| ≤ 2^(2f-1)`.
pub fn sin(raw: i128, f: u32) -> i128 {
    let (k, phi, negative) = reduce(raw, f);
    let (s, c) = sin_cos_rest(phi, negative);
    let v = [s, c, -s, -c][k as usize];
    if raw < 0 {
        -v
    } else {
        v
    }
}

/// `cos(raw / 2^f) · 2^64`, within [`ERROR`]. `2 ≤ f ≤ 32`,
/// `|raw| ≤ 2^(2f-1)`.
pub fn cos(raw: i128, f: u32) -> i128 {
    let (k, phi, negative) = reduce(raw, f);
    let (s, c) = sin_cos_rest(phi, negative);
    [c, -s, -c, s][k as usize]
}

/// `⌊√n⌋`, bit by bit.
fn isqrt(n: u128) -> u128 {
    let mut root = 0u128;
    let mut bit = 1u128 << 126;
    let mut n = n;
    while bit > n {
        bit >>= 2;
    }
    while bit != 0 {
        if n >= root + bit {
            n -= root + bit;
            root = (root >> 1) + bit;
        } else {
            root >>= 1;
        }
        bit >>= 2;
    }
    root
}

/// `π/2 · 2^64`, rounded to nearest.
fn frac_pi_2() -> i128 {
    ((FRAC_PI_2_126 + 2) >> 62) as i128
}

/// `atan t · 2^64` for `t = w / 2^64 ∈ [0, 1]`: three halvings
/// `t → t / (1 + √(1 + t²))` to `t ≤ tan(π/32)`, the full Taylor series,
/// times 8. No table.
fn atan_unit(w: u128) -> u128 {
    let mut t = w;
    for _ in 0..3 {
        let half = t >> 1;
        let s = isqrt((1 << 126) + half * half) << 1;
        t = (t << 63) / ((ONE + s) >> 1);
    }
    let t2 = mul(t, t);
    let mut power = t;
    let mut sum = t as i128;
    let mut k = 1u128;
    loop {
        power = mul(power, t2);
        let term = power / (2 * k + 1);
        if term == 0 {
            return (sum << 3) as u128;
        }
        sum += if k % 2 == 1 {
            -(term as i128)
        } else {
            term as i128
        };
        k += 1;
    }
}

/// `atan(n / d) · 2^64 ∈ [0, π/2]` for `n, d < 2^64`, not both `0`:
/// `π/2 - atan(d / n)` when `n > d`.
fn atan_ratio(n: u128, d: u128) -> i128 {
    if n <= d {
        atan_unit((n << 64) / d) as i128
    } else {
        frac_pi_2() - atan_unit((d << 64) / n) as i128
    }
}

/// `atan2(y, x) · 2^64` of two raw values of the same scale, in `(-π, π]`;
/// `atan2(0, 0) = 0`.
pub fn atan2(y: i128, x: i128) -> i128 {
    if y == 0 && x >= 0 {
        return 0;
    }
    let a = atan_ratio(y.unsigned_abs(), x.unsigned_abs());
    let a = if x < 0 { 2 * frac_pi_2() - a } else { a };
    if y < 0 {
        -a
    } else {
        a
    }
}

/// `atan(raw / 2^f) · 2^64`, within [`ERROR`]. `f ≤ 63`, `|raw| ≤ 2^64`.
pub fn atan(raw: i128, f: u32) -> i128 {
    atan2(raw, 1 << f)
}

/// `asin(raw / 2^f) · 2^64 = 2·atan(x / (1 + √(1 - x²)))`, within
/// [`ERROR`]. `|raw| ≤ 2^f`, `f ≤ 32`.
pub fn asin(raw: i128, f: u32) -> i128 {
    let m = raw.unsigned_abs();
    let s = isqrt(((1u128 << (2 * f)) - m * m) << (126 - 2 * f));
    let a = 2 * atan_ratio(m << (63 - f), (1 << 63) + s);
    if raw < 0 {
        -a
    } else {
        a
    }
}

/// `acos(raw / 2^f) · 2^64 = π/2 - asin(raw / 2^f)`, within [`ERROR`].
/// `|raw| ≤ 2^f`, `f ≤ 32`.
pub fn acos(raw: i128, f: u32) -> i128 {
    frac_pi_2() - asin(raw, f)
}

/// `[lo, hi] · 2^-64` containing `tan(raw / 2^f)`, or `None` when the
/// cosine is too close to `0` for its bound [`ERROR`]: the quotient of
/// [`sin`] and [`cos`] over every value within their bounds.
pub fn tan(raw: i128, f: u32) -> Option<(i128, i128)> {
    let (s, c) = (sin(raw, f), cos(raw, f));
    if c.abs() <= 2 * ERROR {
        return None;
    }
    let q = |n: i128, d: i128| (n << 62).div_euclid(d) << 2;
    let corners = [
        q(s - ERROR, c - ERROR),
        q(s - ERROR, c + ERROR),
        q(s + ERROR, c - ERROR),
        q(s + ERROR, c + ERROR),
    ];
    let lo = corners.iter().min().unwrap() - 4;
    let hi = corners.iter().max().unwrap() + 4;
    Some((lo, hi))
}

/// `[lo, hi]` clamped to the range of a type with `f` fractional bits and
/// `bits` bits, both in units of `2^-64`.
pub fn clamp(lo: i128, hi: i128, bits: u32, f: u32) -> (i128, i128) {
    let max = ((1i128 << (bits - 1)) - 1) << (SCALE - f);
    let min = -(1i128 << (bits - 1)) << (SCALE - f);
    (lo.max(min).min(max), hi.max(min).min(max))
}

/// `|got / 2^f - v| < 2^-f` for every `v ∈ [lo, hi] · 2^-64`.
pub fn within_ulp_of(got: i128, lo: i128, hi: i128, f: u32) -> bool {
    let ulp = 1i128 << (SCALE - f);
    let got = got << (SCALE - f);
    got - lo < ulp && hi - got < ulp
}

/// The value with `f` fractional bits nearest to every value of
/// `[lo, hi] · 2^-64`, if there is one.
pub fn rounded_interval(lo: i128, hi: i128, f: u32) -> Option<i128> {
    let s = SCALE - f;
    let round = |v: i128| (v + (1 << (s - 1))) >> s;
    if round(lo) == round(hi) {
        Some(round(lo))
    } else {
        None
    }
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

/// The `FixedFloat32` arguments whose `tan` lies so close to a midpoint
/// between neighbouring values (the closest `5.9·10⁻⁹` ulp from it) that the
/// bound of [`tan`] contains the midpoint and cannot decide the rounding;
/// sorted. The exhaustive test finds exactly these, and the oracle
/// checks that each is correctly rounded.
pub const TAN_NEAR_MIDPOINT_32: [i32; 178] = [
    -2139067299,
    -2113949028,
    -2069889146,
    -2066594924,
    -2046212082,
    -2041064907,
    -1996799093,
    -1993093134,
    -1977239805,
    -1949033221,
    -1886237559,
    -1853501461,
    -1852471980,
    -1832295062,
    -1767646418,
    -1757969707,
    -1756116712,
    -1725645376,
    -1657702484,
    -1618583917,
    -1483521775,
    -1466227231,
    -1404666852,
    -1397666727,
    -1352783271,
    -1341047720,
    -1316958862,
    -1307282108,
    -1242221732,
    -1233780339,
    -1198779677,
    -1198161836,
    -1177161294,
    -1169337583,
    -1121777589,
    -1072364604,
    -1070717520,
    -1062070233,
    -1055275947,
    -1050952318,
    -1035510754,
    -987127213,
    -981568261,
    -939978993,
    -935655365,
    -925566861,
    -861535895,
    -856182826,
    -754268568,
    -727503188,
    -726267857,
    -722356006,
    -670266496,
    -649677727,
    -644942335,
    -622294713,
    -605206062,
    -577823209,
    -570411090,
    -537675002,
    -525527634,
    -525321745,
    -522027539,
    -472202779,
    -452643511,
    -412907211,
    -409201242,
    -406524708,
    -392730285,
    -376465132,
    -371729724,
    -370494408,
    -331582092,
    -309345851,
    -309139961,
    -294933721,
    -272286110,
    -208872780,
    -186019283,
    -183136861,
    -159871581,
    -146900668,
    -140929934,
    -119105874,
    -93575833,
    -86369776,
    -76281284,
    -64545707,
    -23779993,
    23779993,
    64545707,
    76281284,
    86369776,
    93575833,
    119105874,
    140929934,
    146900668,
    159871581,
    183136861,
    186019283,
    208872780,
    272286110,
    294933721,
    309139961,
    309345851,
    331582092,
    370494408,
    371729724,
    376465132,
    392730285,
    406524708,
    409201242,
    412907211,
    452643511,
    472202779,
    522027539,
    525321745,
    525527634,
    537675002,
    570411090,
    577823209,
    605206062,
    622294713,
    644942335,
    649677727,
    670266496,
    722356006,
    726267857,
    727503188,
    754268568,
    856182826,
    861535895,
    925566861,
    935655365,
    939978993,
    981568261,
    987127213,
    1035510754,
    1050952318,
    1055275947,
    1062070233,
    1070717520,
    1072364604,
    1121777589,
    1169337583,
    1177161294,
    1198161836,
    1198779677,
    1233780339,
    1242221732,
    1307282108,
    1316958862,
    1341047720,
    1352783271,
    1397666727,
    1404666852,
    1466227231,
    1483521775,
    1618583917,
    1657702484,
    1725645376,
    1756116712,
    1757969707,
    1767646418,
    1832295062,
    1852471980,
    1853501461,
    1886237559,
    1949033221,
    1977239805,
    1993093134,
    1996799093,
    2041064907,
    2046212082,
    2066594924,
    2069889146,
    2113949028,
    2139067299,
];
