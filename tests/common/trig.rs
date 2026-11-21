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
    Some(round(lo)).filter(|&lo| lo == round(hi))
}

/// The value with `f` fractional bits nearest to `r / 2^64`, if every value
/// within [`ERROR`] of `r` rounds to it.
pub fn correctly_rounded(r: i128, f: u32) -> Option<i128> {
    rounded_interval(r - ERROR, r + ERROR, f)
}

/// `|got / 2^f - true value| < 2^-f` for every true value within [`ERROR`]
/// of `r`.
pub fn within_ulp(got: i128, r: i128, f: u32) -> bool {
    within_ulp_of(got, r - ERROR, r + ERROR, f)
}

/// The `FixedFloat32` arguments whose `tan` lies so close to a midpoint
/// between neighbouring values (the closest `5.9·10⁻⁹` ulp from it) that the
/// bound of [`tan`] contains the midpoint and cannot decide the rounding;
/// sorted. The exhaustive test finds exactly these, and the oracle
/// checks that each is correctly rounded.
pub const TAN_NEAR_MIDPOINT_32: [i32; 178] = [
    -2_139_067_299,
    -2_113_949_028,
    -2_069_889_146,
    -2_066_594_924,
    -2_046_212_082,
    -2_041_064_907,
    -1_996_799_093,
    -1_993_093_134,
    -1_977_239_805,
    -1_949_033_221,
    -1_886_237_559,
    -1_853_501_461,
    -1_852_471_980,
    -1_832_295_062,
    -1_767_646_418,
    -1_757_969_707,
    -1_756_116_712,
    -1_725_645_376,
    -1_657_702_484,
    -1_618_583_917,
    -1_483_521_775,
    -1_466_227_231,
    -1_404_666_852,
    -1_397_666_727,
    -1_352_783_271,
    -1_341_047_720,
    -1_316_958_862,
    -1_307_282_108,
    -1_242_221_732,
    -1_233_780_339,
    -1_198_779_677,
    -1_198_161_836,
    -1_177_161_294,
    -1_169_337_583,
    -1_121_777_589,
    -1_072_364_604,
    -1_070_717_520,
    -1_062_070_233,
    -1_055_275_947,
    -1_050_952_318,
    -1_035_510_754,
    -987_127_213,
    -981_568_261,
    -939_978_993,
    -935_655_365,
    -925_566_861,
    -861_535_895,
    -856_182_826,
    -754_268_568,
    -727_503_188,
    -726_267_857,
    -722_356_006,
    -670_266_496,
    -649_677_727,
    -644_942_335,
    -622_294_713,
    -605_206_062,
    -577_823_209,
    -570_411_090,
    -537_675_002,
    -525_527_634,
    -525_321_745,
    -522_027_539,
    -472_202_779,
    -452_643_511,
    -412_907_211,
    -409_201_242,
    -406_524_708,
    -392_730_285,
    -376_465_132,
    -371_729_724,
    -370_494_408,
    -331_582_092,
    -309_345_851,
    -309_139_961,
    -294_933_721,
    -272_286_110,
    -208_872_780,
    -186_019_283,
    -183_136_861,
    -159_871_581,
    -146_900_668,
    -140_929_934,
    -119_105_874,
    -93_575_833,
    -86_369_776,
    -76_281_284,
    -64_545_707,
    -23_779_993,
    23_779_993,
    64_545_707,
    76_281_284,
    86_369_776,
    93_575_833,
    119_105_874,
    140_929_934,
    146_900_668,
    159_871_581,
    183_136_861,
    186_019_283,
    208_872_780,
    272_286_110,
    294_933_721,
    309_139_961,
    309_345_851,
    331_582_092,
    370_494_408,
    371_729_724,
    376_465_132,
    392_730_285,
    406_524_708,
    409_201_242,
    412_907_211,
    452_643_511,
    472_202_779,
    522_027_539,
    525_321_745,
    525_527_634,
    537_675_002,
    570_411_090,
    577_823_209,
    605_206_062,
    622_294_713,
    644_942_335,
    649_677_727,
    670_266_496,
    722_356_006,
    726_267_857,
    727_503_188,
    754_268_568,
    856_182_826,
    861_535_895,
    925_566_861,
    935_655_365,
    939_978_993,
    981_568_261,
    987_127_213,
    1_035_510_754,
    1_050_952_318,
    1_055_275_947,
    1_062_070_233,
    1_070_717_520,
    1_072_364_604,
    1_121_777_589,
    1_169_337_583,
    1_177_161_294,
    1_198_161_836,
    1_198_779_677,
    1_233_780_339,
    1_242_221_732,
    1_307_282_108,
    1_316_958_862,
    1_341_047_720,
    1_352_783_271,
    1_397_666_727,
    1_404_666_852,
    1_466_227_231,
    1_483_521_775,
    1_618_583_917,
    1_657_702_484,
    1_725_645_376,
    1_756_116_712,
    1_757_969_707,
    1_767_646_418,
    1_832_295_062,
    1_852_471_980,
    1_853_501_461,
    1_886_237_559,
    1_949_033_221,
    1_977_239_805,
    1_993_093_134,
    1_996_799_093,
    2_041_064_907,
    2_046_212_082,
    2_066_594_924,
    2_069_889_146,
    2_113_949_028,
    2_139_067_299,
];
