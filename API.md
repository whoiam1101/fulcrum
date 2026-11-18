# fulcrum 0.5: API guide

**English** · [Русский](API.ru.md)

How to use the library: the types, how to create values, what operations do at the edges, how to serialize, and how to write generic code. Describes `v0.6.0`.

## 1. Setup

```toml
[dependencies]
fulcrum = { git = "https://github.com/whoiam1101/fulcrum", tag = "v0.6.0" }
```

The crate is `no_std`, has no required dependencies, MSRV 1.60, and no `unsafe` outside the optional `bytemuck` feature. Features (all off by default):

| Feature | What it adds |
|---|---|
| `std` | `std::error::Error` for `ParseError` and `OverflowError` |
| `float-convert` | `to_f64`, `checked_from_f64`, `saturating_from_f64`, for debugging and rendering |
| `strict-overflow` | operators panic instead of saturating, for tests and CI of an engine only |
| `serde` | `Serialize`, `Deserialize`: a decimal string in human-readable formats, the raw integer in binary ones (§14) |
| `bytemuck` | `Pod`, `Zeroable`, for casting slices to bytes; the only `unsafe` of the crate (the impls of these two traits) |
| `num-traits` | `Zero`, `One`, `Bounded`, `Num`, `Signed` |

Everything public is at the crate root: `use fulcrum::{ff32, FixedFloat32, FixedFloat};`.

## 2. Types

| Type | Format | Raw | Range | Step (ulp) | Literal | Accumulator |
|---|---|---|---|---|---|---|
| `FixedFloat8` | Q4.4 | `i8` | `[-8, 7.9375]` | `2⁻⁴ = 0.0625` | `ff8!` | `Accumulator8` |
| `FixedFloat16` | Q8.8 | `i16` | `[-128, 127.996]` | `2⁻⁸ ≈ 0.0039` | `ff16!` | `Accumulator16` |
| `FixedFloat32` | Q16.16 | `i32` | `[-32768, 32767.99998]` | `2⁻¹⁶ ≈ 1.5·10⁻⁵` | `ff32!` | `Accumulator32` |
| `FixedFloat64` | Q32.32 | `i64` | `±2.1·10⁹` | `2⁻³² ≈ 2.3·10⁻¹⁰` | `ff64!` | `Accumulator64` |

A value is `raw / 2^FRAC_BITS`. The types are `Copy`, `Default` (= 0), `Eq`, `Ord`, `Hash`, and `#[repr(transparent)]` over the raw integer. Order and equality are those of the raw integers: there is no `NaN`, `-0` or infinity.

Associated constants of every type: `FRAC_BITS`, `INT_BITS` (including the sign bit), `ZERO`, `ONE`, `NEG_ONE`, `HALF`, `MIN`, `MAX`, `DELTA` (one ulp).

Choosing a width: `FixedFloat64` is the default for simulation (positions, velocities, time); `FixedFloat32` when memory and speed matter and a range of ±32768 with a step of 1.5·10⁻⁵ is enough; 8 and 16 bits for compact data (network packets, parameters, tables) and for tests, since they can be checked exhaustively.

## 3. Creating values

```rust
use fulcrum::{ff32, ff64, FixedFloat32, FixedFloat64};
use core::convert::TryFrom;

const SPEED: FixedFloat64 = ff64!(12.6);
const NEG: FixedFloat32 = ff32!(-0.25);
const BIG: FixedFloat64 = ff64!(1_000_000);

let dt: FixedFloat64 = "0.016".parse().unwrap();
let n = FixedFloat32::from(7i16);
let m = FixedFloat32::try_from(-5i32).unwrap();
let third = FixedFloat32::saturating_from_ratio(1, 3);
let raw = FixedFloat32::from_bits(0x0001_8000);
let parts = FixedFloat32::from_parts(-2, 49152);
```

| Way | Rounding | Out of range |
|---|---|---|
| `ff32!(…)` and the other literals | to nearest, ties up | compile error |
| `parse(s)` / `s.parse()` (`FromStr`), `const fn` | to nearest, ties up | `Err(ParseError)`, `kind() == Overflow` |
| `From<iN/uN>` | exact | cannot happen: implemented only where it always fits |
| `TryFrom<iN/uN>` (those of `i8…i128`, `u8…u128` without a `From`) | exact | `Err(OverflowError)` |
| `saturating_from_int(i128)`, `checked_from_int(i128)` | exact | saturates / `None` |
| `saturating_from_ratio(num, den)`, `checked_from_ratio` (in the raw type) | to nearest, ties up | saturates / `None`; `den = 0` behaves like division by zero |
| `from_bits(raw)` | — | always exact |
| `from_parts(int, frac)`, `checked_from_parts` | — | saturates / `None` |
| `checked_from_scaled_bits(raw, src_frac)`, `saturating_from_scaled_bits`, `wrapping_from_scaled_bits`: `raw / 2^src_frac` for any `i128` and any `src_frac` | to nearest, ties up, once | `None` / saturates by the sign of `raw` / low bits |
| `saturating_from_f64(x)`, `checked_from_f64(x)` (feature `float-convert`) | to nearest, ties up | saturates / `None`; `NaN` gives `0` / `None` |

`From` integers: `FixedFloat16` from `i8`; `FixedFloat32` from `i8`, `u8`, `i16`; `FixedFloat64` from `i8`, `u8`, `i16`, `u16`, `i32`. `FixedFloat8` has none: not even `i8` fits.

`from_parts` and `int_part`/`frac_part` are inverses. The integer part rounds toward `-∞`, the fractional part is non-negative and in units of one ulp: `-1.25` in `FixedFloat32` is `(-2, 49152)`, because `-2 + 49152/65536 = -1.25`.

**Literals** are parsed exactly at compile time, without `f64`. `ff64!(0.1)` is the value nearest to decimal `0.1`, not to `0.1f64`. `_` between digits and a leading `-` are allowed. A literal is always a constant and works in `const` and `static`.

**Strings**: the grammar is `[+-]? digits? ('.' digits?)?` with at least one digit. No exponent (`1e3`), no `_`, no whitespace trimming. `".5"`, `"5."`, `"+3"` are accepted. Parsing is exact for strings of any length: the result is the correctly rounded value of the decimal number.

## 4. Arithmetic

### Operators

`+ - * / %`, unary `-`, their `*Assign` forms and the reference variants (`&a + b`, `a + &b`, `&a + &b`) **saturate** and never panic (without `strict-overflow`).

- `+`, `-`, `%` are exact.
- `*` and `/` round to nearest, **ties toward `+∞`**. The rule is the same across the library: literals, `parse`, narrowing, `>>`, `div_int`, accumulators. One ulp of `FixedFloat8` as an example: `DELTA * HALF == DELTA` (0.03125 → 0.0625), while `-DELTA * HALF == 0` (-0.03125 → 0).
- `%` is `self - rhs · trunc(self / rhs)`, with the sign of the dividend, like the integers.

### Division by zero

| Operation | Result |
|---|---|
| `x / 0`, `saturating_div`, `wrapping_div`, `div_int(0)`, `saturating_from_ratio(n, 0)` | `MAX` for `x > 0`, `MIN` for `x < 0`, `0` for `x = 0` |
| `x % 0`, `saturating_rem`, `wrapping_rem` | `0` |
| `checked_div`, `checked_rem`, `checked_div_int`, `checked_recip`, `checked_from_ratio` | `None` |
| `overflowing_div`, `overflowing_rem` | the result above and `true` |
| `recip()` of zero | `MAX` |

### Explicit overflow semantics

Same as the primitive integers. Everything below is a `const fn`.

| Operation | `checked_` → `Option` | `saturating_` | `wrapping_` | `overflowing_` → `(v, bool)` | operator |
|---|---|---|---|---|---|
| addition | `checked_add` | `saturating_add` | `wrapping_add` | `overflowing_add` | `+` |
| subtraction | `checked_sub` | `saturating_sub` | `wrapping_sub` | `overflowing_sub` | `-` |
| multiplication | `checked_mul` | `saturating_mul` | `wrapping_mul` | `overflowing_mul` | `*` |
| division | `checked_div` | `saturating_div` | `wrapping_div` | `overflowing_div` | `/` |
| remainder | `checked_rem` | `saturating_rem` | `wrapping_rem` | `overflowing_rem` | `%` |
| negation | `checked_neg` | `saturating_neg` | `wrapping_neg` | `overflowing_neg` | unary `-` |
| absolute value | `checked_abs` | `saturating_abs` (= `abs`) | `wrapping_abs` | `overflowing_abs` | — |
| `· 2ⁿ` | `checked_shl` | `saturating_shl` | `wrapping_shl` | — | `<< n` |
| `· n` (integer) | `checked_mul_int` | `mul_int` | `wrapping_mul_int` | — | — |
| `/ n` (integer) | `checked_div_int` | `div_int` | — | — | — |

`wrapping_*` keep the raw result modulo `2^BITS`: `MAX.wrapping_add(DELTA) == MIN`. Multiplication and division round first, then wrap.

### Shifts

`x << n` is the exact `x · 2ⁿ`, saturating; any `n` is accepted. `x >> n` is `x / 2ⁿ` with the same rounding as `/`, so `x >> 1 == x / 2` for every `x`. It is **not** an arithmetic shift of the raw value: `DELTA >> 1 == DELTA`, `-DELTA >> 1 == 0`. For a raw bit shift, use `to_bits()`.

`wrapping_shl(n)` with `n ≥ BITS` gives `0`; unlike the primitives, `n` is not masked.

### Other methods

| Method | What it does |
|---|---|
| `abs()` | absolute value, saturating: `MIN.abs() == MAX` |
| `signum()` | `-1`, `0` or `1` |
| `is_negative()`, `is_positive()`, `is_zero()` | sign |
| `min`, `max` | as in `Ord`, but `const fn` |
| `clamp(lo, hi)` | never panics; returns `hi` when `lo > hi` |
| `abs_diff(other)` | `|a - b|`, saturating |
| `midpoint(other)` | `(a + b) / 2` without intermediate overflow, with the common rounding rule |
| `recip()` | `1 / x`, saturating |
| `sqr()` | `x · x`, saturating |
| `mul_int(n)`, `div_int(n)` | multiplication (exact) and division (rounded) by an integer of the raw type |

### Rounded once: `mul_add`, `mul_div`, `lerp`

These compute the exact result of three operands and round and saturate it once. The intermediate product is never rounded or saturated, so they are more accurate than the same chain of operators and do not fail when only an intermediate value is out of range.

| Method | Value | Out of range | `checked_*` |
|---|---|---|---|
| `x.mul_add(a, b)` | `x · a + b` | saturates | `checked_mul_add` |
| `x.mul_div(a, b)` | `x · a / b`; `b = 0` gives `MAX`, `MIN` or `0` by the sign of `x · a` | saturates | `checked_mul_div`, `None` also for `b = 0` |
| `a.lerp(b, t)` | `a + (b - a) · t`: `t = 0` gives `a`, `t = 1` gives `b` exactly, other `t` extrapolate | saturates | `checked_lerp` |

```rust
use fulcrum::{ff64, FixedFloat64};

let big = FixedFloat64::MAX;
assert_eq!(big * big / big, FixedFloat64::ONE);
assert_eq!(big.mul_div(big, big), big);
assert_eq!(ff64!(10).lerp(ff64!(20), ff64!(0.25)), ff64!(12.5));
```

The explicit methods keep their semantics under `strict-overflow`: they saturate, like `abs` and `mul_int`.

### Square roots: `sqrt`, `rsqrt`, `hypot`

All three are correctly rounded to nearest (error ≤ ½ ulp): the result is the representable value nearest to the exact root. There are no ties: a root is never exactly halfway between two values.

| Method | Value | Outside the domain or range | `checked_*` |
|---|---|---|---|
| `x.sqrt()` | `√x`; never overflows | `x < 0` gives `0` | `checked_sqrt`: `None` for `x < 0` |
| `x.rsqrt()` | `1 / √x`; never overflows for `x > 0` | `x ≤ 0` gives `MAX`, like `recip(0)` | `checked_rsqrt`: `None` for `x ≤ 0` |
| `x.hypot(y)` | `√(x² + y²)`, the squares are exact and never overflow | saturates | `checked_hypot` |

```rust
use fulcrum::{ff32, FixedFloat32};

assert_eq!(ff32!(2).sqrt(), FixedFloat32::SQRT_2);
assert_eq!(ff32!(4).rsqrt(), ff32!(0.5));
assert_eq!(ff32!(3).hypot(ff32!(-4)), ff32!(5));
assert_eq!(FixedFloat32::MAX.hypot(FixedFloat32::MAX), FixedFloat32::MAX);
```

`rsqrt` is one rounding of `1 / √x`, more accurate than `x.sqrt().recip()`, which rounds twice.

### Sine and cosine in turns: `sin_turns`, `cos_turns`

The angle is in turns: `1.0` is 360°, `0.25` is 90°. Only the fraction of a turn matters, so the range reduction is a bit mask: exact on every input, it never overflows, and a game angle stored in turns loses nothing to `π`. The result is in `[-1, 1]` and within 1 ulp of the exact value; on `FixedFloat8`, `FixedFloat16` and `FixedFloat32` every result is checked to be correctly rounded.

| Method | Value | Symmetries, bit for bit (`-x` for `x > MIN`: `-MIN` saturates) |
|---|---|---|
| `x.sin_turns()` | `sin(2π·x)` | `sin_turns(-x) = -sin_turns(x)`, `sin_turns(x + 1) = sin_turns(x)` |
| `x.cos_turns()` | `cos(2π·x)` | `cos_turns(x) = sin_turns(x + ¼)`, `cos_turns(-x) = cos_turns(x)` |

```rust
use fulcrum::{ff32, ff64, FixedFloat32};

assert_eq!(ff32!(0.25).sin_turns(), FixedFloat32::ONE);
assert_eq!(ff32!(0.5).cos_turns(), -FixedFloat32::ONE);
assert_eq!(ff32!(1000.125).sin_turns(), ff32!(0.125).sin_turns());
assert_eq!(ff64!(0.125).sin_turns(), ff64!(0.125).cos_turns());
```

### Sine, cosine and tangent in radians: `sin`, `cos`, `sin_cos`, `tan`

The angle is in radians. The range reduction multiplies the value exactly by 192 bits of `2/π`, so it is accurate on every input, `FixedFloat64::MAX` included. `sin` and `cos` are in `[-1, 1]` and within 1 ulp of the exact value; `tan` is within 1 ulp of the exact value clamped to the range. On `FixedFloat8`, `FixedFloat16` and `FixedFloat32` every result is checked to be correctly rounded.

| Method | Value | Symmetries, bit for bit (`-x` for `x > MIN`) |
|---|---|---|
| `x.sin()` | `sin x` | `sin(-x) = -sin(x)` |
| `x.cos()` | `cos x` | `cos(-x) = cos(x)` |
| `x.sin_cos()` | `(x.sin(), x.cos())`, one range reduction | |
| `x.tan()` | `tan x`, saturated near the poles | `tan(-x) = -tan(x)` where it does not saturate (`MIN` and `-MAX` differ) |
| `x.checked_tan()` | `tan x`, `None` when the rounded value is out of range | |

```rust
use fulcrum::{ff32, ff64, FixedFloat32, FixedFloat64};

assert_eq!(FixedFloat32::ZERO.sin_cos(), (FixedFloat32::ZERO, FixedFloat32::ONE));
assert_eq!(FixedFloat32::PI.cos(), -FixedFloat32::ONE);
assert_eq!(ff32!(-0.5).sin(), -ff32!(0.5).sin());
assert_eq!(FixedFloat64::FRAC_PI_2.tan(), FixedFloat64::MAX);
assert_eq!(FixedFloat64::FRAC_PI_2.checked_tan(), None);
assert_eq!(ff64!(1000000000).sin(), ff64!(0.545843449421226978302001953125));
```

`sin_cos` is also in the `FixedFloat` trait. An angle that only turns and is added up, as in a game, keeps more in turns (`sin_turns`): there the reduction is a mask and `π` never enters. For angles that keep turning see the angle types below.

### Inverse functions: `atan`, `atan2`, `asin`, `acos`

The result is in radians and within 1 ulp of the exact value; on `FixedFloat8`, `FixedFloat16` and `FixedFloat32` every result (and every pair of `atan2` on `FixedFloat8`) is checked to be correctly rounded. Nothing overflows: the result is at most `π` in magnitude, which every type holds, and `atan2` takes the exact ratio of its two arguments, whatever their size.

| Method | Value | Range | Symmetries, bit for bit |
|---|---|---|---|
| `x.atan()` | `atan x` | `[-π/2, π/2]` | `atan(-x) = -atan(x)` for `x > MIN` |
| `y.atan2(x)` | the angle of the point `(x, y)`, like `f64::atan2` | `(-π, π]`, rounded: `[-π, π]` | `atan2(-y, x) = -atan2(y, x)` for `y ≠ 0` |
| `x.asin()` | `asin x`; `x` outside `[-1, 1]` is clamped to it | `[-π/2, π/2]` | `asin(-x) = -asin(x)` |
| `x.acos()` | `acos x`; `x` outside `[-1, 1]` is clamped to it | `[0, π]` | |
| `x.checked_asin()`, `x.checked_acos()` | `None` outside `[-1, 1]` | | |

`atan2(0, 0) = 0` and `atan2(0, x) = π` for `x < 0`: there is no `-0`, so the cut along the negative axis goes to `+π`.

```rust
use fulcrum::{ff32, ff64, FixedFloat32, FixedFloat64};

assert_eq!(ff32!(1).atan(), FixedFloat32::FRAC_PI_4);
assert_eq!(ff32!(0).atan2(ff32!(-1)), FixedFloat32::PI);
assert_eq!(ff32!(-1).atan2(ff32!(0)), -FixedFloat32::FRAC_PI_2);
assert_eq!(ff64!(0.5).asin(), FixedFloat64::FRAC_PI_6);
assert_eq!(ff32!(-1).acos(), FixedFloat32::PI);
assert_eq!(ff32!(2).asin(), FixedFloat32::FRAC_PI_2);
assert_eq!(ff32!(2).checked_asin(), None);
```

`atan2` is also in the `FixedFloat` trait.

### Binary logarithm and exponential: `log2`, `exp2`

Within 1 ulp of the exact value; on `FixedFloat8`, `FixedFloat16` and `FixedFloat32` every result is checked to be correctly rounded, and both functions are checked to be monotone.

| Method | Value | Out of the domain or range |
|---|---|---|
| `x.log2()` | `log₂ x`, exact on powers of two; never overflows | `x ≤ 0` gives `MIN`, the saturation of `-∞` |
| `x.checked_log2()` | the same | `None` for `x ≤ 0` |
| `x.exp2()` | `2^x`, exact on integers `≥ -FRAC_BITS`; `0` below `-FRAC_BITS - 1` | saturates to `MAX` |
| `x.checked_exp2()` | the same | `None` when the rounded result is out of range |

The split of `x` into its integer part and its fraction is exact, so `exp2` loses nothing on any input; `2^(-FRAC_BITS - 1)`, exactly half an ulp, rounds up to `DELTA` by the rule of `*` and `/`.

```rust
use fulcrum::{ff32, FixedFloat32};

assert_eq!(ff32!(8).log2(), ff32!(3));
assert_eq!(ff32!(0.5).log2(), ff32!(-1));
assert_eq!(ff32!(0).log2(), FixedFloat32::MIN);
assert_eq!(ff32!(0.5).exp2(), FixedFloat32::SQRT_2);
assert_eq!(ff32!(-17).exp2(), FixedFloat32::DELTA);
assert_eq!(ff32!(15).exp2(), FixedFloat32::MAX);
assert_eq!(ff32!(15).checked_exp2(), None);
```

### Natural logarithm and exponential: `ln`, `exp`

The same guarantees as `log2` and `exp2`: within 1 ulp of the exact value, every result of `FixedFloat8`, `FixedFloat16` and `FixedFloat32` checked to be correctly rounded, both functions checked to be monotone there.

| Method | Value | Out of the domain or range |
|---|---|---|
| `x.ln()` | `ln x`, exact at `1`; never overflows | `x ≤ 0` gives `MIN`, the saturation of `-∞` |
| `x.checked_ln()` | the same | `None` for `x ≤ 0` |
| `x.exp()` | `e^x`, exact at `0`; `0` below about `-(FRAC_BITS + 1) · ln 2` | saturates to `MAX` |
| `x.checked_exp()` | the same | `None` when the rounded result is out of range |

`exp` reduces `x` by an exact multiple of `ln 2 / 256` at 112 fractional bits, so the error of the reduction stays far below an ulp on every input, also at the top of the range of `FixedFloat64`.

```rust
use fulcrum::{ff32, FixedFloat32};

assert_eq!(ff32!(1).exp(), FixedFloat32::E);
assert_eq!(ff32!(0).exp(), ff32!(1));
assert_eq!(FixedFloat32::E.ln(), ff32!(1));
assert_eq!(ff32!(0).ln(), FixedFloat32::MIN);
assert_eq!(ff32!(-12).exp(), ff32!(0));
assert_eq!(ff32!(11).exp(), FixedFloat32::MAX);
assert_eq!(ff32!(11).checked_exp(), None);
```

### Powers: `pow`, `powi`

`x.pow(y)` is `2^(y · log₂ x)` with a logarithm of 120 fractional bits, so the error of the exponent stays far below an ulp for every `y` of the type; `x.powi(n)` is the same for an integer `n: i32`. Both are within 1 ulp on every width (within `½ + 2^-5.7` ulp on `FixedFloat64`, `½ + 2^-37` up to `FixedFloat32`). Every pair of `FixedFloat8` and `FixedFloat16` is checked to be correctly rounded, except where the exact power falls exactly halfway between two values (such as `(3/8)³` on `FixedFloat16`): such a tie may round either way, not always toward `+∞`. On `FixedFloat64` a result within `2^-5.7` ulp of a halfway point, which occurs near `MAX`, may also round the wrong way. A result that is exactly representable comes out exactly.

| Method | Value | Out of the domain or range |
|---|---|---|
| `x.pow(y)` | `x^y`; `x^0 = 1` for every `x`; `0^y = 0` for `y > 0`; a negative `x` takes the sign of an odd integer `y` | `0^y` for `y < 0` gives `MAX`; a negative `x` with a non-integer `y` gives `0`; saturates to `MAX` or `MIN` by the sign |
| `x.checked_pow(y)` | the same | `None` in each of these cases |
| `x.powi(n)` | `x^n`, `n: i32` | as `pow` |
| `x.checked_powi(n)` | the same | `None` when the rounded result is out of range or `x = 0`, `n < 0` |

```rust
use fulcrum::{ff32, FixedFloat32};

assert_eq!(ff32!(4).pow(ff32!(0.5)), ff32!(2));
assert_eq!(ff32!(2).pow(ff32!(0.5)), FixedFloat32::SQRT_2);
assert_eq!(ff32!(-2).powi(3), ff32!(-8));
assert_eq!(ff32!(-2).pow(ff32!(0.5)), ff32!(0));
assert_eq!(ff32!(-2).checked_pow(ff32!(0.5)), None);
assert_eq!(ff32!(0).powi(-1), FixedFloat32::MAX);
assert_eq!(ff32!(10).checked_powi(5), None);
```

`log2`, `exp2`, `ln`, `exp`, `pow` and `powi` are also in the `FixedFloat` trait.

### Angles: `Angle8` … `Angle64`

An angle kept as every bit of an unsigned integer, the fraction `raw / 2^BITS` of a turn: `Angle8` has 256 steps per turn, `Angle16` 65 536, `Angle32` and `Angle64` steps of `1.46·10⁻⁹` and `3.4·10⁻¹⁹` radians. `+`, `-` and unary `-` wrap modulo a turn, so an angle that keeps turning never needs a range reduction, never saturates, and a sum of rotations does not depend on the order. Each `AngleN` goes with `FixedFloatN`: its sine and cosine are `FixedFloatN`, within 1 ulp (on `Angle8`, `Angle16` and `Angle32` every result is checked to be correctly rounded and equal to `sin_turns` of the same angle).

| Method | Value |
|---|---|
| `ZERO`, `DELTA`, `QUARTER_TURN`, `HALF_TURN`, `BITS` | constants |
| `from_bits(u)`, `to_bits()` | the raw fraction of a turn |
| `from_turns(x)` | `x` turns, exactly: only the fraction of `x` matters |
| `to_turns()` | the angle in turns, in `[0, 1)`, rounded to nearest |
| `from_radians(x)` | `x / 2π` modulo a turn, rounded to nearest; exact range reduction by 192 bits of `2/π`; `from_radians(-x) = -from_radians(x)` |
| `to_radians()` | the angle in radians, rounded to nearest: the exact value is in `[-π, π)`, the rounded one in `[-PI, PI]` (just below `HALF_TURN` it rounds up to `PI`); `HALF_TURN` gives `-PI` |
| `sin()`, `cos()`, `sin_cos()` | within 1 ulp; `sin` odd, `cos` even, `cos(a) = sin(a + QUARTER_TURN)` bit for bit |
| `a + b`, `a - b`, `-a`, `+=`, `-=`, `wrapping_*` | modulo a turn |
| `a.scale(x)`, `a * x`, `a *= x` | `a · x` modulo a turn, rounded to nearest (ties toward `+∞`), `a` taken in `[-½, ½)` of a turn: a turn rate times a time step |

```rust
use fulcrum::{ff32, Angle16, Angle32, FixedFloat32};

let mut heading = Angle32::from_radians(FixedFloat32::FRAC_PI_2);
let rate = Angle32::from_turns(ff32!(0.25));
heading += rate * ff32!(0.5);
heading += Angle32::HALF_TURN + Angle32::HALF_TURN;
let (s, c) = heading.sin_cos();
assert_eq!(Angle16::QUARTER_TURN.sin_cos().0, fulcrum::FixedFloat16::ONE);
assert_eq!(Angle32::HALF_TURN.to_radians(), -FixedFloat32::PI);
assert_eq!(Angle32::from_turns(ff32!(1.25)), Angle32::QUARTER_TURN);
assert!(s > c);
```

There is no `Ord`: angles on a circle have no order. The trait `FixedAngle` (every method and constant above, the raw type `Bits` and the paired fixed-point type `Fixed`) and the associated type `FixedFloat::Angle` let generic code go from a fixed-point type to its angle type.

### Vectors: `Vec2`, `Vec3`

`Vec2<T>` and `Vec3<T>` over any fixed-point type, with public fields `x`, `y` (`z`), `#[repr(C)]`: two or three components in a row, no padding. Aliases name each width: `Vec2f8` … `Vec2f64`, `Vec3f8` … `Vec3f64`. The rules are those of the scalars: operators saturate per component (and panic under `strict-overflow`), and every method that combines components rounds once, from exact intermediates.

| Method | Value |
|---|---|
| `new`, `splat(v)`, `ZERO`, `X`, `Y`, `Z` | constructors and unit vectors |
| `a + b`, `a - b`, `-a`, `a * b`, `a * s`, `s * a`, `a / s`, `*Assign` | per component, like the operators of the component; `a * b` is the component-wise product |
| `min`, `max`, `abs`, `lerp(b, t)` | per component; `lerp` rounds once per component |
| `dot`, `length_sq`, `distance_sq`, `perp_dot` (`Vec2`), `cross` (`Vec3`) | the exact sum of exact products, rounded once and saturated; a difference of components out of range gives `MAX` for the distances |
| `length`, `distance` | correctly rounded root of the exact sum of squares (`hypot` for `Vec2`) |
| `try_normalize`, `normalize` | each component, `x` divided by the length, correctly rounded; the zero vector gives `None` and `ZERO` |
| `clamp_length_max(max)`, `clamp_length(min, max)` | scaled to the bound when longer (shorter) than it: exact comparison, correctly rounded components; `min` is checked first, like `glam`; negative bounds count as `0` |
| `perp()` (`Vec2`) | `(-y, x)`, a quarter turn counterclockwise |
| `rotate(angle)` (`Vec2`) | turned by an angle type `T::Angle`, with a sine and cosine of 62 bits: within 1 ulp for a length below `2^(57 - FRAC_BITS)` (every vector up to `FixedFloat32`, `3.3·10⁷` for `FixedFloat64`); quarter turns are exact |
| `angle_to(b)` | `Vec2`: the signed angle from `a` to `b` in `(-π, π]`; `Vec3`: the angle between them in `[0, π]`; `atan2` of exact cross and dot products, within 1 ulp; `0` for a zero vector |
| `to_le_bytes`, `from_le_bytes`, `to_be_bytes`, `from_be_bytes` | the components in order, each in its own format (§8) |

```rust
use fulcrum::{ff32, Angle32, FixedFloat32, Vec2, Vec2f32, Vec3};

let v = Vec2::new(ff32!(3), ff32!(4));
assert_eq!(v.length(), ff32!(5));
assert_eq!(v.normalize(), Vec2::new(ff32!(0.6), ff32!(0.8)));
assert_eq!(v.clamp_length_max(ff32!(2.5)), Vec2::new(ff32!(1.5), ff32!(2)));
assert_eq!(Vec2f32::X.rotate(Angle32::QUARTER_TURN), Vec2f32::Y);
assert_eq!(Vec2f32::X.angle_to(Vec2f32::Y), FixedFloat32::FRAC_PI_2);
let mut pos = Vec3::new(ff32!(1), ff32!(2), ff32!(3));
pos += Vec3::splat(ff32!(0.5)) * ff32!(2);
assert_eq!(pos, Vec3::new(ff32!(2), ff32!(3), ff32!(4)));
```

With `serde`, a vector is a tuple of its components (`["1.5","-2"]` in JSON); with `bytemuck`, `Vec2<T>` and `Vec3<T>` are `Pod` when `T` is.

## 5. Rounding and integers

| Method | Rule | Overflow |
|---|---|---|
| `floor` | toward `-∞` | never |
| `ceil`, `checked_ceil` | toward `+∞` | saturates / `None` near `MAX` |
| `trunc` | toward zero | never |
| `fract` | `x - trunc(x)`, with the sign of `x` | never |
| `round`, `checked_round` | to nearest, ties **away from zero** | saturates / `None` |
| `round_ties_even`, `checked_round_ties_even` | to nearest, ties to even | saturates / `None` |

The same rules returning an integer of the raw type: `to_int_floor`, `to_int_ceil`, `to_int_trunc`, `to_int_round`, `to_int_round_ties_even`. They never overflow, because the raw integer is wider than the integer part.

Example: `-1.25` gives `floor = -2`, `ceil = -1`, `trunc = -1`, `fract = -0.25`. `2.5.round() = 3`, `(-2.5).round() = -3`, `2.5.round_ties_even() = 2`.

Note that `round` (ties away from zero, like `f64::round`) differs from the rule of `*` and `/` (ties toward `+∞`).

## 6. Conversions between widths

| Direction | How | Result |
|---|---|---|
| narrow → wide | `From` / `.into()` | always exact |
| wide → narrow | `TryFrom` | fractional part rounds to nearest (ties up); `Err(OverflowError)` when the integer part does not fit |
| any → any | `T::saturating_from(x)` | rounds, saturates |
| any → any | `T::wrapping_from(x)` | rounds, keeps the low bits |

```rust
let w: FixedFloat64 = ff16!(1.5).into();
assert_eq!(FixedFloat8::try_from(ff32!(1.03125)), Ok(ff8!(1.0625)));
assert!(FixedFloat8::try_from(ff32!(100)).is_err());
assert_eq!(FixedFloat8::saturating_from(ff32!(100)), FixedFloat8::MAX);
assert_eq!(FixedFloat8::wrapping_from(ff32!(100)), ff8!(4));
```

`saturating_from` and `wrapping_from` take any `T: FixedFloat`, including the same type.

## 7. Text

**`Display`** prints the value exactly: a binary fraction with `F` bits has at most `F` decimal digits. So `ff32!(0.1)` prints as `0.100006103515625`, which is the stored value.

With a precision `{:.N}` it rounds to nearest, **ties to even**, like `f64` formatting: `{:.1}` gives `0.2` for `0.25` and `0.8` for `0.75`. Width, fill, alignment, `+` and `0` are supported: `format!("{:+08.3}", ff32!(3.14159)) == "+003.142"`.

`parse(display(x)) == x` for every value (checked on all 2³² values of `FixedFloat32`).

**`Debug`** prints the value and the raw bits in hex: `1.5 (0x00018000)`, so logs show exactly what is in memory.

**Parse errors** are `ParseError` with a `kind()` method:

| `ParseErrorKind` | When |
|---|---|
| `Empty` | empty string or only a sign |
| `InvalidDigit` | an extra character: exponent, whitespace, `_`, a second dot |
| `Overflow` | the number does not fit the type |

`ParseErrorKind` is `#[non_exhaustive]`, so a `match` needs a `_` arm.

## 8. Bytes

`to_le_bytes`, `from_le_bytes`, `to_be_bytes`, `from_be_bytes`: the raw value as `[u8; 1|2|4|8]`. The layout does not depend on the platform. Little-endian is the canonical format for snapshots, replays and checksums:

```rust
assert_eq!(ff32!(1.5).to_le_bytes(), [0x00, 0x80, 0x01, 0x00]);
assert_eq!(FixedFloat32::from_le_bytes([0x00, 0x80, 0x01, 0x00]), ff32!(1.5));
```

A simulation state hash is a hash of the bytes of its numbers. `Hash` is deterministic too, but the result depends on the hasher, so compare bytes across machines.

## 9. Constants

Correctly rounded for every type, generated by `tools/gen-tables` with exact arithmetic:

`PI`, `TAU`, `FRAC_PI_2`, `FRAC_PI_3`, `FRAC_PI_4`, `FRAC_PI_6`, `FRAC_PI_8`, `FRAC_1_PI`, `FRAC_2_PI`, `SQRT_2`, `FRAC_1_SQRT_2`, `SQRT_3`, `FRAC_1_SQRT_3`, `E`, `LN_2`, `LN_10`, `LOG2_E`, `LOG2_10`, `LOG10_2`, `LOG10_E`, `GOLDEN_RATIO`, `DEG_TO_RAD`, `RAD_TO_DEG`.

`FixedFloat8` has no `DEG_TO_RAD` (rounds to zero) and no `RAD_TO_DEG` (out of range). Narrow types are coarse: `FixedFloat8::PI == 3.125`.

## 10. Sums and accumulators

The main tool for determinism in parallel code.

**`Iterator::sum`** is exact: all terms are added into an `i128` without saturation, and the total saturates once at the end. The result depends neither on the order nor on intermediate overflow. `fold` with `+` saturates at every step and behaves differently:

```rust
let xs = [FixedFloat32::MAX, FixedFloat32::ONE, -FixedFloat32::ONE];
let s: FixedFloat32 = xs.iter().sum();
let f = xs.iter().fold(FixedFloat32::ZERO, |a, b| a + *b);
assert_eq!(s, FixedFloat32::MAX);
assert_eq!(f, FixedFloat32::MAX - FixedFloat32::ONE);
```

**`AccumulatorN`** is the same sum as a value that can be split between threads:

| Method | What it does |
|---|---|
| `T::accumulator()`, `AccumulatorN::new()`, `ZERO`, `Default` | empty |
| `add(x)`, `sub(x)`, `extend(iter)`, `collect()` | exact addition |
| `add_product(a, b)` | exact unrounded product |
| `merge(other)`, `Sum<AccumulatorN>` | combine partial sums; associative and commutative |
| `finish()` | rounds and saturates once |
| `checked_finish()` | `None` when the total is out of range |

```rust
let mut left = FixedFloat64::accumulator();
left.extend(&xs[..mid]);
let mut right = FixedFloat64::accumulator();
right.extend(&xs[mid..]);
assert_eq!(left.merge(right).finish(), xs.iter().sum::<FixedFloat64>());
```

Any split between threads and any tree of `merge` calls gives the same bits. An accumulator is `Copy`, `Eq` and `Hash`: its state can be compared and sent over the network.

**A dot product** built with `add_product` is rounded once instead of at every term, so it is more accurate and still order-independent. For `FixedFloat32`, `0.1·0.1 + 0.1·0.1` gives `0.0200042724609375` through `add_product` and `0.019989013671875` through `*` and `+`. `Accumulator64` keeps a 256-bit state, so its products at scale `2⁻⁶⁴` are exact too.

**`Iterator::product`** is just `*` in iteration order. Rounded multiplication is not associative, so the caller fixes the order.

The state is an `i128` with wrapping addition: it can only lose information after more than 2⁶³ terms.

## 11. Generic code: the `FixedFloat` trait

Sealed: only fulcrum's types implement it. It requires `Copy + Default + Ord + Hash + Debug + Display + FromStr<Err = ParseError>`, all arithmetic operators and their `*Assign` forms.

Contents:
- `type Bits`;
- constants `FRAC_BITS`, `INT_BITS`, `ZERO`, `ONE`, `NEG_ONE`, `HALF`, `MIN`, `MAX`, `DELTA`, `PI`, `TAU`, `FRAC_PI_2`, `E`, `SQRT_2`;
- methods `from_bits`, `to_bits`, `saturating_from_int`, `checked_from_int`, `checked_add/sub/mul/div`, `wrapping_add/sub/mul`, `abs`, `is_negative`, `floor`, `ceil`, `round`, `sqrt`, `hypot`, `lerp`, `sin_cos`, `atan2`, `log2`, `exp2`, `ln`, `exp`, `pow`, `powi`, and the associated type `Angle` (the angle type of the same width, with the trait `FixedAngle`: `from_turns`, `to_turns`, `from_radians`, `to_radians`, `sin`, `cos`, `sin_cos`, `scale`, `from_bits`, `to_bits`, the constants, wrapping `+ - neg` and `* x`).

```rust
use fulcrum::FixedFloat;

fn total<T: FixedFloat>(xs: &[T]) -> T {
    xs.iter().fold(T::ZERO, |a, &b| a + b)
}
```

Everything else (`saturating_*`, `overflowing_*`, `to_int_*`, bytes, accumulators, other constants) exists only as inherent methods of the concrete types (`const` where §15 says so). The trait grows with the stages: `sin_cos` and `atan2` joined in stage 4, `hypot` and `lerp` in stage 5 for the generic vectors, `log2`, `exp2`, `ln`, `exp`, `pow` and `powi` in stage 6.

## 12. `strict-overflow`

For tests and CI of code that uses fulcrum. Never enable it in a shipped build.

With the feature, these panic instead of saturating: the operators `+ - * / %` and their `*Assign` forms, unary `-` of `MIN`, `<<`, `Iterator::sum` and `Iterator::product`. Division and remainder by zero through operators panic too. The explicit methods (`saturating_*`, `wrapping_*`, `checked_*`, `overflowing_*`, `AccumulatorN::finish`) behave the same with and without it. Engine tests catch every unexpected saturation, and the release build keeps deterministic behaviour without panics.

For tests only:

```toml
[dev-dependencies]
fulcrum = { git = "https://github.com/whoiam1101/fulcrum", tag = "v0.6.0", features = ["strict-overflow"] }
```

Cargo unifies features, so under `cargo test` of your crate the feature is enabled for the normal dependency too.

## 13. `float-convert`

`to_f64()`, `checked_from_f64(x)`, `saturating_from_f64(x)`. Both directions work on the IEEE 754 bit pattern with integer operations, so they are exact and deterministic by themselves. `to_f64` is exact while the raw value has at most 53 significant bits (always, for 8 to 32 bits).

Use it for debugging, tests, rendering and loading input data. Once a value has gone through `f64` arithmetic, determinism is lost: never feed `f64` back into simulation logic.

## 14. `serde`, `bytemuck`, `num-traits`

`serde`: human-readable formats (JSON, YAML, TOML) get the exact decimal string of `Display`, so `parse` gives the same bits back: `ff64!(12.5)` is `"12.5"`, `ff64!(0.1)` is `"0.1000000000931322574615478515625"`. They also accept an integer number, converted exactly, and only together with `float-convert` a floating-point number such as `12.6` without quotes, rounded like `checked_from_f64`; without `float-convert` it is an error, so a float never sneaks into the logic. Binary formats (postcard, bincode, CBOR, MessagePack) get the raw integer, encoded as the format encodes the storage integer (`i64` for `FixedFloat64`): 8 fixed bytes in bincode, a varint in postcard.

`bytemuck`: `Pod` and `Zeroable`, so `bytemuck::cast_slice` turns `&[FixedFloat64]` into `&[i64]` or `&[u8]` and back without copying (structure-of-arrays data, buffers for a renderer). The bytes are in native order, like `to_bits().to_ne_bytes()`; for files and the network use `to_le_bytes` (§8).

`num-traits`: `Zero`, `One`, `Bounded`, `Num` and `Signed` with the semantics of the operators: saturating, rounded to nearest. `Num::from_str_radix` accepts only radix 10; `Signed::abs_sub(a, b)` is `max(a - b, 0)`.

## 15. Guarantees

- **Same bits everywhere.** The result of every operation depends only on the input bits: not on the platform, compiler, optimization level or number of threads. Checked by a golden hash on x86-64, ARM64 and i686 in debug and release. A determinism bug is treated as a security issue ([SECURITY.md](SECURITY.md)).
- **No panics** without `strict-overflow`: not on overflow, not on division by zero, not on any input string.
- **Accuracy.** `+ - %`, comparisons, left shift and widening are exact. `* / >>`, `div_int`, `mul_add`, `mul_div`, `lerp`, `sqrt`, `rsqrt`, `hypot`, narrowing, parsing, literals and accumulators are correctly rounded (error ≤ ½ ulp, ties toward `+∞`). Constants are correctly rounded. `sin_turns`, `cos_turns`, `sin`, `cos`, `tan`, `atan`, `atan2`, `asin`, `acos`, `log2`, `exp2`, `ln`, `exp`, `pow` and `powi` are within 1 ulp.
- **`const fn`** almost everywhere: every method of the types except `saturating_from`, `wrapping_from` and the `f64` conversions; on accumulators only `new`, `merge`, `finish` and `checked_finish` are `const`. Operators are not: `core::ops` traits are not `const` in stable Rust.
- **Stability.** The API may change before 1.0. The result bits of existing operations do not: speedups must produce the same bits.

## 16. Common mistakes

- **Chains of `*` are not associative:** `(a * b) * c` may differ from `a * (b * c)` by an ulp. The order of operations is part of deterministic logic; keep it fixed. For sums of products, use `add_product`.
- **`fold` with `+` instead of `sum`** saturates on intermediate values. For a deterministic parallel sum, use only `sum` or accumulators.
- **`>>` rounds** instead of truncating like it does on integers.
- **`round` and `/` break ties differently:** away from zero and toward `+∞`.
- **Narrow types are coarse.** In `FixedFloat8`, `PI == 3.125` and `1/3 ≈ 0.3125`. See the step and range in §2.
- **`parse` does not trim whitespace** and has no exponent: `"1e3"` and `" 1"` are `InvalidDigit`.
- **`f64` in logic** breaks determinism. `float-convert` belongs only at the boundary with the outside world.
