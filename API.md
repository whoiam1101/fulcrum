# fulcrum 0.1: API guide

**English** · [Русский](API.ru.md)

How to use the library: the types, how to create values, what operations do at the edges, how to serialize, and how to write generic code. Describes `v0.1.1`.

## 1. Setup

```toml
[dependencies]
fulcrum = { git = "https://github.com/whoiam1101/fulcrum", tag = "v0.1.1" }
```

The crate is `no_std`, has no dependencies, MSRV 1.60, no `unsafe`. Features (all off by default):

| Feature | What it adds |
|---|---|
| `alloc` | nothing public in 0.1, reserved |
| `std` | `std::error::Error` for `ParseError` and `OverflowError` (enables `alloc`) |
| `float-convert` | `to_f64`, `checked_from_f64`, `saturating_from_f64`, for debugging and rendering |
| `strict-overflow` | operators panic instead of saturating, for tests and CI of an engine only |

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
| `add_product(a, b)` (8, 16, 32 bits) | exact unrounded product |
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

**A dot product** built with `add_product` is rounded once instead of at every term, so it is more accurate and still order-independent. For `FixedFloat32`, `0.1·0.1 + 0.1·0.1` gives `0.0200042724609375` through `add_product` and `0.019989013671875` through `*` and `+`. `Accumulator64` has no `add_product` yet: the exact product of two `i64` at scale `2⁻⁶⁴` does not fit an `i128`. It comes in stage 2 together with `U256`.

**`Iterator::product`** is just `*` in iteration order. Rounded multiplication is not associative, so the caller fixes the order.

The state is an `i128` with wrapping addition: it can only lose information after more than 2⁶³ terms.

## 11. Generic code: the `FixedFloat` trait

Sealed: only fulcrum's types implement it. It requires `Copy + Default + Ord + Hash + Debug + Display + FromStr<Err = ParseError>`, all arithmetic operators and their `*Assign` forms.

Contents:
- `type Bits`;
- constants `FRAC_BITS`, `INT_BITS`, `ZERO`, `ONE`, `NEG_ONE`, `HALF`, `MIN`, `MAX`, `DELTA`, `PI`, `TAU`, `FRAC_PI_2`, `E`, `SQRT_2`;
- methods `from_bits`, `to_bits`, `saturating_from_int`, `checked_from_int`, `checked_add/sub/mul/div`, `wrapping_add/sub/mul`, `abs`, `is_negative`, `floor`, `ceil`, `round`.

```rust
use fulcrum::FixedFloat;

fn total<T: FixedFloat>(xs: &[T]) -> T {
    xs.iter().fold(T::ZERO, |a, &b| a + b)
}
```

Everything else (`saturating_*`, `overflowing_*`, `to_int_*`, bytes, accumulators, other constants) exists only as inherent methods of the concrete types (`const` where §14 says so). The trait grows with the stages: `sqrt` joins in stage 4 and `sin_cos` in stage 5.

## 12. `strict-overflow`

For tests and CI of code that uses fulcrum. Never enable it in a shipped build.

With the feature, these panic instead of saturating: the operators `+ - * / %` and their `*Assign` forms, unary `-` of `MIN`, `<<`, `Iterator::sum` and `Iterator::product`. Division and remainder by zero through operators panic too. The explicit methods (`saturating_*`, `wrapping_*`, `checked_*`, `overflowing_*`, `AccumulatorN::finish`) behave the same with and without it. Engine tests catch every unexpected saturation, and the release build keeps deterministic behaviour without panics.

For tests only:

```toml
[dev-dependencies]
fulcrum = { git = "https://github.com/whoiam1101/fulcrum", tag = "v0.1.1", features = ["strict-overflow"] }
```

Cargo unifies features, so under `cargo test` of your crate the feature is enabled for the normal dependency too.

## 13. `float-convert`

`to_f64()`, `checked_from_f64(x)`, `saturating_from_f64(x)`. Both directions work on the IEEE 754 bit pattern with integer operations, so they are exact and deterministic by themselves. `to_f64` is exact while the raw value has at most 53 significant bits (always, for 8 to 32 bits).

Use it for debugging, tests, rendering and loading input data. Once a value has gone through `f64` arithmetic, determinism is lost: never feed `f64` back into simulation logic.

## 14. Guarantees

- **Same bits everywhere.** The result of every operation depends only on the input bits: not on the platform, compiler, optimization level or number of threads. Checked by a golden hash on x86-64, ARM64 and i686 in debug and release. A determinism bug is treated as a security issue ([SECURITY.md](SECURITY.md)).
- **No panics** without `strict-overflow`: not on overflow, not on division by zero, not on any input string.
- **Accuracy.** `+ - %`, comparisons, left shift and widening are exact. `* / >>`, `div_int`, narrowing, parsing, literals and accumulators are correctly rounded (error ≤ ½ ulp, ties toward `+∞`). Constants are correctly rounded.
- **`const fn`** almost everywhere: every method of the types except `saturating_from`, `wrapping_from` and the `f64` conversions; on accumulators only `new`, `merge`, `finish` and `checked_finish` are `const`. Operators are not: `core::ops` traits are not `const` in stable Rust.
- **Stability.** The API may change before 1.0. The result bits of existing operations do not: speedups must produce the same bits.

## 15. Common mistakes

- **Chains of `*` are not associative:** `(a * b) * c` may differ from `a * (b * c)` by an ulp. The order of operations is part of deterministic logic; keep it fixed. For sums of products, use `add_product`.
- **`fold` with `+` instead of `sum`** saturates on intermediate values. For a deterministic parallel sum, use only `sum` or accumulators.
- **`>>` rounds** instead of truncating like it does on integers.
- **`round` and `/` break ties differently:** away from zero and toward `+∞`.
- **Narrow types are coarse.** In `FixedFloat8`, `PI == 3.125` and `1/3 ≈ 0.3125`. See the step and range in §2.
- **`parse` does not trim whitespace** and has no exponent: `"1e3"` and `" 1"` are `InvalidDigit`.
- **`f64` in logic** breaks determinism. `float-convert` belongs only at the boundary with the outside world.
