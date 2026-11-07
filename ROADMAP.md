# Roadmap

Each stage ends with an annotated tag. Stage *n* is tagged `v0.n.0`; fixes, speedups and the "between stages" items are `v0.n.x`. A stage is done only when all of its *Done when* items hold. Speedups never change result bits: every algorithm keeps the rounding rule (to nearest, ties toward `+∞`) and must pass the same exhaustive tests and oracle.

| Stage | What | Version | Status |
|---|---|---|---|
| 1 | Integer core: `FixedFloat8`..`FixedFloat64` | `v0.1.0` | ✅ done |
| 2 | 256-bit integers, `FixedFloat128` | `v0.2.0` | next |
| 3 | 512-bit integers, `FixedFloat256` | `v0.3.0` | |
| 4 | `sqrt`, `rsqrt`, `hypot` | `v0.4.0` | |
| 5 | Trigonometry and `Angle` | `v0.5.0` | |
| 6 | `Vec2`, `Vec3` | `v0.6.0` | |
| 7 | `exp2`, `log2`, `exp`, `ln`, `pow` | `v0.7.0` | |
| 8 | Batch operations, optimizations | `v0.8.0` | |
| 9 | Remaining proofs, API freeze | `v1.0.0` | |

Every new type (stages 2, 3) and every new function (stages 4–8) comes with the same set of checks as stage 1: oracle or high-precision reference, edge-case tests, the golden hash extended to it, a fuzz target where it parses or divides, Kani "no panic", and benchmarks against the competitors listed for the stage.

## 1. Integer core ✅ `v0.1.0`

Four types with arithmetic, rounding, conversions, exact parsing and formatting, literals, bytes, up to 23 correctly rounded constants per type and exact accumulators. See [What is in 0.1](README.md#what-is-in-01).

Verified by: exhaustive tests of every pair for `FixedFloat8` and `FixedFloat16` and of `parse(display(x))` for every `FixedFloat32`, the rational oracle with edge-biased property tests, fuzzing of `parse`, `*`, `/` and formatting, stress and algebra runs, a golden hash on x86-64, ARM64 and 32-bit x86, and Kani on all four widths: `+ - neg abs`, `midpoint`, rounding, `to_int_*`, shifts, parts, bytes, narrowing, `from_int`, and `parse` without panics on strings up to 64 bytes; `*` and `mul_int` on 8..32 bits; `/`, `div_int`, `from_ratio` on 8 bits (16 bits is covered exhaustively); accumulator order independence on 8 bits.

### Between 1 and 2 (`v0.1.x`)

Stage 1 debts, closed in `v0.1.0`:
- [x] Narrowing with explicit semantics: `saturating_from`, `wrapping_from` from any width.
- [x] `TryFrom<i8 … i128, u8 … u128>` with `OverflowError` for integers that do not fit (`From` exists only where it is lossless).
- [x] `<<` and `>>` by an integer; `>>` rounds like `/`.
- [x] Kani: equality with the specification for `round`, `round_ties_even`, `to_int_*`, shifts, narrowing and `from_int` on all four widths, `mul_int` on 8..32 bits, `div_int` and `from_ratio` on 8 bits (16 bits is covered exhaustively).
- [x] Kani: `parse` never panics on strings up to 64 bytes, for every width.
- [x] Exhaustive `parse(display(x)) = x` for all 2³² values of `FixedFloat32` (weekly CI).
- Moved to stage 2: Kani "no panic" for `*` and `/` of `FixedFloat64`; 128-bit multiplication and division do not converge, Lean L3 covers them.

Speed and tooling:
- [ ] Division: `/` is 1.3–2× slower than `fixed` on 16 and 32 bits (see the README benchmarks).
- [ ] Benchmark report fails on missing data instead of showing it as "on par".
- [ ] Instruction-count regression tests (`iai-callgrind`) and an `cargo asm` check of `mul`, `div`, `saturating_add` on x86-64 and aarch64.
- [ ] Competitors that need no new fulcrum code: integers (`i32`, `i64`, `i128`) as the lower bound, `rust_decimal`.

Integrations, optional features, off by default (a build without features has no dependencies and keeps the MSRV):
- [ ] `serde`: the raw value in binary formats, a decimal string such as `"12.6"` in human-readable ones (JSON, YAML); a YAML number without quotes arrives as `f64` and is accepted only together with `float-convert`.
- [ ] `bytemuck`: `Pod` and `Zeroable`, for SoA arrays and passing data to a renderer.
- [ ] `num-traits`: `Zero`, `One`, `Bounded`, `Num`, `Signed`.
- [ ] CI builds and tests every feature on its own and all together, on 1.60 and stable; `cargo-deny` covers the optional dependencies.

## 2. `FixedFloat128` `v0.2.0`

Prerequisites (do first, as `v0.1.x`):
- [ ] One list of sizes for tests, so adding a width is one line instead of ~15 edits.
- [ ] A test reference wider than `i128`: the current one stops at 64 bits. The oracle (`num-rational`) is the reference for 128 and 256 bits.
- [ ] Kani "no panic" for `*` and `/` of `FixedFloat64`, moved from stage 1: through Lean L3 on the kernel, or Kani on a reduced model.
- [ ] A public constructor from raw bits with an arbitrary scale, designed for wide raw values. Until then it stays internal: in 0.1 it took an `i128`, which cannot hold a Q64.64 raw value with a larger scale.

Deliverables:
- `fulcrum::wide::U256`, `I256`, public, with the method names of the primitive integers (`wrapping_add`, `overflowing_mul`, `leading_zeros`, `checked_shl`, …): add, sub, shifts, compare, `mul` 128×128 → 256, `divlu` 256/128 with a fast path for 64-bit divisors.
- `FixedFloat128` (Q64.64, raw `i128`) with the full stage 1 API: kernel `kernel::k128`, `ff128!` literal, 16-byte `to_le_bytes`/`to_be_bytes`, `From`/`TryFrom` with every smaller width, all constants.
- `Accumulator128`: its exact state needs more than `i128`.
- `mul_add`, `mul_div`, `lerp` for all widths (they need `U256` for `FixedFloat64`).
- `Accumulator64::add_product`.

**Done when:** property tests of `wide` against `num-bigint` and of `FixedFloat128` against the oracle pass; the stage 1 suites (edge, stress, algebra, golden hash, fuzz) run on `FixedFloat128`.
**Verified by:** Kani for `wide` (add, sub, shifts, compare against bitwise specification; `mul` against the sum of partial products) and for `divlu` on a reduced model (`u8`/`u16` limbs); Kani "no panic" for `FixedFloat128` except division; Aeneas set up on `kernel`; Lean L3 (`kernel` multiplication equals the specification) and L4 (`U256`/`U512` arithmetic equals arithmetic in ℕ).
**Benchmarks against:** `fixed` `I64F64`; `ethnum` and `bnum` for `wide`.

## 3. `FixedFloat256` `v0.3.0`

- `wide::U512`, Knuth's algorithm D (384/256 division).
- `FixedFloat256` (Q128.128, raw `I256`) with the full API, `ff256!`, 32-byte serialization, `Accumulator256`.
- `parse` and `Display` on wide magnitudes: today they work on `u128`, which does not hold a Q128.128 value.
- Multiplication 256×256 → 512 by the school method; Karatsuba only if a benchmark shows a gain.
- Trigonometry later needs Q128.128 too: the CORDIC fallback of stage 5 is chosen by benchmark.

**Done when:** same as stage 2, for 256 bits.
**Verified by:** Kani for `U512` and Knuth D on a reduced model; Lean L5 (`divlu` and Knuth D: quotient and remainder are correct, `q̂` is corrected at most twice).
**Benchmarks against:** `ethnum`, `bnum`; division cost is documented.

## 4. Square roots `v0.4.0`

- `sqrt`, `checked_sqrt` (negative input: `sqrt` gives `0`, `checked_sqrt` gives `None`), correctly rounded: integer square root of `raw << N`, then a correction step. Own Newton iteration with a `leading_zeros` start (`isqrt` from `core` needs Rust 1.84, above the MSRV); on `wide` for 128 and 256 bits.
- `rsqrt` (Newton for `1/√x`, no division) and `hypot` (no intermediate overflow), ≤ 1 ulp.
- `sqrt` in the `FixedFloat` trait.

**Done when:** 100% of `sqrt` results are correctly rounded; `rsqrt` and `hypot` stay within 1 ulp against a high-precision reference.
**Verified by:** exhaustive check of all 2³² `FixedFloat32` values for `sqrt` and `rsqrt`; Gappa for the start estimate and the number of Newton steps; Lean L6 (`isqrt` terminates and equals `Nat.sqrt`). A CI job checks the Rocq proofs produced by Gappa when `verify/gappa`, `src/tables` or `tools/gen-tables` change, and weekly; it is used again in stages 5 and 7.
**Benchmarks against:** `libm` (software float), hardware `f32`/`f64`. Accuracy table (max and mean ulp error, share of correctly rounded results) in `bench/results/`.

## 5. Trigonometry `v0.5.0`

- `sin`, `cos`, `sin_cos`, `tan` in radians; `sin_turns`, `cos_turns` in turns (1.0 = 360°), where range reduction is a bit mask.
- `atan`, `atan2`, `asin`, `acos`.
- `Angle`: turns with wrapping addition, never saturates.
- Table of 256 points per quarter circle plus a short series; tables and coefficients generated by `tools/gen-tables` (switches to `astro-float`), which also generates the Gappa scripts. Tables are `const` or immutable `static`: no lazy initialization, no caches.
- CORDIC as a fallback for Q128.128 if the table is slower.
- `sin_cos` in the `FixedFloat` trait.

**Done when:** ≤ 1 ulp on every type against a high-precision reference.
**Verified by:** Sollya and Gappa error bounds for `sin`, `cos`, `atan` on every size; exhaustive check of all 2³² `FixedFloat32` values for `sin`, `cos`, `sin_turns`.
**Benchmarks against:** `libm`, `cordic`; a demonstration that `f64::sin` from `std` differs between x86 and ARM while fulcrum does not.

## 6. Vectors `v0.6.0`

- `Vec2<T: FixedFloat>`, `Vec3<T: FixedFloat>`, `#[repr(C)]`, aliases `Vec2f32`, `Vec2f64`, …
- `new`, `ZERO`, `X`/`Y`/`Z`; `+ -`, `*` and `/` by a scalar; component-wise `mul`, `min`, `max`, `abs`; `dot`, `cross` (`Vec3`), `perp_dot` and `perp` (`Vec2`); `length`, `length_sq`, `distance`, `distance_sq`; `normalize`, `try_normalize` (zero vector gives `None`); `lerp`, `rotate`, `angle_to`, `clamp_length`; `to_le_bytes`.
- `dot` and `length_sq` in the wide type, rounded once.

**Done when:** tests pass and the macro benchmark "one tick" runs: 5 000 units, `pos += vel · dt`, neighbour search by `distance_sq`, `normalize`, turning toward a target with `atan2`; variants `FixedFloat32`, `FixedFloat64`, `FixedFloat128`, `fixed`, `f32` with `glam`.
**Verified by:** Kani, no panics.
**Benchmarks against:** `glam`.

## 7. Exponentials and logarithms `v0.7.0`

- `exp2`, `log2`, `exp`, `ln`, `powi`, `pow`.

**Done when:** ≤ 2 ulp on every type against a high-precision reference.
**Verified by:** Sollya and Gappa; exhaustive check of all 2³² `FixedFloat32` values for `exp2` and `log2`.

## 8. Batch operations `v0.8.0`

- `fulcrum::batch`: `add_assign_slice`, `mul_scalar_slice`, `fma_slice` for SoA arrays, written for auto-vectorization (SSE, AVX2, NEON) without `unsafe` or intrinsics; only if benchmarks show a gain.
- Optimizations found by the benchmarks of stages 1–7.

**Done when:** the gain is confirmed by benchmarks.
**Verified by:** Kani, `batch` is bit-identical to the scalar functions.

## 9. Proofs and 1.0 `v1.0.0`

- Lean L1: the specification in Lean (with Mathlib), and "shift right by N after adding `2^(N-1)` equals rounding to nearest, ties up" for every N.
- Lean L2: checking the high bits ⇔ the result is outside `[MIN, MAX]`, for every width.
- Lean L7 (optional): `parse(display(x)) = x`.
- API review and freeze; decide on publishing to crates.io.

**Done when:** L1 and L2 are proven and nothing in the API is expected to change.

## Alongside every stage

- Benchmarks are rerun when the code changes; the README section is regenerated by a pull request. Every stage adds its functions and the competitors listed above.
- Bit-identical results on every CI target are a release requirement: a determinism bug is treated as a security issue ([SECURITY.md](SECURITY.md)).
