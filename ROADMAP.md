# Roadmap

Each stage ends with an annotated tag: stages 1–7 are `v0.n.0`, stage 8 is `v1.0.0`, and each later stage raises the minor version. Fixes, speedups and the "between stages" items raise the patch version. A stage is done only when all of its *Done when* items hold. Speedups never change result bits: every algorithm keeps the rounding rule (to nearest, ties toward `+∞`) and must pass the same exhaustive tests and oracle.

| Stage | What | Version | Status |
|---|---|---|---|
| 1 | Integer core: `FixedFloat8`..`FixedFloat64` | `v0.1.0` | ✅ done |
| 2 | `FixedFloat64` complete: `mul_add`, `mul_div`, `lerp`, `add_product` | `v0.2.0` | ✅ done |
| 3 | `sqrt`, `rsqrt`, `hypot` | `v0.3.0` | ✅ done |
| 4 | Trigonometry and angle types | `v0.4.0` | ✅ done |
| 5 | `Vec2`, `Vec3` | `v0.5.0` | ✅ done |
| 6 | `exp2`, `log2`, `exp`, `ln`, `pow` | `v0.6.0` | ✅ done |
| 7 | Optimizations, vectorized loops | `v0.7.0` | ✅ done |
| 8 | Lean proofs of the kernel and of the error bounds | `v1.0.0` | ✅ done |
| 9 | API review and freeze | `v1.1.0` | ✅ done |
| 10 | Faster Lean build | `v1.2.0` | |
| — | `FixedFloat128`, `FixedFloat256`, only on demand | after `1.0` | deferred |

Widths stop at `FixedFloat64`. Q32.32 holds ±2.1·10⁹ with a step of 2.3·10⁻¹⁰, which covers game worlds, and the accumulators are already exact. Every extra width would repeat the work of every later stage (tables, error bounds, proofs) for a type nobody uses yet, so the wide types wait at the end of the plan until a concrete need appears ([Wide types](#wide-types-on-demand)).

Every new function (stages 2–7) comes with the same set of checks as stage 1: oracle or high-precision reference, edge-case tests, the golden hash extended to it, a fuzz target where it parses or divides, Kani "no panic", and benchmarks against the competitors listed for the stage.

## 1. Integer core ✅ `v0.1.0`

Four types with arithmetic, rounding, conversions, exact parsing and formatting, literals, bytes, up to 23 correctly rounded constants per type and exact accumulators. See the [API guide](API.md).

Verified by: exhaustive tests of every pair for `FixedFloat8` and `FixedFloat16` and of `parse(display(x))` for every `FixedFloat32`, the rational oracle with edge-biased property tests, fuzzing of `parse`, `*`, `/` and formatting, stress and algebra runs, a golden hash on x86-64, ARM64 and 32-bit x86, and Kani on all four widths: `+ - neg abs`, `midpoint`, rounding, `to_int_*`, shifts, parts, bytes, narrowing, `from_int`, and `parse` without panics on strings up to 64 bytes; `*` and `mul_int` on 8..32 bits; `/`, `div_int`, `from_ratio` on 8 bits (16 bits is covered exhaustively); accumulator order independence on 8 bits.

**Done when:** every check above passes in CI (the weekly jobs included), the golden hash is the same on x86-64, ARM64 and 32-bit x86 in debug and release, and the stage 1 debts below are closed. Speed is not part of the condition: speedups do not change result bits and ship as `v0.1.x`.

### Between 1 and 2 (`v0.1.x`)

Stage 1 debts, closed in `v0.1.0`:
- [x] Narrowing with explicit semantics: `saturating_from`, `wrapping_from` from any width.
- [x] `TryFrom<i8 … i128, u8 … u128>` with `OverflowError` for integers that do not fit (`From` exists only where it is lossless).
- [x] `<<` and `>>` by an integer; `>>` rounds like `/`.
- [x] Kani: equality with the specification for `round`, `round_ties_even`, `to_int_*`, shifts, narrowing and `from_int` on all four widths, `mul_int` on 8..32 bits, `div_int` and `from_ratio` on 8 bits (16 bits is covered exhaustively).
- [x] Kani: `parse` never panics on strings up to 64 bytes, for every width.
- [x] Exhaustive `parse(display(x)) = x` for all 2³² values of `FixedFloat32` (weekly CI).
- Moved to stage 2: Kani "no panic" for `*` and `/` of `FixedFloat64` (closed there by plain Kani).

Speed and tooling, closed in `v0.2.0`:
- [x] Benchmark report fails on missing data instead of showing it as "on par".
- [x] Integers (`i32`, `i64`, `i128`) as the lower bound in the benchmarks.
- Open items moved to [Between 2 and 3](#between-2-and-3-v02x).

## 2. `FixedFloat64` complete ✅ `v0.2.0`

Prerequisites (do first, as `v0.1.x`):
- [x] One list of sizes for tests, so adding a width is one line instead of ~15 edits (`tests/common/widths.rs`).
- [x] Kani "no panic" for `*` and `/` of `FixedFloat64`, moved from stage 1: plain Kani converges with the current kernel (`mul_no_panic_64`, `div_no_panic_64`, under 30 s each).
- [x] A public constructor from raw bits with an arbitrary scale: `checked_from_scaled_bits`, `saturating_from_scaled_bits`, `wrapping_from_scaled_bits` on an `i128` raw value.

Deliverables:
- [x] `mul_add` (`self * a + b`, rounded once), `mul_div` (`self * a / b`, no intermediate overflow), `lerp` with `checked_*` variants for all widths. Every exact intermediate fits the next primitive, `i128` for `FixedFloat64` (INTERNALS §3.9).
- [x] `Accumulator64::add_product`, on an internal 256-bit state (`src/wide.rs`, `I256`: add, sub, shift; rounding stays in `kernel`). Where a primitive has the same operation, the method has its name.
- [x] Speed: `mul_div` of `FixedFloat64` takes the magnitudes on 64 bits before the product, 2× faster (26.3 → 13.2 µs per 4096 on x86-64), same bits. A software 128/64 division (`divlu`) was measured and is slower than the `u128` division on x86-64; aarch64 is measured in stage 7.

**Done when:** `mul_add`, `mul_div`, `lerp` and `add_product` equal the oracle on every width, exhaustively on `FixedFloat8`; the golden hash covers them; the Kani "no panic" debt of `FixedFloat64` `*` and `/` is closed; benchmarks are in the README.
**Verified by:** every triple of `FixedFloat8` against the specification, `mul_div` by zero included (`tests/combined.rs`; the Kani harness of 8 bits that repeated it is removed); Kani: `mul_add` and `lerp` against the specification on 16 bits; no panics of `*`, `/`, `mul_add`, `mul_div`, `lerp` on 64 bits; `I256` on full 256-bit operands; one `add_product` of 64 bits against an independent rounding.
**Benchmarks against:** `fixed` (`saturating_mul_add`, `saturating_lerp`, `x * y / z`, sums of saturating products), integers (`i32`, `i64`, `i128`). Integers run the same loops as a reference point. Result on x86-64: faster than `fixed` in 7 of 8 cases; `mul_add` of `FixedFloat64` is 1.12–1.19× slower between runs, the cost of rounding to nearest instead of truncating.

### Between 2 and 3 (`v0.2.x`)

Integrations, optional features, off by default (a build without features has no dependencies and keeps the MSRV), closed in `v0.3.0`:
- [x] `serde`: the raw value in binary formats, the exact decimal string of `Display` in human-readable ones (JSON, YAML); an integer number is accepted exactly, a floating-point number (a YAML or JSON number without quotes arrives as `f64`) only together with `float-convert`.
- [x] `bytemuck`: `Pod` and `Zeroable`, for SoA arrays and passing data to a renderer. Their `unsafe impl` are the only `unsafe` of the crate (`#![deny(unsafe_code)]`, `src/pod.rs`, checked by `tests/source_rules.rs`).
- [x] `num-traits`: `Zero`, `One`, `Bounded`, `Num`, `Signed`.
- [x] CI builds every feature on its own and all together on 1.60 and stable and tests them on stable through their public traits (`integrations/`, a separate workspace); `cargo-deny` covers the optional dependencies.

Speed and tooling, moved to [Between 3 and 4](#between-3-and-4-v03x).

## 3. Square roots ✅ `v0.3.0`

- [x] `sqrt`, `checked_sqrt` (negative input: `sqrt` gives `0`, `checked_sqrt` gives `None`), correctly rounded: integer square root of `raw << N`, then a correction step. Own Newton iteration (`isqrt` from `core` needs Rust 1.84, above the MSRV): a start from a 256-entry table (`k64`: from `k32::isqrt`), a fixed number of steps, then an exact descent, so the result does not depend on the start or the number of steps.
- [x] `rsqrt`, `checked_rsqrt` (`x ≤ 0`: `MAX`, `None`) and `hypot`, `checked_hypot` (no intermediate overflow): correctly rounded, better than the planned ≤ 1 ulp. `rsqrt` is one division and `isqrt`, not a Newton iteration for `1/√x` without division (INTERNALS §3.10).
- [x] `sqrt` in the `FixedFloat` trait.

**Done when:** 100% of `sqrt` results are correctly rounded; `rsqrt` and `hypot` stay within 1 ulp against a high-precision reference. All three are correctly rounded against the oracle (`BigInt::sqrt`) and the accuracy table.
**Verified by:** exhaustive check of all 2³² `FixedFloat32` values for `sqrt` and `rsqrt` and of all 2³² pairs of `hypot` on `FixedFloat16` (`--ignored`, weekly); every value on 8 and 16 bits and every pair of `hypot` on 8 bits in every run; Kani for `isqrt` of the kernel on every 16- and 32-bit argument (`k8`, `k16`: the roots of `FixedFloat8` and `FixedFloat16`; the Kani harness of `sqrt`, `rsqrt`, `hypot` on 8 bits repeated the exhaustive check and is removed); the 64- and 128-bit `isqrt` of `k32` and `k64` does not converge in 30 minutes (symbolic wide division in a loop), so `FixedFloat32` relies on the exhaustive check above and `FixedFloat64` on the oracle, fuzzing and the proof in INTERNALS §3.10; the rational oracle and the `ops` fuzz target on every width; the golden hash. Gappa is not needed: Newton ends with an exact descent, so no error bound of the start or of the steps enters the result. The Gappa and Rocq CI job moved to stage 4, where approximation errors do, and was then replaced by Lean in stage 8.
**Benchmarks against:** `libm` (software float), hardware `f32`/`f64`. Accuracy table (max and mean ulp error, share of correctly rounded results) in the README and `bench/results/`, generated by `bench/src/accuracy.rs`.

### Between 3 and 4 (`v0.3.x`)

Speed and tooling:
- [x] Instruction-count regression gate: `bench/benches/instr.rs` (gungraun) runs on every push to `main` and every PR against the base commit and fails above +1 % instructions (`.github/workflows/perf.yml`).
- Rejected: `rust_decimal` as a competitor; a decimal floating type is chosen for decimal semantics, not as an alternative to binary fixed point (ARCHITECTURE §10).
- Moved to stage 7: `/` on 16 bits, `mul_div` of `FixedFloat64` on aarch64, the `cargo asm` check, square roots without division.

Quality gates:
- [x] `pre-commit` hooks (`.pre-commit-config.yaml`): file hygiene, gitleaks, typos, actionlint, zizmor, rustfmt and clippy on every manifest, the source rules; tests, MSRV build and `cargo deny` before push.
- [x] CI: clippy and rustfmt on every manifest, rustdoc without warnings, typos, Miri on the `unsafe` of `src/pod.rs`, line coverage with a floor, every feature combination (`cargo hack`), semver of each release against the previous tag, weekly mutation testing; actions pinned by commit, gitleaks and zizmor in `security.yml`, Dependabot with a 7-day cooldown.
- [x] CI split between every push and the weekly run: on a push, tests on every width (8 and 16 bits exhaustively, in debug with overflow checks), the oracle and nine quick Kani harnesses outside the kernel (under a minute); weekly, by hand and on a tag, every Kani harness in parallel, the exhaustive `FixedFloat32` runs one job per file with `overflow-checks`, stress (5 + 3 minutes), fuzz, mutants, beta and nightly. Kani harnesses that repeated an exhaustive test are removed; documentation-only changes run `docs.yml` (typos, source rules, doctests) instead of the whole CI.
- [x] `justfile`: one recipe per local check; the local hooks of `pre-commit` and the CI jobs call the recipes; only the CI steps that depend on the runner, the target or a matrix variable (`targets`, `fuzz`, `kani`, the instruction counts of `perf.yml`) call cargo directly.
- Moved to [Between 6 and 7](#between-6-and-7-v06x): coverage of `integrations/`.
- Rejected: Miri on more than `pod.rs`; Miri finds undefined behaviour, which only the `unsafe` of `pod.rs` can cause, and overflow in safe code is caught by the debug tests (ARCHITECTURE §10).

## 4. Trigonometry ✅ `v0.4.0`

- [x] `sin_turns`, `cos_turns` in turns (1.0 = 360°): range reduction is a bit mask, one table of 257 points per quarter circle (`src/tables/trig.rs`, 62 fractional bits) and a short series for the remainder, rounded once (`src/trig.rs`, INTERNALS §3.11). Within 1 ulp with an internal error below `2^-59`; every result of `FixedFloat8`, `FixedFloat16` and `FixedFloat32` is correctly rounded (exhaustive, against a reference whose error bound the oracle samples). `sin(-x) = -sin(x)`, `cos(-x) = cos(x)` and `cos(x) = sin(x + ¼)` bit for bit.
- [x] `sin`, `cos`, `sin_cos`, `tan` (and `checked_tan`) in radians: the magnitude multiplied exactly by 192 bits of `2/π` (a 256-bit product) gives the angle in quarter turns, then the same quarter table; `tan` is the quotient of the quarter's sine and cosine, rounded once, and near a pole the cotangent of the 128-bit distance to it, so it stays within 1 ulp up to saturation (INTERNALS §3.12). Every result of `FixedFloat8`, `FixedFloat16` and `FixedFloat32` is correctly rounded (exhaustive, against a reference that subtracts `k·π/2` instead; the oracle decides 178 `tan` values of `FixedFloat32` within `10⁻⁸` ulp of a midpoint); `sin` and `tan` odd and `cos` even bit for bit.
- [x] `atan`, `atan2`, `asin`, `acos` (and `checked_asin`, `checked_acos`): one `atan(n/d)` of two integers of the same scale, from a table of `atan(k/256)` (257 points, 62 bits) and a short series of the exact remainder `(256n - kd)/(256d + kn)`, so `atan2` never divides its arguments and nothing overflows; `asin` and `acos` are `atan2` of `x` and the exact integer root `√(1 - x²)`. Error below `5·2^-62`, within 1 ulp (INTERNALS §3.13). Every result of `FixedFloat8`, `FixedFloat16` and `FixedFloat32` and every pair of `atan2` on `FixedFloat8` is correctly rounded (exhaustive, against a reference without the table that halves the angle three times); `atan` and `asin` odd bit for bit; `atan2` in the `FixedFloat` trait.
- [x] `Angle8`, `Angle16`, `Angle32`, `Angle64`: an angle as every bit of an unsigned integer, the fraction of a turn, the companion of the fixed-point type of the same width; wrapping `+`, `-`, unary `-`, never saturates; `sin`, `cos`, `sin_cos` within 1 ulp from the same quarter table; `from_turns` exact, `to_turns`, `from_radians`, `to_radians` (the exact value in `[-π, π)`, with a `π` of 126 bits) and `scale` (a rate times a time step) correctly rounded (INTERNALS §3.14). `FixedAngle` trait and `FixedFloat::Angle` for generic code (`Vec2::rotate` of stage 5). Every `sin` and `cos` of `Angle8`, `Angle16` and `Angle32` is correctly rounded (exhaustive); the oracle checks the conversions in radians on every value of 8 and 16 bits.
- [x] Tables generated by `tools/gen-tables` with the interval integer arithmetic of the constants (`num-bigint`, no `astro-float`): an entry is written only when both ends of its interval round the same way. Tables are `const`: no lazy initialization, no caches.
- Moved to stage 8: formal error bounds of the trigonometry (Gappa scripts and their Rocq proofs were planned here), proven in Lean on the code extracted by Aeneas instead.
- [x] `sin_cos` in the `FixedFloat` trait.
- [x] Benchmarks of `sin_turns`, `cos_turns`, `sin`, `cos`, `tan`, `atan`, `atan2`, `asin`, `acos` on `FixedFloat32` and `FixedFloat64` against `libm`, the `std` floats and `cordic` (`bench/benches/ops.rs`), and the accuracy table against the 256-bit oracle (`bench/src/trig_accuracy.rs`): max error and share of correctly rounded results of every implementation, in the README.
- [x] Determinism across platforms: `bench/src/bin/determinism.rs` computes `sin`, `cos`, `tan`, `atan2` of `std` `f64`, `libm` and fulcrum on the same operands on Linux x86-64 and ARM64, macOS and Windows runners, and `bench.yml` puts the count of results that differ from Linux x86-64 into the README on every push.

**Done when:** ≤ 1 ulp on every type against a high-precision reference.
**Verified by:** the error bounds derived in INTERNALS §3.11–3.14 (below `2^-59`, a margin of `2^26` over the `2^-33` that 1 ulp of `FixedFloat64` needs); exhaustive check of every value of 8, 16 and 32 bits for every function, all correctly rounded; the 256-bit interval oracle and fuzzing on every width; "no panic" by the exhaustive checks on 8–32 bits (in release with overflow checks) and the pairs of `atan2` on 16 bits, Kani on the 64-bit `sin_turns`, `cos_turns`, `sin`, `cos`, `tan`, the angle types on 32 and 64 bits and the pairs of `atan2` on 32 bits; `atan` and `atan2` of 64 bits and `asin`, `acos` beyond 32 bits rely on the oracle and fuzzing, where Kani does not converge (INTERNALS §11). The formal proof of the bounds is part of stage 8.
**Benchmarks against:** `libm`, `cordic`; a demonstration that `f64::sin` from `std` differs between x86 and ARM while fulcrum does not.

## 5. Vectors ✅ `v0.5.0`

- [x] `Vec2<T>`, `Vec3<T>` with public fields, `#[repr(C)]`, aliases `Vec2f8` … `Vec2f64`, `Vec3f8` … `Vec3f64` (`src/vec.rs`).
- [x] `new`, `splat`, `ZERO`, `X`/`Y`/`Z`; `+ -`, unary `-`, `*` by a scalar on either side, `/` by a scalar, component-wise `*` of two vectors (an operator, as in `glam`), `min`, `max`, `abs`, `lerp`; all saturate per component like the scalar operators.
- [x] `dot`, `length_sq`, `distance_sq`, `perp_dot`, `cross`: the exact sum of exact products, rounded once (`dot` through the accumulator, `I256` on 64 bits; the 2×2 determinant in the kernel, `det`). `length` and `distance` correctly rounded: `hypot` for `Vec2`, a new kernel `hypot3` for `Vec3`, with the domain of `isqrt` widened to `3 · 2^(2W-2)`.
- [x] `perp` (`Vec2`).
- [x] `normalize`, `try_normalize` (zero vector gives `None`), `clamp_length_max`, `clamp_length` (bounds as in `glam`): each component correctly rounded from the exact squared length, a 256/128-bit division (Knuth's algorithm D, `src/wide.rs`) on 64 bits; there are no ties (INTERNALS §3.15).
- [x] `rotate` by `T::Angle` with a sine and cosine of 62 bits, within 1 ulp below a raw length of `2^57`; `angle_to` (`Vec2` signed, `Vec3` in `[0, π]`) as `atan2` of exact cross and dot products, within 1 ulp.
- [x] `to_le_bytes`, `from_le_bytes`, `to_be_bytes`, `from_be_bytes`; `bytemuck` (`Pod` for vectors of a `Pod` type) and `serde` (a tuple of the components) behind their features.
- [x] API guide (`API.md`, `API.ru.md`), INTERNALS §3.15, README.

**Done when:** every item above is checked, the tests and the oracle pass on every width, and the macro benchmark "one tick" runs: 5 000 units, `pos += vel · dt`, neighbour search by `distance_sq`, `normalize`, turning toward a target with `atan2`; variants `FixedFloat32`, `FixedFloat64`, `fixed`, `f32` with `glam`; results in the README.
**Verified by:**
- the integer reference of `tests/common/reference.rs` (`tests/vec.rs`, `tests/vec_geometry.rs`): every `length` of `Vec2` and `Vec3` on `FixedFloat8`, edge-biased random vectors on every width, `normalize` and `clamp_length` by the definition of rounding, `rotate` and `angle_to` against the independent sine and `atan2` of `tests/common/trig.rs`;
- the rational oracle on every width (`oracle/tests/vec.rs`), including the 64-bit sums beyond `i128` and `clamp_length` with `min > max` and negative bounds; the fuzz target `vec`; a golden hash of the vectors next to the one of the scalars;
- Kani "no panic": the operators, `dot`, `cross`, `perp_dot` and `distance_sq` on every width (`vec_no_panic_*`), `length` and `distance` on 8 bits, `rotate` and `angle_to` of `Vec2` on 8 and 16 bits (`proofs_geometry`, one CI job each), and `isqrt` on the widened domain for `k8` and `k16` (`isqrt_spec_8/16`).

Kani does not converge on the rest. `normalize` and `clamp_length` (the 256-by-128-bit division) exhaust the memory of a CI runner within a minute, `length` of 16 bits and `angle_to` of `Vec3` run past five hours, and every root, `normalize`, `rotate` and `angle_to` of 32 and 64 bits divides `u64` and `u128` in loops (as for `sqrt` in stage 3). Exhaustive tests in release with overflow checks prove "no panic" on their domain instead: `normalize` of every `Vec2` and `Vec3` of `FixedFloat8` and every `Vec2` of `FixedFloat16`, `clamp_length` of every `Vec2` of `FixedFloat8` with every pair of bounds and every `Vec3` with every bound, `angle_to` of every `Vec3` of `FixedFloat8` against the vectors with components in `{MIN, 0, MAX}`. `length` of `Vec2` on 16 bits is `hypot`, checked on every pair, and of `Vec3` the root of an exact sum of squares (`isqrt_spec_16`). Beyond these domains the oracle, fuzzing and the bounds of INTERNALS §3.15 stand in.

**Benchmarks against:** `glam` (`dot`, `length`, `normalize`, `distance_sq`, `rotate`, `angle_to`, `clamp_length` of `Vec2`; `cross`, `length`, `normalize` of `Vec3`), and the "one tick" macro benchmark of `bench/src/tick.rs`, each tick from the same starting state. Result on x86-64: the tick takes 105 ns per unit on `FixedFloat32` and 159 ns on `FixedFloat64`, against 150 and 616 ns for `fixed` `I16F16` and `I32F32` with `cordic` and 52 ns for `glam`; the vector functions are 2–94× slower than `glam` on hardware floats.

Checked before the tag `v0.5.0`:
- [x] Every Kani harness of the stage passes (`vec_no_panic_8/16/32/64`, the five of `proofs_geometry`, `isqrt_spec_8/16`), run outside the developer machine; the exhaustive tests of `tests/vec_geometry.rs` pass with `--ignored` in release with overflow checks.
- [x] The bench workflow puts the vector and tick tables into the README.
- [x] The golden hash of the vectors is the same on x86-64, ARM64 and 32-bit x86 in debug and release.

### Between 5 and 6 (`v0.5.x`)

- Moved to stage 7: the narrower division of `normalize` and `clamp_length` of `FixedFloat32`, `length` and `rotate` against an `isqrt` without division, vector operations in the instruction-count gate.

## 6. Exponentials and logarithms ✅ `v0.6.0`

- [x] `log2`, `checked_log2` (`x ≤ 0`: `MIN`, `None`): the exponent of the argument, `log₂ c` of a table of `log₂(1 + k/256)` (256 points, 62 bits, `src/tables/exp.rs`) at the point just below the mantissa, and three terms of `2·log₂ e · atanh s` of the exact `s = (u - c)/(u + c) < 2^-9`, rounded once; error below `2^-59`, so within `½ + 2^-27` ulp (INTERNALS §3.16).
- [x] `exp2`, `checked_exp2` (saturating to `MAX`): `x = n + t` by a mask, `2^(k/256)` of a table at 126 bits times `e^y` of the remainder, `y < 2^-8.5`, by seven terms at 72 bits, shifted by `n` and rounded once; within `½ + 2^-7.5` ulp on `FixedFloat64`, `½ + 2^-39` up to `FixedFloat32`. Exact on integers `≥ -FRAC_BITS`.
- Every result of `log2` and `exp2` of `FixedFloat8`, `FixedFloat16` and `FixedFloat32` is correctly rounded and both are monotone (exhaustive, against the reference of `tests/common/exp.rs`: the full series without tables, the bound checked by the oracle); the 256-bit interval oracle on every width (`oracle/tests/exp.rs`); the fuzz target `ops`; the golden hash `GOLDEN_EXP`; Kani `exp2_no_panic_64`, `log2_no_panic_64`.
- [x] `ln`, `checked_ln` (`x ≤ 0`: `MIN`, `None`): `(e - f) · ln 2 + log₂ u · ln 2` from the same unrounded 62-bit `log₂ u` as `log2`, summed at 104 bits and rounded once; error below `2^-59.5`, within `½ + 2^-27` ulp, exact at `1`.
- [x] `exp`, `checked_exp` (saturating to `MAX`, `0` from `x ≤ -2·FRAC_BITS`): an exact reduction `x = j · ln 2/256 + y` at 112 bits, `j` from the product with `2·log₂ e` and one correction, then the table `2^(k/256)` and the series of `exp2`; the same bound as `exp2`, exact at `0` (INTERNALS §3.16).
- Every result of `ln` and `exp` of `FixedFloat8`, `FixedFloat16` and `FixedFloat32` is correctly rounded and both are monotone (exhaustive, against `tests/common/exp.rs`: `ln` without the binary logarithm, `exp` reduced by a division by `ln 2` with the full series); the interval oracle on every width (its `exp` is the series of the whole argument, without a reduction); the fuzz target `ops`; `GOLDEN_EXP` extended; Kani `exp_no_panic_64`, `ln_no_panic_64`.
- [x] `pow`, `checked_pow`, `powi`, `checked_powi`: `2^(y · log₂ x)` with a wide `log₂ x` of 120 fractional bits (a 126-bit table of `log₂(1 + k/256)`, `s` at 128 bits, seven terms, error below `1.05 · 2^-120`), the product with `y` exact up to `2^-120`, then the tail of `exp2`; within `½ + 2^-5.7` ulp on `FixedFloat64`, `½ + 2^-37` up to `FixedFloat32`. `x^0 = 1`, `0^(y<0)` saturates, a negative base takes the sign of an odd integer exponent and gives `0`/`None` for a non-integer one; an exact power halfway between two values may round either way (INTERNALS §3.16).
- `pow` and `powi` within 1 ulp, and correctly rounded wherever the reference of `tests/common/exp.rs` decides (not on `FixedFloat64`, where results within `2^-5.7` ulp of a halfway point near `MAX` may round the wrong way); `powi` against exact integer powers on `i128` on 16, 32 and 64 bits: every pair of `FixedFloat8` and (weekly) of `FixedFloat16`, `powi` on every value of 8 and 16 bits, random pairs of 16 and 32 bits; the interval oracle on every width; the fuzz target `ops`; `GOLDEN_EXP` extended; Kani `pow_no_panic_64`.
- [x] `log2`, `exp2`, `ln`, `exp`, `pow`, `powi` in the `FixedFloat` trait (the saturating forms, as `sqrt` and `atan2`).
- [x] Benchmarks of `log2`, `exp2`, `ln`, `exp`, `pow`, `powi` on `FixedFloat32` and `FixedFloat64` against `libm` and the `std` floats, and of `exp` against `cordic`, its only function of the group (`fixed` has only integer logarithms, `int_log2` and `int_log10`; `bench/benches/ops.rs`); the accuracy table against the 256-bit oracle (`bench/src/exp_accuracy.rs`); `exp`, `ln` and `pow` in the determinism table (`bench/src/bin/determinism.rs`). Result on the CI runner (x86-64): 8–12 ns for `log2`, `exp2`, `ln`, `exp`, 1.08–5.7× slower than `libm`, `exp` 1.16× and 10.4× faster than `cordic`; `pow` and `powi` 50–53 ns, 1.5–1.9× slower than `libm`, dominated by the two `u128` divisions of the wide logarithm; fulcrum correctly rounded on every sample of the accuracy table, the floats up to thousands of ulps off (`powi` of `std`: 1148 ulps on `Q16.16`, 6660 on `Q32.32`); `exp`, `ln` and `pow` of fulcrum and `libm` bit for bit the same on Linux ARM64, macOS and Windows, of `std` not.

**Done when:** ≤ 2 ulp on every type against a high-precision reference.
**Verified by:** exhaustive check of all 2³² `FixedFloat32` values for `exp2` and `log2`, the interval oracle, error bounds derived in INTERNALS and proven in Lean in stage 8. Sollya may be used once by hand to choose minimax coefficients: a design tool, not a check.

Checked before the tag `v0.6.0`:
- [x] Every Kani harness of the stage passes in the weekly shard `_64` (`exp2_no_panic_64`, `log2_no_panic_64`, `exp_no_panic_64`, `ln_no_panic_64`, `pow_no_panic_64`), run outside the developer machine; a harness that does not converge is removed and recorded (ARCHITECTURE §10).
- [x] The weekly exhaustive jobs `exp` (every `FixedFloat32` value of the four functions) and `pow` (every pair of `FixedFloat16`) pass in release with overflow checks.
- [x] `GOLDEN_EXP` is the same on x86-64, ARM64 and 32-bit x86 in debug and release.
- [x] The bench workflow puts the speed, accuracy and determinism tables of the stage into the README.
- Moved to stage 7: `pow` without the two `u128` divisions of the wide logarithm (a reciprocal of `u + c` by multiplication, or a table of `1/c`), the gap to `libm` above.

### Between 6 and 7 (`v0.6.x`)

- [x] Coverage of `integrations/` merged into the report (`num.rs` and `serialize.rs` show 0 % today), then raise the floor from 80 % (from [Between 3 and 4](#between-3-and-4-v03x)). `just cov` merges the profiles of both runs with `llvm-cov` of llvm-tools: `num.rs` 91 %, `serialize.rs` 91 %, all of `src` 93.0 % of lines; the floor is 92 % (ARCHITECTURE §10).

## 7. Optimizations ✅ `v0.7.0`

No batch API (`add_assign_slice` and the like): a plain loop over slices is the batch operation, and it vectorizes as well as the scalar code it calls. So the work goes into the scalar code, which every loop of the user, `Vec2` and `Vec3` share. Every item keeps the result bits: the golden hashes and the exhaustive tests do not change.

Vectorized loops:
- [x] `+`, `-`, `*`, `mul_int`, `mul_add`, `lerp` in a loop over slices of `FixedFloat8`, `FixedFloat16` and `FixedFloat32` vectorize on x86-64 (SSE2, AVX2) and aarch64 (NEON), without `unsafe` or intrinsics; where a branch of the kernel blocks it, the kernel is rewritten without the branch. `FixedFloat64` is out of scope: no SIMD set multiplies 64×64 → 128. All of them vectorize on all three, except `*`, `mul_int`, `mul_add`, `lerp` of `FixedFloat32` on SSE2 (no 64-bit compare and no signed 32×32 → 64 multiply) and `mul_int` of `FixedFloat32` on NEON; the rewrites that vectorize them were slower on x86-64 and are rejected (ARCHITECTURE §10).
- [x] Measured on the aarch64 runner, where the x86-64 numbers above decided: `mul_int` of `FixedFloat32` as a wide product and `saturate` (vectorizes on NEON), the `u128` division of `isqrt` of `FixedFloat64`, the two of `log2`/`pow` and the one of `mul_div` against `divlu` (no hardware 128/64 division there). Rejected without the measurement: `src` has no platform code, so each function has one form on every target, and each alternative is slower on x86-64 or no faster; a win on aarch64 alone would not change the choice (ARCHITECTURE §10).
- [x] A check of the assembly (`--emit asm`, `bench/src/bin/asm.rs`) of these loops and of `mul`, `div`, `saturating_add` in CI on x86-64 (the SSE2 baseline and with AVX2 enabled) and on the aarch64 runner (NEON), so that a loss of vectorization on any of the three fails CI (from [Between 3 and 4](#between-3-and-4-v03x)).
- [x] Benchmarks of the loops against the same loops of `fixed` and of `i32`/`i16` without rounding; the loops in the instruction-count gate (`bench/benches/instr.rs`, x86-64), so that a loss of speed fails CI.
- [x] "Arrays" in the API guides (`API.md`, `API.ru.md`): write a plain loop; which widths and operations vectorize, with the numbers of the benchmarks.

Speedups found by the benchmarks of stages 1–6:
- [x] `pow` without the two `u128` divisions of the wide logarithm (a reciprocal of `u + c` by multiplication, or a table of `1/c`); today 50–53 ns, 1.5–1.9× slower than `libm` (from stage 6). Rejected on x86-64: each division is one hardware 128/64 `div`, and with both replaced by a shift (wrong values, the bound of any replacement) `log2` of `FixedFloat64` takes 18.1 ns instead of 18.05 (ARCHITECTURE §10); the 7-term series is the cost.
- [x] Square roots without division: `isqrt` through a Newton iteration for `1/√x` (multiplications only) with the same exact descent; was 5–26 ns, 3.3–16× slower than `libm` (from [Between 3 and 4](#between-3-and-4-v03x)). Done for `FixedFloat32` (`sqrt` 4.65 → 3.68 ns, `rsqrt` 6.96 → 4.94 ns, ARCHITECTURE §10); `FixedFloat64` still takes one `u128` division after the 32-bit start (`sqrt` 17.8 ns): on x86-64 it is one hardware 128/64 `div`, and two 64-bit divisions in its place were slower (ARCHITECTURE §10); rejected for `FixedFloat64`.
- [x] `length` and `rotate` of the vectors measured against the new `isqrt`; `normalize` and `clamp_length` of `FixedFloat32` (41 and 27 ns) with a division narrower than `u128`, the quotient has at most 33 bits (from [Between 5 and 6](#between-5-and-6-v05x)). `length` of `Vec2f32` 5.91 → 5.20 ns with the new `isqrt`; `rotate` takes no root. On 8–32 bits `normalize` and `clamp_length` take one root and one division per vector instead of a 256-bit product, a division and a root per component: `Vec3` `normalize` 1.3–1.4× faster, `clamp_length` 7–22 %, `Vec2f32` `normalize` on par (ARCHITECTURE §10).
- [x] Division: `/` 1.08–1.17× slower than `fixed` on 16 bits and in the latency of 32 bits; `mul_div` of `FixedFloat64` on aarch64, the `u128` division against `divlu` (from [Between 3 and 4](#between-3-and-4-v03x)). The latency of 32 bits is now ahead of `fixed` (4.44 against 5.36 ns); on 16 bits the other two forms of the rounded division were slower than the current one (1.87 ns throughput; `fixed` 1.21, it truncates), rejected (ARCHITECTURE §10); `mul_div` on aarch64 moves to the item of the aarch64 runner.
- [x] Vector operations in the instruction-count gate (from [Between 5 and 6](#between-5-and-6-v05x)).

Speedups found while working on stage 7:
- [x] `lerp` and `det` round as `mul` does, adding the half before the shift on 8–32 bits: loops of `lerp` 7–17 % and `perp_dot` 7–16 % faster (ARCHITECTURE §10).
- [x] `Display` on `u64` with the digits in one buffer: 1.8–3.4× faster (ARCHITECTURE §10).

**Done when:** every item above is done or rejected by a benchmark, with the reason recorded (ARCHITECTURE §10); the loops of the first group vectorize on 8–32 bits, except those of `FixedFloat32` that need an instruction the target lacks (on SSE2 a 64-bit compare and a signed 32×32 → 64 multiply for `*`, `mul_int`, `mul_add`, `lerp`; on NEON the saturating 32-bit multiply of `mul_int`), whose rewrites were slower (ARCHITECTURE §10); the result bits are unchanged.
**Verified by:** the golden hashes on x86-64, ARM64 and 32-bit x86, the exhaustive tests and the oracle on every rewritten function, its Kani harnesses; the instruction-count gate and the README benchmarks for the speed.

Checked before the tag `v0.7.0`:
- [x] The job `vectorization` passes on SSE2, AVX2 and NEON (`ubuntu-24.04-arm`), and the instruction-count gate runs the loops and the vector operations.
- [x] The weekly exhaustive jobs pass in release with overflow checks: `sqrt` and `rsqrt` of every `FixedFloat32`, `hypot` and `normalize` of every pair of 16 bits, `normalize` and `clamp_length` of 8 bits, `parse ∘ Display` of every `FixedFloat32`.
- [x] The Kani harnesses of the kernel pass in the weekly shards, run outside the developer machine; `isqrt_spec_8` and `isqrt_spec_16` cover the starts that did not change, the `rsqrt` start of `k32` and `scale_narrow` are covered by the exhaustive tests above.
- [x] The golden hashes are the same on x86-64, ARM64 and 32-bit x86 in debug and release.
- [x] The job `coverage` passes with the merged report and the floor of 92 %.
- [x] The bench workflow puts the table "Loops over slices" into the README.

## 8. Lean proofs of the kernel and 1.0 ✅ `v1.0.0`

Lean 4 proves `src/kernel.rs`, the one place that owns widths and rounding, and the error bounds of the functions that approximate: trigonometry, exponentials and logarithms. Kani, the oracle, exhaustive tests and fuzzing cover the rest, as in the earlier stages. Lean replaces the Gappa, Sollya and Rocq of the first plan, since it proves the bounds on the code that Aeneas extracts instead of on a model written next to it.

Every theorem below holds on the extracted code. "Never fails" means the extracted function returns a value for every input of its domain, so the Rust code cannot panic there. The math without code lives in `verify/lean/Fulcrum/Math/`, the lemmas shared by every width in `Fulcrum/Lemmas/`, and the derivations in INTERNALS §2–3.16.

- [x] Lean L1, rounding. `kernel::shr_round` never fails and rounds to nearest, ties up, for every `i128` and every shift, including shifts of 128 and more (`Fulcrum/L1/ShrRound.lean`). `magnitude_rounds_up`, the same rule on a sign and a magnitude for parsing and floats, rounds by the first dropped bit and the sticky bits (`Fulcrum/L1/RoundsUp.lean`).
- [x] Lean L2, range. On `k8`..`k64`, `fits` holds exactly for the values in `[MIN, MAX]`, `narrow` returns them, `saturate` clamps and `wrap` wraps in two's complement (`Fulcrum/L2/Narrow.lean`). `to_int` is `⌊w / 2^F⌋` wrapped to the storage type, and `from_parts` is `int · 2^F + frac` (`Fulcrum/L2/Parts.lean`).
- [x] Lean L3, the kernel functions on `k8`..`k64` equal the specification and never fail: `mul`, `mul_add`, `lerp` (`Fulcrum/L3/Mul.lean`, `Lerp.lean`); `mul_div`, `div` and `div_int` in both forms of `div_kernel!`, and `div_total`, which also covers a zero divisor (`Fulcrum/L3/Div/`); `rescale` for scales that differ by less than 128, while every caller differs by at most 32 (`Fulcrum/L3/Rescale.lean`); `isqrt` on its whole domain `n ≤ 3 · 2^(BITS - 2)`, with the `SQRT_START` and `RSQRT_START` tables proven as built (`Fulcrum/L3/Sqrt/`).
- [x] Lean L4, the error bounds of INTERNALS §3.11–3.16 for every `2 ≤ f ≤ 32` at once, since the functions of `src/trig.rs` and `src/exp.rs` take `f` as an argument. Each function never fails and stays within `½ + 2^-27` ulp of the true value unless noted.
  - [x] Extraction: `just extract` starts from `crate::kernel`, `crate::trig` and `crate::exp` and brings the tables of `src/tables/` along; `FunsExternal.lean` adds `i128::unsigned_abs` and `u64`, `u128::wrapping_neg`.
  - [x] Constants and tables: `π` and `ln 2` to `2^-270` (`Fulcrum/Math/Const.lean`), the series of `sin`, `cos`, `arctan`, `log` and `exp` with bounded tails (`Fulcrum/Math/Series.lean`), every entry of `src/tables/trig.rs` and `src/tables/exp.rs` within half a unit (`Fulcrum/Tables/`).
  - [x] Sine and cosine in turns (§3.11): `sin_quarter` within `6.1u` of the sine of the quarter (`Fulcrum/L4/SinQuarter.lean`); `sin_position`, `sin_turns`, `cos_turns` for `f ≤ 62` within `½ + 6.1 · 2^(f - 62)` ulp (`Fulcrum/L4/Turns.lean`).
  - [x] In radians (§3.12): `reduce` is the exact product with 192 bits of `2/π`; `sin`, `cos`, `sin_cos` for `f ≤ 62` within `½ + 6.9 · 2^(f - 62)` ulp (`Fulcrum/L4/Radians.lean`); `tan` for `f ≤ 32` within `½ + 2^f / 10^12` ulp, or the saturation mark `±2^(2f)` when `|tan| ≥ 2^(f+1)` (`Fulcrum/L4/Tan.lean`). The sign of the mark is not proven.
  - [x] Inverse functions (§3.13): `atan_unit` within `2.9u`, `atan_ratio` within `3.4u`; `atan` and `atan2` within `½ + 4 · 2^(f - 62)` ulp, `asin` and `acos` within `½ + 5 · 2^(f - 62)` ulp (`Fulcrum/L4/Atan.lean`).
  - [x] Angle types (§3.14): `angle_sin`, `angle_cos` within `½ + 6.1 · 2^(f - 62)` ulp; `angle_scale` exact; `angle_to_radians` within `½ + (5/4) · 2^(f - n - 61)` ulp; `angle_from_radians` within `½ + (5/4) · 2^(n - 130)` steps (`Fulcrum/L4/Angle.lean`).
  - [x] Vectors (§3.15): `rotate` within `½ + 6.1 · (|x| + |y|) · 2^-62` raw units before saturation; `atan2_wide` and `angle_between2` within `½ + 5 · 2^(f - 62)` ulp, `angle_between3` within `½ + 8 · 2^(f - 62)` ulp (`Fulcrum/L4/Vec.lean`).
  - [x] Logarithms (§3.16): `log2_unit` within `7.6u`; `log2` within `½ + 7.6 · 2^(f - 62)` ulp, `ln` within `½ + 5.6 · 2^(f - 62)` ulp (`Fulcrum/L4/Log.lean`).
  - [x] Exponentials (§3.16): `exp2` returns the saturation mark `2^(2f)` exactly for `⌊x⌋ ≥ f - 1` and `exp` only for `e^x · 2^f ≥ 2^(2f - 1)`; otherwise both are within `½ + 1.4 · 2^(2f - 72)` ulp, `½ + 2^-7.5` at `f = 32` (`Fulcrum/L4/Exp.lean`).
  - [x] Powers (§3.16): `log2_wide` within `1.05W` of `log₂ |x| · 2^120`, `exp2_wide` away from the saturation mark within `½ + 2.2 · 2^(2f - 71)` ulp; `pow` within `½ + 2^-5.8` ulp on `FixedFloat64`, with the edges and the sign of `exp::pow` (`Fulcrum/L4/Pow.lean`).
- [x] Lean L5, the rest of `src/kernel.rs`, so that its Kani harnesses and exhaustive tests could go:
  - [x] `det` is `round((a · d - b · c) / 2^F)` (`Fulcrum/L5/Det.lean`).
  - [x] `midpoint` is `round((a + b) / 2)`, `shr(a, n)` is `round(a / 2^n)` for every `n`, `shl(a, n)` is `a · 2^n` wrapped with the overflow flag (`Fulcrum/L5/Shift.lean`).
  - [x] `ceil`, `round_half_away`, `round_ties_even` round as named (`Fulcrum/L5/Round.lean`).
  - [x] `sqrt` is `round √(a · 2^F)`, `rsqrt` is `round √(2^(3F) / a)`, `hypot` and `hypot3` are the rounded roots of the exact sums of squares, `cmp_length` is the sign of `a² + b² + c² - k²` (`Fulcrum/L5/Length.lean`).
  - [x] `scale_vec` rounds every component to `round(|x| · k / √(a² + b² + c²))` with the sign of `x`, with no ties possible (`Fulcrum/L5/Scale.lean` for `k8`..`k32`, `Scale64.lean` for `k64`, the 256-bit arithmetic of `src/wide.rs` in `Fulcrum/Wide/`).
  - [x] `mul_int` stays outside L5: it is `saturating_mul` and the other integer methods of `core` in `src/define.rs`, like `+` and `-`, and its Kani harness `mul_int_spec_*` stays (ARCHITECTURE §10).
- [x] No axiom of our own, no `sorry`, no `native_decide` or `bv_decide`: `#check_axioms` in `verify/lean/Fulcrum.lean` fails the build unless every declaration uses only `propext`, `Classical.choice` and `Quot.sound`, and `leanchecker` in CI replays every module through the kernel. CI extracts the code again with Charon and Aeneas at the commit pinned in `verify/lean/lake-manifest.json` and fails when the result differs. The only hand-written definitions are the `unsigned_abs` and `wrapping_neg` of `core` (`Kernel/FunsExternal.lean`).
- [x] What L1–L5 prove is not brute-forced again. The Kani harnesses of the kernel and the "no panic" harnesses of `trig.rs` and `exp.rs` that L4 covers are removed, together with the exhaustive tests of the kernel (every pair of 16 bits, `sqrt` and `rsqrt` of every `FixedFloat32`, every pair of `hypot` on `FixedFloat16`). The every-push exhaustive tests of 8 and 16 bits and the sampled tests through the public API stay. Harnesses that also check code outside the kernel keep that part: `add_round_spec_*`, `rem_spec_8`, `narrow_spec_*`, `from_int_spec_*` (ARCHITECTURE §10).
- [x] No publishing to crates.io: `rat` uses the git tag.

**Done when:** L1–L5 are proven, and what they prove is no longer brute-forced. The API review and freeze move to `v1.1.0`.

## 9. API review and freeze ✅ `v1.1.0`

Every public item of `API.md` is reviewed against the engine (`rat`): names, signatures, what is public. After `v1.1.0` the API changes only in a major version.

- [x] The contract of `rat` (`docs/ARCHITECTURE.md` §1.1 of the engine) is covered: the same bits on x86-64 and ARM64, saturation without panics, `sqrt`, `sin`, `cos`, `atan2` without floats, `Vec2` and `Vec3` with `length`, `normalize` and `dot`, bytes and `serde` for snapshots, replays and checksums, `no_std`.
- [x] Names and signatures stay: every public item of the rustdoc of `v1.0.0` was checked against `API.md`, no documented item is renamed or removed, which would take a major version (`cargo semver-checks` in CI, which passes `v1.0.0` → `v1.1.0` as a minor change; it skips `#[doc(hidden)]` items, which are not part of the API). What the engine does not use yet (`serde` and bytes of the angle types, `Send + Sync` on `FixedFloat`, vectors from arrays and between widths) is not added: a minor version adds it when the code of `rat` needs it (ARCHITECTURE §10).
- [x] What is public: the hidden kernels of the generic vectors and of `saturating_from`, `wrapping_from` (`__dot`, `__det`, `__hypot3`, `__scale_to`, `__cmp_length`, `__rotate`, `__angle2`, `__angle3`, `__raw_i128`) move from `FixedFloat` to a private supertrait, and each takes a private token, so no code outside the crate can call them; a `compile_fail` doctest checks it. `__lit` stays hidden and public for the literal macros.
- [x] `API.md` and `API.ru.md` describe `v1.1.0`: `shr_round` as the `const` form of `>>`, the bits of an angle for snapshots, the `const` methods of the vectors, the sealed traits that a minor version may extend, and the freeze in place of "the API may change before 1.0".

**Done when:** the review is done and nothing in the API is expected to change.

## 10. Faster Lean build `v1.2.0`

The `lean` job of CI is the longest check on every push. The proofs stay the same theorems; only how they are built and checked changes.

- CI: what does not change between pushes is cached, and independent checks run in parallel.
- A margin under the heartbeat limit, so that an update of Mathlib or Aeneas does not break a proof that only just fits.
- The slowest proofs, found by the profiler, are made lighter: heavy tactics over a long context give way to direct terms and small lemmas, each change measured.
- The modules are split so that the longest chain of imports gets shorter.

**Done when:** the `lean` job is at least twice as fast as on `v1.0.0`, and every proof keeps a margin under the heartbeat limit.

## Wide types (on demand)

Not planned. Q32.32 covers the game worlds this library is written for, every exact intermediate already lives inside the crate (`i128`, the internal 256-bit integer of `src/wide.rs`), and every extra width would repeat the tables, error bounds, Kani harnesses and Lean proofs of every stage. `FixedFloat128` (Q64.64) or a wider type comes as a minor release after 1.0 only if a concrete user needs more than Q32.32; the tests name what has to grow first (`tests/common/widths.rs`).

## Alongside every stage

- Benchmarks are rerun when the code changes; the workflow commits the regenerated README section and `bench/results/` straight to `main`. Every stage adds its functions and the competitors listed above.
- Bit-identical results on every CI target are a release requirement: a determinism bug is treated as a security issue ([SECURITY.md](SECURITY.md)).
