# Roadmap

Each stage ends with an annotated tag. Stage *n* is tagged `v0.n.0`; fixes, speedups and the "between stages" items are `v0.n.x`. A stage is done only when all of its *Done when* items hold. Speedups never change result bits: every algorithm keeps the rounding rule (to nearest, ties toward `+∞`) and must pass the same exhaustive tests and oracle.

| Stage | What | Version | Status |
|---|---|---|---|
| 1 | Integer core: `FixedFloat8`..`FixedFloat64` | `v0.1.0` | ✅ done |
| 2 | `FixedFloat64` complete: `mul_add`, `mul_div`, `lerp`, `add_product` | `v0.2.0` | ✅ done |
| 3 | `sqrt`, `rsqrt`, `hypot` | `v0.3.0` | ✅ done |
| 4 | Trigonometry and `Angle` | `v0.4.0` | in progress |
| 5 | `Vec2`, `Vec3` | `v0.5.0` | |
| 6 | `exp2`, `log2`, `exp`, `ln`, `pow` | `v0.6.0` | |
| 7 | Batch operations, optimizations | `v0.7.0` | |
| 8 | Lean proofs of the kernel, API freeze | `v1.0.0` | |
| — | `FixedFloat128`, `FixedFloat256`, only on demand | after `1.0` | deferred |

Widths stop at `FixedFloat64` until 1.0. Q32.32 holds ±2.1·10⁹ with a step of 2.3·10⁻¹⁰, which covers game worlds, and the accumulators are already exact. Every extra width would repeat the work of every later stage (tables, error bounds, proofs) for a type nobody uses yet, so the wide types wait at the end of the plan until a concrete need appears ([Wide types](#wide-types-on-demand)).

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
- [x] `Accumulator64::add_product`, on an internal 256-bit state (`src/wide.rs`, `I256`: add, sub, shift; rounding stays in `kernel`). Where a primitive has the same operation, the method has its name ([Wide types](#wide-types-on-demand)).
- [x] Speed: `mul_div` of `FixedFloat64` takes the magnitudes on 64 bits before the product, 2× faster (26.3 → 13.2 µs per 4096 on x86-64), same bits. A software 128/64 division (`divlu`) was measured and is slower than the `u128` division on x86-64; aarch64 is not measured yet (below).

**Done when:** `mul_add`, `mul_div`, `lerp` and `add_product` equal the oracle on every width, exhaustively on `FixedFloat8`; the golden hash covers them; the Kani "no panic" debt of `FixedFloat64` `*` and `/` is closed; benchmarks are in the README.
**Verified by:** Kani: `mul_add`, `mul_div`, `lerp` against the specification on 8 bits, `mul_add` and `lerp` on 16 bits; no panics of `*`, `/`, `mul_add`, `mul_div`, `lerp` on 64 bits; `I256` on full 256-bit operands; one `add_product` of 64 bits against an independent rounding.
**Benchmarks against:** `fixed` (`saturating_mul_add`, `saturating_lerp`, `x * y / z`, sums of saturating products), integers (`i32`, `i64`, `i128`). Integers run the same loops as a reference point. Result on x86-64: faster than `fixed` in 7 of 8 cases; `mul_add` of `FixedFloat64` is 1.12–1.19× slower between runs, the cost of rounding to nearest instead of truncating.

### Between 2 and 3 (`v0.2.x`)

Speed and tooling:
Integrations, optional features, off by default (a build without features has no dependencies and keeps the MSRV), closed in `v0.3.0`:
- [x] `serde`: the raw value in binary formats, the exact decimal string of `Display` in human-readable ones (JSON, YAML); an integer number is accepted exactly, a floating-point number (a YAML or JSON number without quotes arrives as `f64`) only together with `float-convert`.
- [x] `bytemuck`: `Pod` and `Zeroable`, for SoA arrays and passing data to a renderer. The two `unsafe impl` are the only `unsafe` of the crate (`#![deny(unsafe_code)]`, `src/pod.rs`, checked by `tests/source_rules.rs`).
- [x] `num-traits`: `Zero`, `One`, `Bounded`, `Num`, `Signed`.
- [x] CI builds every feature on its own and all together on 1.60 and stable and tests them on stable through their public traits (`integrations/`, a separate workspace); `cargo-deny` covers the optional dependencies.

Speed and tooling, moved to [Between 3 and 4](#between-3-and-4-v03x).

## 3. Square roots ✅ `v0.3.0`

- [x] `sqrt`, `checked_sqrt` (negative input: `sqrt` gives `0`, `checked_sqrt` gives `None`), correctly rounded: integer square root of `raw << N`, then a correction step. Own Newton iteration (`isqrt` from `core` needs Rust 1.84, above the MSRV): a start from a 256-entry table (`k64`: from `k32::isqrt`), a fixed number of steps, then an exact descent, so the result does not depend on the start or the number of steps.
- [x] `rsqrt`, `checked_rsqrt` (`x ≤ 0`: `MAX`, `None`) and `hypot`, `checked_hypot` (no intermediate overflow): correctly rounded, better than the planned ≤ 1 ulp. `rsqrt` is one division and `isqrt`, not a Newton iteration for `1/√x` without division (INTERNALS §3.10).
- [x] `sqrt` in the `FixedFloat` trait.

**Done when:** 100% of `sqrt` results are correctly rounded; `rsqrt` and `hypot` stay within 1 ulp against a high-precision reference. All three are correctly rounded against the oracle (`BigInt::sqrt`) and the accuracy table.
**Verified by:** exhaustive check of all 2³² `FixedFloat32` values for `sqrt` and `rsqrt` and of all 2³² pairs of `hypot` on `FixedFloat16` (`--ignored`, weekly); every value on 8 and 16 bits and every pair of `hypot` on 8 bits in every run; Kani for `isqrt` of the kernel on every 16- and 32-bit argument (`k8`, `k16`: the roots of `FixedFloat8` and `FixedFloat16`) and for `sqrt`, `rsqrt`, `hypot` against the definition of rounding on 8 bits; the 64- and 128-bit `isqrt` of `k32` and `k64` does not converge in 30 minutes (symbolic wide division in a loop), so `FixedFloat32` relies on the exhaustive check above and `FixedFloat64` on the oracle, fuzzing and the proof in INTERNALS §3.10; the rational oracle and the `ops` fuzz target on every width; the golden hash. Gappa is not needed: Newton ends with an exact descent, so no error bound of the start or of the steps enters the result. The Gappa and Rocq CI job moves to stage 4, where approximation errors do.
**Benchmarks against:** `libm` (software float), hardware `f32`/`f64`. Accuracy table (max and mean ulp error, share of correctly rounded results) in the README and `bench/results/`, generated by `bench/src/accuracy.rs`.

### Between 3 and 4 (`v0.3.x`)

Speed and tooling:
- [ ] Division: `/` is 1.08–1.17× slower than `fixed` on 16 bits and in the latency of 32 bits (README benchmarks, x86-64).
- [ ] `mul_div` of `FixedFloat64` on aarch64: measure the `u128` division against `divlu`, which has no hardware 128/64 instruction to compete with there.
- [x] Instruction-count regression gate: `bench/benches/instr.rs` (gungraun) runs on every push to `main` and every PR against the base commit and fails above +1 % instructions (`.github/workflows/perf.yml`).
- [ ] A `cargo asm` check of `mul`, `div`, `saturating_add` on x86-64 and aarch64.
- [ ] `rust_decimal` as a competitor.

Quality gates:
- [x] `pre-commit` hooks (`.pre-commit-config.yaml`): file hygiene, gitleaks, typos, actionlint, zizmor, rustfmt and clippy on every manifest, the source rules; tests, MSRV build and `cargo deny` before push.
- [x] CI: clippy and rustfmt on every manifest, rustdoc without warnings, typos, Miri on the `unsafe` of `src/pod.rs`, line coverage with a floor, every feature combination (`cargo hack`), semver of each release against the previous tag, weekly mutation testing; actions pinned by commit, gitleaks and zizmor in `security.yml`, Dependabot with a 7-day cooldown.
- [x] CI split between every push and the weekly run: on a push, tests on every width (8 and 16 bits exhaustively, in debug with overflow checks), the oracle and nine quick Kani harnesses outside the kernel (under a minute); weekly, by hand and on a tag, every Kani harness in parallel, the exhaustive `FixedFloat32` runs one job per file with `overflow-checks`, stress (5 + 3 minutes), fuzz, mutants, beta and nightly. Kani harnesses that repeated an exhaustive test are removed; documentation-only changes run `docs.yml` (typos, source rules, doctests) instead of the whole CI.
- [x] `justfile`: one recipe per local check; the local hooks of `pre-commit` and the CI jobs `lint`, `msrv`, `powerset`, `miri`, `coverage`, `mutants` call the recipes. The CI `test` matrix (it runs on Windows) and the `audit.yml` matrix (one cargo-deny job per manifest) keep their own lists.
- [ ] Coverage of `integrations/` merged into the report (`num.rs` and `serialize.rs` show 0 % today), then raise the floor from 80 %.
- [ ] Miri on more than `pod.rs`: the edge tests take over 30 minutes under Miri, they need a reduced input set first.
- [ ] Square roots without division: `isqrt` through a Newton iteration for `1/√x` (multiplications only) with the same exact descent, so the bits stay the same. Today the roots take 5–26 ns, 3.3–16× slower than `libm` (README); the dependent hardware divisions of `k32::isqrt` and the one `u128` division of `k64` are the cost.

## 4. Trigonometry `v0.4.0`

- [x] `sin_turns`, `cos_turns` in turns (1.0 = 360°): range reduction is a bit mask, one table of 257 points per quarter circle (`src/tables/trig.rs`, 62 fractional bits) and a short series for the remainder, rounded once (`src/trig.rs`, INTERNALS §3.11). Within 1 ulp with an internal error below `2^-59`; every result of `FixedFloat8`, `FixedFloat16` and `FixedFloat32` is correctly rounded (exhaustive, against a reference whose error bound the oracle samples). `sin(-x) = -sin(x)`, `cos(-x) = cos(x)` and `cos(x) = sin(x + ¼)` bit for bit.
- [x] `sin`, `cos`, `sin_cos`, `tan` (and `checked_tan`) in radians: the magnitude multiplied exactly by 192 bits of `2/π` (a 256-bit product) gives the angle in quarter turns, then the same quarter table; `tan` is the quotient of the quarter's sine and cosine, rounded once, and near a pole the cotangent of the 128-bit distance to it, so it stays within 1 ulp up to saturation (INTERNALS §3.12). Every result of `FixedFloat8`, `FixedFloat16` and `FixedFloat32` is correctly rounded (exhaustive, against a reference that subtracts `k·π/2` instead; the oracle decides 178 `tan` values of `FixedFloat32` within `10⁻⁸` ulp of a midpoint); `sin` and `tan` odd and `cos` even bit for bit.
- [x] `atan`, `atan2`, `asin`, `acos` (and `checked_asin`, `checked_acos`): one `atan(n/d)` of two integers of the same scale, from a table of `atan(k/256)` (257 points, 62 bits) and a short series of the exact remainder `(256n - kd)/(256d + kn)`, so `atan2` never divides its arguments and nothing overflows; `asin` and `acos` are `atan2` of `x` and the exact integer root `√(1 - x²)`. Error below `5·2^-62`, within 1 ulp (INTERNALS §3.13). Every result of `FixedFloat8`, `FixedFloat16` and `FixedFloat32` and every pair of `atan2` on `FixedFloat8` is correctly rounded (exhaustive, against a reference without the table that halves the angle three times); `atan` and `asin` odd bit for bit; `atan2` in the `FixedFloat` trait.
- [x] `Angle8`, `Angle16`, `Angle32`, `Angle64`: an angle as every bit of an unsigned integer, the fraction of a turn, the companion of the fixed-point type of the same width; wrapping `+`, `-`, unary `-`, never saturates; `sin`, `cos`, `sin_cos` within 1 ulp from the same quarter table; `from_turns` exact, `to_turns`, `from_radians`, `to_radians` (in `[-π, π)`, with a `π` of 126 bits) and `scale` (a rate times a time step) correctly rounded (INTERNALS §3.14). `FixedAngle` trait and `FixedFloat::Angle` for generic code (`Vec2::rotate` of stage 5). Every `sin` and `cos` of `Angle8`, `Angle16` and `Angle32` is correctly rounded (exhaustive); the oracle checks the conversions in radians on every value of 8 and 16 bits.
- [x] Tables generated by `tools/gen-tables` with the interval integer arithmetic of the constants (`num-bigint`, no `astro-float`): an entry is written only when both ends of its interval round the same way. Tables are `const`: no lazy initialization, no caches.
- [ ] Gappa scripts generated by `tools/gen-tables` from the same description as the tables.
- [x] `sin_cos` in the `FixedFloat` trait.
- [ ] Benchmarks of `sin_turns`, `cos_turns` and the accuracy table.

**Done when:** ≤ 1 ulp on every type against a high-precision reference.
**Verified by:** Sollya and Gappa error bounds for `sin`, `cos`, `atan` on every size; exhaustive check of all 2³² `FixedFloat32` values for `sin`, `cos`, `sin_turns`. A CI job checks the Rocq proofs produced by Gappa when `verify/gappa`, `src/tables` or `tools/gen-tables` change, and weekly; it is used again in stage 6 (moved from stage 3, where Newton's exact descent needs no error bound).
**Benchmarks against:** `libm`, `cordic`; a demonstration that `f64::sin` from `std` differs between x86 and ARM while fulcrum does not.

## 5. Vectors `v0.5.0`

- `Vec2<T: FixedFloat>`, `Vec3<T: FixedFloat>`, `#[repr(C)]`, aliases `Vec2f32`, `Vec2f64`, …
- `new`, `ZERO`, `X`/`Y`/`Z`; `+ -`, `*` and `/` by a scalar; component-wise `mul`, `min`, `max`, `abs`; `dot`, `cross` (`Vec3`), `perp_dot` and `perp` (`Vec2`); `length`, `length_sq`, `distance`, `distance_sq`; `normalize`, `try_normalize` (zero vector gives `None`); `lerp`, `rotate`, `angle_to`, `clamp_length`; `to_le_bytes`.
- `dot` and `length_sq` in the wide type, rounded once (the accumulator with `add_product`).

**Done when:** tests pass and the macro benchmark "one tick" runs: 5 000 units, `pos += vel · dt`, neighbour search by `distance_sq`, `normalize`, turning toward a target with `atan2`; variants `FixedFloat32`, `FixedFloat64`, `fixed`, `f32` with `glam`.
**Verified by:** Kani, no panics.
**Benchmarks against:** `glam`.

## 6. Exponentials and logarithms `v0.6.0`

- `exp2`, `log2`, `exp`, `ln`, `powi`, `pow`.

**Done when:** ≤ 2 ulp on every type against a high-precision reference.
**Verified by:** Sollya and Gappa; exhaustive check of all 2³² `FixedFloat32` values for `exp2` and `log2`.

## 7. Batch operations `v0.7.0`

- `fulcrum::batch`: `add_assign_slice`, `mul_scalar_slice`, `fma_slice` for SoA arrays, written for auto-vectorization (SSE, AVX2, NEON) without `unsafe` or intrinsics; only if benchmarks show a gain.
- Optimizations found by the benchmarks of stages 1–6.

**Done when:** the gain is confirmed by benchmarks.
**Verified by:** Kani, `batch` is bit-identical to the scalar functions.

## 8. Lean proofs of the kernel and 1.0 `v1.0.0`

Lean 4 is the last step and covers only `src/kernel.rs`: the one place that owns widths and rounding. Everything else is checked by Kani, the oracle, exhaustive tests and fuzzing, as in the earlier stages.

- Lean L1: the specification in Lean (with Mathlib), and "shift right by N after adding `2^(N-1)` equals rounding to nearest, ties up" for every N (`shr_round`).
- Lean L2: checking the high bits ⇔ the result is outside `[MIN, MAX]`, for every width (`fits`, `narrow`, `saturate`).
- Lean L3: the kernel functions extracted by Aeneas (`mul`, `div`, `div_int`, `mul_add`, `mul_div`, `lerp`, `rescale`, and the integer square root if it lives in the kernel) equal the specification.
- What L1–L3 prove is not brute-forced again: the Kani harnesses of the kernel (`mul_spec_*`, `div_spec_8`, `ratio_and_div_int_spec_8`, `mul_int_spec_*`, `combined_no_div_spec_16`, `mul_no_panic_64`, `div_no_panic_64`, `rounding_spec_*`, `add_round_spec_*`, `shift_spec_*`, `narrow_spec_*`, `from_int_spec_*`, `isqrt_spec_*`) and its exhaustive tests (every pair of 16 bits in `tests/exhaustive.rs`, `sqrt` and `rsqrt` of every `FixedFloat32`, every pair of `hypot` on `FixedFloat16`) are removed; sampled integration tests through the public API stay. Until then they run weekly only, not on every push (INTERNALS §11).
- API review and freeze; decide on publishing to crates.io.

**Done when:** L1–L3 are proven and nothing in the API is expected to change.

## Wide types (on demand)

Not planned: done only if a concrete user needs more than Q32.32, as a minor release after 1.0. The game engine this library is written for keeps world coordinates in `FixedFloat64`.

- `FixedFloat128` (Q64.64, raw `i128`) and `FixedFloat256` (Q128.128, raw `I256`) with the full API: kernels, `ff128!`/`ff256!`, 16- and 32-byte serialization, `From`/`TryFrom` with every smaller width, all constants, `Accumulator128`/`Accumulator256`.
- `fulcrum::wide` made public: `U256`, `I256`, `U512`, Knuth's algorithm D (384/256 division); school multiplication 256×256 → 512, Karatsuba only if a benchmark shows a gain.
- `parse` and `Display` on wide magnitudes: today they work on `u128`, which does not hold a Q128.128 value.
- Every function of stages 2–6 on the new widths: Newton `sqrt` on `wide`, longer trigonometry series (CORDIC for Q128.128 if the table is slower), new tables and Gappa bounds.
- Tests: `reference!` of `tests/common/reference.rs` instantiated over an integer wider than `i128`, or the oracle where the tests cannot hold one (today `Pcg32::edge_bits` returns `i64` and `Widest` in `tests/consts.rs` is `FixedFloat64`); the oracle (`num-rational`) is the reference for 128 and 256 bits; the stage 1 suites (edge, stress, algebra, golden hash, fuzz) on the new widths.

**Verified by:** Kani "no panic" except division; Kani for `U512` and Knuth D on a reduced model (`u8`/`u16` limbs); property tests against `num-bigint`.
**Benchmarks against:** `fixed` `I64F64`; `ethnum`, `bnum` for `wide`.

## Alongside every stage

- Benchmarks are rerun when the code changes; the workflow commits the regenerated README section and `bench/results/` straight to `main`. Every stage adds its functions and the competitors listed above.
- Bit-identical results on every CI target are a release requirement: a determinism bug is treated as a security issue ([SECURITY.md](SECURITY.md)).
