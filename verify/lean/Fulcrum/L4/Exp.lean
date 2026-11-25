module

public import Fulcrum.L4.Log
public import Fulcrum.Math.Exp

/-!
# L4: `exp::expm1`, `exp_unit`, `exp2_unit`, `round_mantissa`, `exp2`, `exp` (INTERNALS §3.16)

On the code extracted by Aeneas, with `1 ≤ f ≤ 32`.

- `expm1(y)` of `y ≤ 2^64 - 2^57` is `expm1N y` of `Math/Exp.lean`, within `1.6` units of
  `(e^(y / 2^72) - 1) · 2^72`.
- `exp_unit(k, y)` of `k < 256`, `y ≤ ⌊LN_2 / 2^40⌋` adds to the entry `k` of `EXP2` the
  products of its halves with `expm1`: within `0.81 · 2^56` of `2^(k/256) · e^(y / 2^72) · 2^126`,
  at most `2^127 - 2^55` (the last entry and the largest `y`, evaluated by the kernel).
- `exp2_unit(k, b, f)` takes `y = ⌊b · LN_2 / 2^(f + 32)⌋`, within `2^-72 + 2^-113` of
  `b / 2^f · ln 2`: within `1.4 · 2^56` of `2^(k/256 + b/2^f) · 2^126`.
- `round_mantissa` is one `shr_round` by `min (126 - f - n) 128`; `mantissa_round_near` turns
  a mantissa within `1.4 · 2^56` into a result within `½ + 1.4 · 2^(2f) / 2^72`.
- `exp2` splits `raw = n · 2^f + t` by a shift and a mask and returns the mark `2^(2f)` for
  `n ≥ f - 1`; otherwise it is within `½ + 1.4 · 2^(2f) / 2^72` of `2^(raw / 2^f) · 2^f`.
- `exp` returns the mark from `raw ≥ f · 2^f` and `0` from `raw ≤ -2f · 2^f`; `j` is within
  `1` of `raw · 2^(112 - f) / LN_2` because `TWO_LOG2_E · LN_2 - 2^167` is small, so one
  correction gives the exact `y = raw · 2^(112 - f) - j · LN_2 ∈ [0, LN_2)`, `y / 2^112` within
  `2^-97` of `x - j · ln 2 / 256`. The mark comes only with `e^x · 2^f ≥ 2^(2f - 1)`
  (`LN_2 ≥ ln 2 · 2^104`); otherwise the result is within `½ + 1.4 · 2^(2f) / 2^72` of
  `e^x · 2^f`.
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace Fulcrum

set_option maxRecDepth 10000

/-- `exp::EXPM1_FRAC` is `72`. -/
theorem expm1_frac_val : fulcrum.exp.EXPM1_FRAC.val = 72 := by
  unfold fulcrum.exp.EXPM1_FRAC; rfl

/-- A division of a `u128` by a non-zero literal. -/
theorem u128_div_spec (x y : Std.U128) (d : ℕ) (hy : y.val = d) (hd : 0 < d) :
    (x / y) ⦃ r => r.val = x.val / d ⦄ := by
  obtain ⟨z, hz, hv⟩ := UScalar.div_spec x (y := y) (by omega)
  rw [hz, WP.spec_ok, hv, hy]

/-- `exp::ONE_64` is `2^64`. -/
theorem one_64_spec : fulcrum.exp.ONE_64 ⦃ r => r.val = 2 ^ 64 ⦄ := by
  unfold fulcrum.exp.ONE_64
  exact WP.spec_mono (shl_i32_spec 1#u128 64#i32 64 rfl (by rw [UScalarTy.U128_numBits_eq]; norm_num)
    (by rw [UScalarTy.U128_numBits_eq, lit_val]; norm_num)) fun r hr => by rw [hr, lit_val, one_mul]

/-- A Horner step of `exp::expm1` on the code: `c + ⌊y · g / 2^72⌋` of `u128` values with
`y, g < 2^64` and `c ≤ 2^64`; stated for any continuation `k`. -/
theorem horner_spec {α} (y g c : Std.U128) (hy : y.val < 2 ^ 64) (hg : g.val < 2 ^ 64) (hc : c.val ≤ 2 ^ 64)
    (k : Std.U128 → Result α) (P : α → Prop)
    (hk : ∀ r : Std.U128, r.val = c.val + y.val * g.val / 2 ^ 72 → k r ⦃ P ⦄) :
    (do
      let i ← y * g
      let j ← i >>> fulcrum.exp.EXPM1_FRAC
      let r ← c + j
      k r) ⦃ P ⦄ := by
  refine WP.spec_bind (UScalar.mul_spec (x := y) (y := g) (by
    rw [U128_max_val]
    calc y.val * g.val ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
      _ ≤ 2 ^ 128 - 1 := by norm_num)) fun i hi => ?_
  refine WP.spec_bind (UScalar.ShiftRight_spec i fulcrum.exp.EXPM1_FRAC
    (by rw [expm1_frac_val, UScalarTy.U128_numBits_eq]; norm_num)) fun j ⟨hj, _⟩ => ?_
  rw [expm1_frac_val, Nat.shiftRight_eq_div_pow, hi] at hj
  have jl : j.val ≤ 2 ^ 64 := by
    rw [hj]; exact Nat.div_le_of_le_mul ((Nat.mul_le_mul hy.le hg.le).trans (by norm_num))
  refine WP.spec_bind (UScalar.add_spec (x := c) (y := j) (by rw [U128_max_val]; omega)) fun r hr => ?_
  exact hk r (by rw [hr, hj])

/-- L4 on the code: `exp::expm1(y)` of `y ≤ 2^64 - 2^57` never fails and is `expm1N y`. -/
theorem expm1_spec (y : Std.U64) (hy : y.val ≤ 2 ^ 64 - 2 ^ 57) :
    fulcrum.exp.expm1 y ⦃ r => r.val = expm1N y.val ⦄ := by
  unfold fulcrum.exp.expm1
  rw [lift, bind_ok]
  have yv := cast_u128_val y
  generalize UScalar.cast .U128 y = y1 at yv ⊢
  have y64 : y1.val < 2 ^ 64 := by omega
  have y72 : y.val ≤ 2 ^ 72 := by omega
  refine WP.spec_bind one_64_spec fun i hi => ?_
  refine WP.spec_bind (u128_div_spec i 720#u128 720 (lit_val _ (by decide)) (by norm_num)) fun i1 h1 => ?_
  refine WP.spec_bind (u128_div_spec i 5040#u128 5040 (lit_val _ (by decide)) (by norm_num)) fun i2 h2 => ?_
  rw [hi] at h1 h2
  have ch : 2 ^ 64 / 2 + (2 ^ 64 / 6 + (2 ^ 64 / 24 + (2 ^ 64 / 120 + (2 ^ 64 / 720 + 2 ^ 64 / 5040)))) <
      2 ^ 64 := by norm_num
  have hs := horner_step_le
  refine horner_spec y1 i2 i1 y64 (by rw [h2]; omega) (by rw [h1]; omega) _ _ fun g hg => ?_
  rw [h1, h2, yv] at hg
  have gl : g.val ≤ 2 ^ 64 / 720 + 2 ^ 64 / 5040 := hg ▸ hs _ _ _ y72
  refine WP.spec_bind (u128_div_spec i 120#u128 120 (lit_val _ (by decide)) (by norm_num)) fun i5 h5 => ?_
  rw [hi] at h5
  refine horner_spec y1 g i5 y64 (by omega) (by rw [h5]; omega) _ _ fun g1 hg1 => ?_
  rw [h5, yv] at hg1
  have g1l : g1.val ≤ 2 ^ 64 / 120 + (2 ^ 64 / 720 + 2 ^ 64 / 5040) :=
    hg1 ▸ (hs _ _ _ y72).trans (Nat.add_le_add_left gl _)
  refine WP.spec_bind (u128_div_spec i 24#u128 24 (lit_val _ (by decide)) (by norm_num)) fun i8 h8 => ?_
  rw [hi] at h8
  refine horner_spec y1 g1 i8 y64 (by omega) (by rw [h8]; omega) _ _ fun g2 hg2 => ?_
  rw [h8, yv] at hg2
  have g2l : g2.val ≤ 2 ^ 64 / 24 + (2 ^ 64 / 120 + (2 ^ 64 / 720 + 2 ^ 64 / 5040)) :=
    hg2 ▸ (hs _ _ _ y72).trans (Nat.add_le_add_left g1l _)
  refine WP.spec_bind (u128_div_spec i 6#u128 6 (lit_val _ (by decide)) (by norm_num)) fun i11 h11 => ?_
  rw [hi] at h11
  refine horner_spec y1 g2 i11 y64 (by omega) (by rw [h11]; omega) _ _ fun g3 hg3 => ?_
  rw [h11, yv] at hg3
  have g3l : g3.val ≤ 2 ^ 64 / 6 + (2 ^ 64 / 24 + (2 ^ 64 / 120 + (2 ^ 64 / 720 + 2 ^ 64 / 5040))) :=
    hg3 ▸ (hs _ _ _ y72).trans (Nat.add_le_add_left g2l _)
  refine WP.spec_bind (u128_div_spec i 2#u128 2 (lit_val _ (by decide)) (by norm_num)) fun i14 h14 => ?_
  rw [hi] at h14
  refine horner_spec y1 g3 i14 y64 (by omega) (by rw [h14]; omega) _ _ fun h hh => ?_
  rw [h14, yv] at hh
  have hl : h.val < 2 ^ 64 := by
    have := hh ▸ (hs _ _ _ y72).trans (Nat.add_le_add_left g3l _)
    omega
  refine WP.spec_bind (UScalar.mul_spec (x := y1) (y := y1) (by
    rw [U128_max_val]
    calc y1.val * y1.val ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
      _ ≤ 2 ^ 128 - 1 := by norm_num)) fun i17 h17 => ?_
  refine WP.spec_bind (UScalar.ShiftRight_spec i17 fulcrum.exp.EXPM1_FRAC
    (by rw [expm1_frac_val, UScalarTy.U128_numBits_eq]; norm_num)) fun z ⟨hz, _⟩ => ?_
  rw [expm1_frac_val, Nat.shiftRight_eq_div_pow, h17, yv] at hz
  have zl : z.val ≤ 2 ^ 56 := by
    rw [hz]; exact Nat.div_le_of_le_mul ((Nat.mul_le_mul (by omega : y.val ≤ 2 ^ 64) (by omega : y.val ≤ 2 ^ 64)).trans
      (by norm_num))
  refine WP.spec_bind (UScalar.mul_spec (x := z) (y := h) (by
    rw [U128_max_val]
    calc z.val * h.val ≤ 2 ^ 56 * 2 ^ 64 := Nat.mul_le_mul zl hl.le
      _ ≤ 2 ^ 128 - 1 := by norm_num)) fun i18 h18 => ?_
  refine WP.spec_bind (shr_i32_spec i18 64#i32 64 rfl (by rw [UScalarTy.U128_numBits_eq]; norm_num)) fun i19 h19 => ?_
  rw [h18] at h19
  have val : y.val + i19.val = expm1N y.val := by
    rw [h19, hz, hh, hg3, hg2, hg1, hg]; rfl
  have ⟨_, up⟩ := expm1_series_near y.val (by omega)
  refine WP.spec_bind (UScalar.add_spec (x := y1) (y := i19) (by rw [U128_max_val]; omega)) fun r hr => ?_
  rw [WP.spec_ok, cast_u64_val, hr, yv, val, Nat.mod_eq_of_lt (by omega)]

/-- Every entry of `EXP2` is at most the last one. -/
theorem exp2_le_last (k : ℕ) (hk : k < 256) :
    (fulcrum.tables.exp.EXP2.val[k]!).val ≤ (fulcrum.tables.exp.EXP2.val[255]!).val := by
  have all : ∀ k : ℕ, k < 256 →
      (fulcrum.tables.exp.EXP2.val[k]!).val ≤ (fulcrum.tables.exp.EXP2.val[255]!).val := by decide +kernel
  exact all k hk

/-- The mantissa of the largest entry of `EXP2` and the largest `expm1` stays below
`2^127 - 2^55`. -/
theorem exp2_last_top :
    (fulcrum.tables.exp.EXP2.val[255]!).val + (fulcrum.tables.exp.EXP2.val[255]!).val *
      expm1N (fulcrum.tables.exp.LN_2.val / 2 ^ 40) / 2 ^ 72 ≤ 2 ^ 127 - 2 ^ 55 := by
  rw [ln_2_val]; unfold expm1N; decide +kernel

/-- An entry `k < 256` of `EXP2`, read by `index_usize`: within `½` of
`2^(k/256) · 2^126`, and at most the last entry. -/
theorem exp2_table_spec (i : Std.Usize) (hi : i.val < 256) :
    Array.index_usize fulcrum.tables.exp.EXP2 i ⦃ x =>
      |(x.val : ℝ) - (2 : ℝ) ^ ((i.val : ℝ) / 256) * 2 ^ 126| ≤ 1 / 2 ∧
        x.val ≤ (fulcrum.tables.exp.EXP2.val[255]!).val ⦄ := by
  have hl : i.val < fulcrum.tables.exp.EXP2.length := by
    rw [Array.length, fulcrum.tables.exp.EXP2.property]; exact hi
  refine WP.spec_mono (Array.index_usize_spec _ i hl) fun x hx => ?_
  have e := exp2_entry i.val hi
  have m := exp2_le_last i.val hi
  rw [getElem!_pos fulcrum.tables.exp.EXP2.val i.val
    (show i.val < fulcrum.tables.exp.EXP2.val.length from hl), ← hx] at e m
  exact ⟨e, m⟩

/-- L4 on the code: `exp::exp_unit(k, y)` of `k < 256`, `y ≤ ⌊LN_2 / 2^40⌋` (`y / 2^72` below
`ln 2 / 256`) never fails and is within `0.81 · 2^56` of `2^(k/256) · e^(y / 2^72) · 2^126`,
at most `2^127 - 2^55`. -/
theorem exp_unit_spec (k y : Std.U64) (hk : k.val < 256) (hy : y.val ≤ fulcrum.tables.exp.LN_2.val / 2 ^ 40) :
    fulcrum.exp.exp_unit k y ⦃ m =>
      |(m.val : ℝ) - (2 : ℝ) ^ ((k.val : ℝ) / 256) * Real.exp (y.val / 2 ^ 72) * 2 ^ 126| ≤ 81 / 100 * 2 ^ 56 ∧
        m.val ≤ 2 ^ 127 - 2 ^ 55 ⦄ := by
  have n128 : UScalarTy.U128.numBits = 128 := rfl
  have yM : y.val ≤ 12786308645202655659 := by rw [ln_2_val] at hy; exact hy
  unfold fulcrum.exp.exp_unit
  rw [lift, bind_ok]
  have ck := usize_cast_val k (by omega)
  refine WP.spec_bind (exp2_table_spec _ (by rw [ck]; exact hk)) fun t ⟨ht, tM⟩ => ?_
  rw [ck] at ht
  have top := exp2_last_top
  have tl : t.val < 2 ^ 127 := by
    have := Nat.le_add_right (fulcrum.tables.exp.EXP2.val[255]!).val
      ((fulcrum.tables.exp.EXP2.val[255]!).val * expm1N (fulcrum.tables.exp.LN_2.val / 2 ^ 40) / 2 ^ 72)
    omega
  by_cases y0 : y = 0#u64
  · rw [ite_eq_left y0, WP.spec_ok]
    have yv : y.val = 0 := by rw [y0]; rfl
    rw [yv, Nat.cast_zero, zero_div, Real.exp_zero, mul_one]
    refine ⟨ht.trans (by norm_num), by omega⟩
  rw [ite_eq_right y0]
  refine WP.spec_bind (expm1_spec y (by omega)) fun i1 h1 => ?_
  rw [lift, bind_ok]
  have ev := cast_u128_val i1
  generalize UScalar.cast .U128 i1 = e at ev ⊢
  rw [h1] at ev
  have ⟨near, eup⟩ := expm1_series_near y.val (by omega)
  have el : e.val < 2 ^ 64 := by omega
  refine WP.spec_bind (shr_i32_spec t 64#i32 64 rfl (by rw [n128]; norm_num)) fun i2 h2 => ?_
  have i2l : i2.val < 2 ^ 63 := by rw [h2, Nat.div_lt_iff_lt_mul (by positivity)]; omega
  refine WP.spec_bind (UScalar.mul_spec (x := i2) (y := e) (by
    rw [U128_max_val]
    calc i2.val * e.val ≤ 2 ^ 63 * 2 ^ 64 := Nat.mul_le_mul i2l.le el.le
      _ ≤ 2 ^ 128 - 1 := by norm_num)) fun i3 h3 => ?_
  refine WP.spec_bind (UScalar.sub_spec (x := fulcrum.exp.EXPM1_FRAC) (y := 64#u32)
    (by rw [expm1_frac_val, lit_val]; norm_num)) fun i4 ⟨h4, _⟩ => ?_
  rw [expm1_frac_val, lit_val] at h4
  refine WP.spec_bind (UScalar.ShiftRight_spec i3 i4 (by rw [h4, n128]; norm_num)) fun i5 ⟨h5, _⟩ => ?_
  rw [h4, Nat.shiftRight_eq_div_pow, h3, h2] at h5
  set E : ℝ := Real.exp (y.val / 2 ^ 72) - 1 with hE
  have Y0 : (0 : ℝ) ≤ y.val / 2 ^ 72 := by positivity
  have Y1 : (y.val : ℝ) / 2 ^ 72 ≤ 1 / 2 ^ 8 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (y.val : ℝ) ≤ 12786308645202655659 := by exact_mod_cast yM
    linarith
  have E0 : 0 ≤ E := by rw [hE]; linarith [Real.add_one_le_exp ((y.val : ℝ) / 2 ^ 72)]
  have E1 : E ≤ 1 := by
    have := Real.abs_exp_sub_one_le (x := (y.val : ℝ) / 2 ^ 72) (by rw [abs_of_nonneg Y0]; linarith)
    rw [abs_of_nonneg Y0] at this
    have := (abs_le.mp this).2
    rw [hE]; linarith
  have ⟨mn, mup⟩ := exp_unit_near t.val e.val _ E ht (by rw [ev]; exact near) tl E0 E1
  have mtop : t.val + t.val / 2 ^ 64 * e.val / 2 ^ 8 + t.val % 2 ^ 64 * e.val / 2 ^ 72 ≤ 2 ^ 127 - 2 ^ 55 := by
    refine mup.trans (le_trans ?_ top)
    refine Nat.add_le_add tM (Nat.div_le_div_right (Nat.mul_le_mul tM ?_))
    rw [ev]; exact expm1N_mono _ _ hy
  refine WP.spec_bind (UScalar.add_spec (x := t) (y := i5) (by rw [U128_max_val, h5]; omega)) fun i6 h6 => ?_
  rw [lift, bind_ok, lift, bind_ok]
  have i8v : (UScalar.cast .U128 (UScalar.cast .U64 t)).val = t.val % 2 ^ 64 := by
    rw [cast_u128_val, cast_u64_val]
  generalize UScalar.cast .U128 (UScalar.cast .U64 t) = i8 at i8v ⊢
  refine WP.spec_bind (UScalar.mul_spec (x := i8) (y := e) (by
    rw [U128_max_val]
    calc i8.val * e.val ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by rw [i8v]; omega) (by omega)
      _ ≤ 2 ^ 128 - 1 := by norm_num)) fun i9 h9 => ?_
  refine WP.spec_bind (UScalar.ShiftRight_spec i9 fulcrum.exp.EXPM1_FRAC
    (by rw [expm1_frac_val, n128]; norm_num)) fun i10 ⟨h10, _⟩ => ?_
  rw [expm1_frac_val, Nat.shiftRight_eq_div_pow, h9, i8v] at h10
  refine WP.spec_mono (UScalar.add_spec (x := i6) (y := i10) (by rw [U128_max_val, h6, h5, h10]; omega))
    fun m hm => ?_
  have mv : m.val = t.val + t.val / 2 ^ 64 * e.val / 2 ^ 8 + t.val % 2 ^ 64 * e.val / 2 ^ 72 := by
    rw [hm, h6, h5, h10]
  rw [mv]
  refine ⟨?_, mtop⟩
  rw [show (2 : ℝ) ^ ((k.val : ℝ) / 256) * Real.exp (y.val / 2 ^ 72) * 2 ^ 126 =
    (2 : ℝ) ^ ((k.val : ℝ) / 256) * 2 ^ 126 * (1 + E) by rw [hE]; ring]
  exact mn

/-- `e^A` against `e^B` for `|A - B| ≤ d ≤ 2^-60`: within `(1 + 2^-60) · d · e^B`. -/
theorem exp_shift_near (A B d : ℝ) (h : |A - B| ≤ d) (hd : d ≤ 1 / 2 ^ 60) :
    |Real.exp A - Real.exp B| ≤ Real.exp B * ((1 + 1 / 2 ^ 60) * d) := by
  have d0 : 0 ≤ d := (abs_nonneg _).trans h
  have h1 : |A - B| ≤ 1 := h.trans (hd.trans (by norm_num))
  have q := Real.abs_exp_sub_one_sub_id_le h1
  rw [show Real.exp A - Real.exp B = Real.exp B * (Real.exp (A - B) - 1) by
    rw [mul_sub, ← Real.exp_add, add_sub_cancel, mul_one], abs_mul, abs_of_pos (Real.exp_pos _)]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  have sq : (A - B) ^ 2 ≤ d * (1 / 2 ^ 60) := by
    rw [← sq_abs, sq]; exact mul_le_mul h (h.trans hd) (abs_nonneg _) d0
  calc |Real.exp (A - B) - 1| ≤ |Real.exp (A - B) - 1 - (A - B)| + |A - B| := by
        have := abs_add_le (Real.exp (A - B) - 1 - (A - B)) (A - B)
        rwa [sub_add_cancel] at this
    _ ≤ (A - B) ^ 2 + d := add_le_add q h
    _ ≤ (1 + 1 / 2 ^ 60) * d := by nlinarith

/-- L4 on the code: `exp::exp2_unit(k, b, f)` of `k < 256`, `b · 2^8 < 2^f`, `f ≤ 32` never
fails and is within `1.4 · 2^56` of `2^(k/256 + b/2^f) · 2^126`, at most `2^127 - 2^55`. -/
theorem exp2_unit_spec (k b : Std.U64) (f : Std.U32) (hk : k.val < 256) (hb : b.val * 2 ^ 8 < 2 ^ f.val)
    (hf : f.val ≤ 32) :
    fulcrum.exp.exp2_unit k b f ⦃ m =>
      |(m.val : ℝ) - (2 : ℝ) ^ ((k.val : ℝ) / 256 + b.val / 2 ^ f.val) * 2 ^ 126| ≤ 14 / 10 * 2 ^ 56 ∧
        m.val ≤ 2 ^ 127 - 2 ^ 55 ⦄ := by
  have n128 : UScalarTy.U128.numBits = 128 := rfl
  unfold fulcrum.exp.exp2_unit
  rw [lift, bind_ok]
  have bl : b.val < 2 ^ 24 := by
    have : 2 ^ f.val ≤ 2 ^ 32 := Nat.pow_le_pow_right two_pos hf
    omega
  have L := ln_2_val
  refine WP.spec_bind (UScalar.mul_spec (x := UScalar.cast .U128 b) (y := fulcrum.tables.exp.LN_2) (by
    rw [cast_u128_val, U128_max_val, L]
    calc b.val * 14058695031733113177892216608772 ≤ 2 ^ 24 * 14058695031733113177892216608772 :=
          Nat.mul_le_mul_right _ bl.le
      _ ≤ 2 ^ 128 - 1 := by norm_num)) fun i1 h1 => ?_
  rw [cast_u128_val] at h1
  refine WP.spec_bind (UScalar.add_spec (x := f) (y := fulcrum.tables.exp.LN_2_FRAC)
    (by rw [ln_2_frac_val, U32_max_val]; omega)) fun i2 h2 => ?_
  rw [ln_2_frac_val] at h2
  refine WP.spec_bind (UScalar.sub_spec (x := i2) (y := fulcrum.exp.EXPM1_FRAC)
    (by rw [expm1_frac_val, h2]; omega)) fun i3 ⟨h3, _⟩ => ?_
  rw [expm1_frac_val, h2] at h3
  refine WP.spec_bind (UScalar.ShiftRight_spec i1 i3 (by rw [h3, n128]; omega)) fun i4 ⟨h4, _⟩ => ?_
  rw [Nat.shiftRight_eq_div_pow, h1, h3, show f.val + 104 - 72 = f.val + 32 by omega] at h4
  have Lp : (0 : ℝ) < fulcrum.tables.exp.LN_2.val := by rw [L]; norm_num
  have yr : (i4.val : ℝ) ≤ b.val * fulcrum.tables.exp.LN_2.val / 2 ^ (f.val + 32) ∧
      (b.val : ℝ) * fulcrum.tables.exp.LN_2.val / 2 ^ (f.val + 32) < i4.val + 1 := by
    have ⟨a, c⟩ := floor_div_near (b.val * fulcrum.tables.exp.LN_2.val) (2 ^ (f.val + 32)) (by positivity)
    rw [← h4] at a c; push_cast at a c; exact ⟨a, by linarith⟩
  have bf : (b.val : ℝ) * 2 ^ 8 / 2 ^ f.val < 1 := by
    rw [div_lt_one (by positivity)]; exact_mod_cast hb
  have ylim : i4.val ≤ fulcrum.tables.exp.LN_2.val / 2 ^ 40 := by
    rw [Nat.le_div_iff_mul_le (by positivity)]
    have : (i4.val : ℝ) * 2 ^ 40 ≤ fulcrum.tables.exp.LN_2.val := by
      have e : (b.val : ℝ) * fulcrum.tables.exp.LN_2.val / 2 ^ (f.val + 32) * 2 ^ 40 =
          b.val * 2 ^ 8 / 2 ^ f.val * fulcrum.tables.exp.LN_2.val := by
        rw [pow_add]; field_simp
      calc (i4.val : ℝ) * 2 ^ 40 ≤ b.val * fulcrum.tables.exp.LN_2.val / 2 ^ (f.val + 32) * 2 ^ 40 :=
            mul_le_mul_of_nonneg_right yr.1 (by positivity)
        _ ≤ 1 * fulcrum.tables.exp.LN_2.val := by
            rw [e]; exact mul_le_mul_of_nonneg_right bf.le Lp.le
        _ = _ := one_mul _
    exact_mod_cast this
  rw [lift, bind_ok]
  have yv : (UScalar.cast .U64 i4).val = i4.val := by
    rw [cast_u64_val, Nat.mod_eq_of_lt (lt_of_le_of_lt ylim (by rw [L]; norm_num))]
  refine WP.spec_mono (exp_unit_spec k _ hk (yv ▸ ylim)) fun m ⟨mn, mtop⟩ => ⟨?_, mtop⟩
  rw [yv] at mn
  set A : ℝ := (i4.val : ℝ) / 2 ^ 72
  set B : ℝ := Real.log 2 * (b.val / 2 ^ f.val)
  have l0 := log_two_ge'
  have l1 := log_two_le'
  have dAB : |A - B| ≤ 1 / 2 ^ 72 + 1 / 2 ^ 113 := by
    have eL := ln_2_entry
    have mid : |(b.val : ℝ) * fulcrum.tables.exp.LN_2.val / 2 ^ (f.val + 32) / 2 ^ 72 - B| ≤ 1 / 2 ^ 113 := by
      rw [show (b.val : ℝ) * fulcrum.tables.exp.LN_2.val / 2 ^ (f.val + 32) / 2 ^ 72 - B =
        b.val * 2 ^ 8 / 2 ^ f.val * (((fulcrum.tables.exp.LN_2.val : ℝ) - Real.log 2 * 2 ^ 104) / 2 ^ 112) by
          simp only [B]; rw [pow_add]; field_simp, abs_mul,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ b.val * 2 ^ 8 / 2 ^ f.val), abs_div,
        abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 112)]
      calc (b.val : ℝ) * 2 ^ 8 / 2 ^ f.val * (|(fulcrum.tables.exp.LN_2.val : ℝ) - Real.log 2 * 2 ^ 104| / 2 ^ 112)
          ≤ 1 * ((1 / 2) / 2 ^ 112) := mul_le_mul bf.le (div_le_div_of_nonneg_right eL (by positivity))
            (by positivity) zero_le_one
        _ = 1 / 2 ^ 113 := by norm_num
    have fl : |A - (b.val : ℝ) * fulcrum.tables.exp.LN_2.val / 2 ^ (f.val + 32) / 2 ^ 72| ≤ 1 / 2 ^ 72 := by
      simp only [A]
      rw [← sub_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 72)]
      exact div_le_div_of_nonneg_right (abs_le.mpr ⟨by linarith [yr.2], by linarith [yr.1]⟩) (by positivity)
    calc |A - B| ≤ |A - (b.val : ℝ) * fulcrum.tables.exp.LN_2.val / 2 ^ (f.val + 32) / 2 ^ 72| +
          |(b.val : ℝ) * fulcrum.tables.exp.LN_2.val / 2 ^ (f.val + 32) / 2 ^ 72 - B| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add fl mid
  have es := exp_shift_near A B _ dAB (by norm_num)
  have tgt : (2 : ℝ) ^ ((k.val : ℝ) / 256 + b.val / 2 ^ f.val) = (2 : ℝ) ^ ((k.val : ℝ) / 256) * Real.exp B := by
    rw [Real.rpow_add two_pos, Real.rpow_def_of_pos two_pos (b.val / 2 ^ f.val)]
  have top : (2 : ℝ) ^ ((k.val : ℝ) / 256) * Real.exp B ≤ 2 := by
    rw [← tgt]
    have : (k.val : ℝ) / 256 + b.val / 2 ^ f.val ≤ 1 := by
      have : (k.val : ℝ) ≤ 255 := by exact_mod_cast Nat.le_of_lt_succ hk
      have : (b.val : ℝ) / 2 ^ f.val ≤ 1 / 256 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith [(div_lt_one (by positivity)).mp bf]
      linarith
    calc (2 : ℝ) ^ ((k.val : ℝ) / 256 + b.val / 2 ^ f.val) ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le one_le_two this
      _ = 2 := Real.rpow_one 2
  rw [tgt]
  have T0 : (0 : ℝ) ≤ (2 : ℝ) ^ ((k.val : ℝ) / 256) := by positivity
  calc |(m.val : ℝ) - (2 : ℝ) ^ ((k.val : ℝ) / 256) * Real.exp B * 2 ^ 126|
      ≤ |(m.val : ℝ) - (2 : ℝ) ^ ((k.val : ℝ) / 256) * Real.exp A * 2 ^ 126| +
        |(2 : ℝ) ^ ((k.val : ℝ) / 256) * 2 ^ 126 * (Real.exp A - Real.exp B)| := by
        rw [show (m.val : ℝ) - (2 : ℝ) ^ ((k.val : ℝ) / 256) * Real.exp B * 2 ^ 126 =
          ((m.val : ℝ) - (2 : ℝ) ^ ((k.val : ℝ) / 256) * Real.exp A * 2 ^ 126) +
            (2 : ℝ) ^ ((k.val : ℝ) / 256) * 2 ^ 126 * (Real.exp A - Real.exp B) by ring]
        exact abs_add_le _ _
    _ ≤ 81 / 100 * 2 ^ 56 + 2 ^ 126 * (2 * ((1 + 1 / 2 ^ 60) * (1 / 2 ^ 72 + 1 / 2 ^ 113))) := by
        refine add_le_add mn ?_
        rw [abs_mul, abs_of_nonneg (by positivity), show (2 : ℝ) ^ ((k.val : ℝ) / 256) * 2 ^ 126 *
          |Real.exp A - Real.exp B| = 2 ^ 126 * ((2 : ℝ) ^ ((k.val : ℝ) / 256) * |Real.exp A - Real.exp B|) by ring]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc (2 : ℝ) ^ ((k.val : ℝ) / 256) * |Real.exp A - Real.exp B|
            ≤ (2 : ℝ) ^ ((k.val : ℝ) / 256) * (Real.exp B * ((1 + 1 / 2 ^ 60) * (1 / 2 ^ 72 + 1 / 2 ^ 113))) :=
              mul_le_mul_of_nonneg_left es T0
          _ = (2 : ℝ) ^ ((k.val : ℝ) / 256) * Real.exp B * ((1 + 1 / 2 ^ 60) * (1 / 2 ^ 72 + 1 / 2 ^ 113)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right top (by positivity)
    _ ≤ 14 / 10 * 2 ^ 56 := by norm_num

/-- `tables::exp::EXP2_FRAC` is `126`. -/
theorem exp2_frac_val : fulcrum.tables.exp.EXP2_FRAC.val = 126 := by
  unfold fulcrum.tables.exp.EXP2_FRAC; rfl

/-- An `f ≤ 32` read as `i64` keeps its value. -/
theorem f_i64_val (f : Std.U32) (hf : f.val ≤ 32) : (UScalar.hcast .I64 f).val = (f.val : ℤ) := by
  rw [UScalar.hcast_val_eq, IScalarTy.I64_numBits_eq]
  exact Int.bmod_eq_of_le (by push_cast; omega) (by push_cast; omega)

/-- L4 on the code: `exp::overflow(f)` of `f ≤ 32` never fails and is `2^(2f)`. -/
theorem overflow_spec (f : Std.U32) (hf : f.val ≤ 32) :
    fulcrum.exp.overflow f ⦃ r => r.val = 2 ^ (2 * f.val) ⦄ := by
  unfold fulcrum.exp.overflow
  refine WP.spec_bind (UScalar.mul_spec (x := 2#u32) (y := f) (by rw [lit_val, U32_max_val]; omega))
    fun i5 h5 => ?_
  rw [lit_val] at h5
  refine WP.spec_mono (IScalar.ShiftLeft_spec 1#i128 i5 (by rw [h5, IScalarTy.I128_numBits_eq]; omega))
    fun z ⟨hz, _⟩ => ?_
  rw [hz, h5, show ((1#i128 : Std.I128).val) = 1 from rfl, Int.shiftLeft_eq, one_mul,
    IScalarTy.I128_numBits_eq]
  refine Int.bmod_eq_of_le ?_ ?_
  · have : (0 : ℤ) ≤ 2 ^ (2 * f.val) := by positivity
    exact (neg_nonpos.mpr (by positivity)).trans this
  · exact (pow_lt_pow_right₀ (by norm_num) (by omega : 2 * f.val < 127)).trans_le (by norm_num)

/-- L4 on the code: `exp::round_mantissa(m, n, f)` of `m < 2^127`, `-2^62 ≤ n ≤ 126 - f`,
`f ≤ 32` never fails and rounds `m / 2^s` once, `s = min (126 - f - n) 128`. -/
theorem round_mantissa_spec (m : Std.U128) (n : Std.I64) (f : Std.U32) (hm : m.val < 2 ^ 127)
    (hn0 : -2 ^ 62 ≤ n.val) (hn1 : n.val ≤ 126 - f.val) (hf : f.val ≤ 32) :
    fulcrum.exp.round_mantissa m n f ⦃ r =>
      r.val = roundHalfUp (exact (min (126 - f.val - n.val).toNat 128) m.val) ⦄ := by
  unfold fulcrum.exp.round_mantissa
  rw [lift, bind_ok, lift, bind_ok]
  have c126 : (UScalar.hcast .I64 fulcrum.tables.exp.EXP2_FRAC).val = 126 := by
    rw [UScalar.hcast_val_eq, exp2_frac_val]; rfl
  have fc := f_i64_val f hf
  have mn : IScalar.min .I64 = -2 ^ 63 := min_eq_neg_pow IScalarTy.I64_numBits_eq
  have mx : IScalar.max .I64 = 2 ^ 63 - 1 := max_eq_pow_sub_one IScalarTy.I64_numBits_eq
  refine WP.spec_bind (IScalar.sub_spec (x := UScalar.hcast .I64 fulcrum.tables.exp.EXP2_FRAC)
    (y := UScalar.hcast .I64 f) (by rw [c126, fc, mn]; omega) (by rw [c126, fc, mx]; omega)) fun i2 h2 => ?_
  rw [c126, fc] at h2
  refine WP.spec_bind (IScalar.sub_spec (x := i2) (y := n) (by rw [h2, mn]; omega)
    (by rw [h2, mx]; omega)) fun s hs => ?_
  rw [h2] at hs
  have mc : (UScalar.hcast .I128 m).val = (m.val : ℤ) := by
    rw [UScalar.hcast_val_eq, IScalarTy.I128_numBits_eq]
    exact Int.bmod_eq_of_le ((neg_nonpos.mpr (by positivity)).trans (Int.natCast_nonneg _))
      ((by exact_mod_cast hm : (m.val : ℤ) < 2 ^ 127).trans_le (by norm_num))
  by_cases big : s > 128#i64
  · have b : (128 : ℤ) < s.val := big
    rw [ite_eq_left big, bind_ok, lift, bind_ok]
    refine WP.spec_mono (shr_round_spec _ _) fun r hr => ?_
    rw [hr, mc, lit_val, min_eq_right (by omega)]
  · have b : s.val ≤ 128 := not_lt.mp big
    rw [ite_eq_right big, bind_ok, lift, bind_ok]
    refine WP.spec_mono (shr_round_spec _ _) fun r hr => ?_
    have sv : (IScalar.hcast .U32 s).val = (126 - f.val - n.val).toNat := by
      rw [IScalar.hcast_val_eq, UScalarTy.U32_numBits_eq, hs, Int.emod_eq_of_lt (by omega) (by omega)]
    rw [hr, mc, sv, min_eq_left (by omega)]

/-- `2^(raw / 2^f) · 2^f · 2^s = 2^(t / 2^f) · 2^126` for `raw = 2^f · n + t` and
`s = 126 - f - n`. -/
theorem exp2_scale (raw n : ℤ) (f s : ℕ) (t : ℝ) (h : (raw : ℝ) = 2 ^ f * n + t) (hs : (s : ℤ) = 126 - f - n) :
    (2 : ℝ) ^ ((raw : ℝ) / 2 ^ f) * 2 ^ f * 2 ^ s = (2 : ℝ) ^ (t / 2 ^ f) * 2 ^ 126 := by
  have e : (raw : ℝ) / 2 ^ f = (n : ℝ) + t / 2 ^ f := by rw [h]; field_simp
  have p : (2 : ℝ) ^ n * 2 ^ f * 2 ^ s = 2 ^ 126 := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ two_ne_zero, ← zpow_add₀ two_ne_zero]
    congr 1
    omega
  rw [e, Real.rpow_add two_pos, Real.rpow_intCast, ← p]
  ring

/-- The rounding of `exp2`, `exp` and `exp2_wide`: a mantissa `m < 2^127` within `1.4 · 2^56`
of `X · 2^s`, `s = 126 - f - n`, `n ≤ f - 2`, `0 ≤ X`, `X · 2^s ≤ 2^128`, rounded once by
`2^(min s 128)`, `f ≤ 32`, is within `½ + 1.4 · 2^(2f) / 2^72` of `X`. -/
theorem mantissa_round_near (m : ℕ) (n : ℤ) (f : ℕ) (X : ℝ) (mlt : m < 2 ^ 127) (hf : f ≤ 32) (hn : n ≤ f - 2) (X0 : 0 ≤ X)
    (hX : X * 2 ^ (126 - f - n).toNat ≤ 2 ^ 128)
    (hm : |(m : ℝ) - X * 2 ^ (126 - f - n).toNat| ≤ 14 / 10 * 2 ^ 56) :
    |((roundHalfUp (exact (min (126 - f - n).toNat 128) m) : ℤ) : ℝ) - X| ≤
      1 / 2 + 14 / 10 * 2 ^ (2 * f) / 2 ^ 72 := by
  set s : ℕ := (126 - f - n).toNat with hsd
  have sv : (s : ℤ) = 126 - f - n := Int.toNat_of_nonneg (by omega)
  by_cases cl : s ≤ 128
  · rw [min_eq_left cl]
    have near := round_div_near m s X (14 / 10 * 2 ^ 56) (by exact_mod_cast hm)
    refine near.trans (add_le_add le_rfl ?_)
    rw [div_le_div_iff₀ (by positivity) (by positivity), mul_assoc, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    rw [← pow_add, ← pow_add]
    exact pow_le_pow_right₀ one_le_two (by omega)
  · rw [min_eq_right (by omega)]
    have q0 : (0 : ℚ) ≤ exact 128 m := by unfold exact; positivity
    have q1 : exact 128 m < 1 / 2 := by
      unfold exact
      rw [div_lt_iff₀ (by positivity)]
      have : (m : ℚ) < 2 ^ 127 := by exact_mod_cast mlt
      push_cast; linarith
    have z : roundHalfUp (exact 128 m) = 0 := by
      unfold roundHalfUp
      exact Int.floor_eq_zero_iff.mpr ⟨by linarith, by linarith⟩
    rw [z, Int.cast_zero, zero_sub, abs_neg, abs_of_nonneg X0]
    have p : (2 : ℝ) ^ 129 ≤ 2 ^ s := pow_le_pow_right₀ one_le_two (by omega)
    have : X * 2 ^ 129 ≤ 2 ^ 128 := (mul_le_mul_of_nonneg_left p X0).trans hX
    have : (0 : ℝ) ≤ 14 / 10 * 2 ^ (2 * f) / 2 ^ 72 := by positivity
    nlinarith

/-- L4 on the code: `exp::exp2(raw, f)` with `1 ≤ f ≤ 32` never fails; it returns the mark
`2^(2f)` when `⌊raw / 2^f⌋ ≥ f - 1`, and otherwise a value within
`½ + 1.4 · 2^(2f) / 2^72` of `2^(raw / 2^f) · 2^f`. -/
theorem exp2_spec (raw : Std.I64) (f : Std.U32) (hf1 : 1 ≤ f.val) (hf : f.val ≤ 32) :
    fulcrum.exp.exp2 raw f ⦃ r =>
      ((f.val : ℤ) - 1 ≤ raw.val / 2 ^ f.val ∧ r.val = 2 ^ (2 * f.val)) ∨
      (raw.val / 2 ^ f.val < (f.val : ℤ) - 1 ∧
        |(r.val : ℝ) - (2 : ℝ) ^ ((raw.val : ℝ) / 2 ^ f.val) * 2 ^ f.val| ≤
          1 / 2 + 14 / 10 * 2 ^ (2 * f.val) / 2 ^ 72) ⦄ := by
  unfold fulcrum.exp.exp2
  have mn : IScalar.min .I64 = -2 ^ 63 := min_eq_neg_pow IScalarTy.I64_numBits_eq
  have mx : IScalar.max .I64 = 2 ^ 63 - 1 := max_eq_pow_sub_one IScalarTy.I64_numBits_eq
  refine WP.spec_bind (IScalar.ShiftRight_spec raw f (by rw [IScalarTy.I64_numBits_eq]; omega))
    fun n ⟨hn, _⟩ => ?_
  rw [shr_eq_div] at hn
  rw [lift, bind_ok]
  have fc := f_i64_val f hf
  refine WP.spec_bind (IScalar.sub_spec (x := UScalar.hcast .I64 f) (y := 1#i64) (by rw [fc, mn, show (1#i64 : Std.I64).val = 1 from rfl]; omega)
    (by rw [fc, mx, show (1#i64 : Std.I64).val = 1 from rfl]; omega)) fun i1 h1 => ?_
  rw [fc, show (1#i64 : Std.I64).val = 1 from rfl] at h1
  by_cases ho : n >= i1
  · have : i1.val ≤ n.val := ho
    rw [ite_eq_left ho]
    exact WP.spec_mono (overflow_spec f hf) fun r hr => Or.inl ⟨by rw [← hn]; omega, hr⟩
  have nlt : n.val < (f.val : ℤ) - 1 := by
    have : ¬ i1.val ≤ n.val := ho
    omega
  rw [ite_eq_right ho, lift, bind_ok]
  refine WP.spec_bind (UScalar.ShiftLeft_spec 1#u64 f _ (by rw [UScalarTy.U64_numBits_eq]; omega) rfl)
    fun i3 ⟨h3, _⟩ => ?_
  rw [lit_val, Nat.shiftLeft_eq, one_mul, UScalar.size_def, UScalarTy.U64_numBits_eq,
    Nat.mod_eq_of_lt (Nat.pow_lt_pow_right one_lt_two (by omega))] at h3
  refine WP.spec_bind (UScalar.sub_spec (x := i3) (y := 1#u64) (by rw [h3, lit_val]; exact Nat.one_le_two_pow))
    fun i4 ⟨h4, _⟩ => ?_
  rw [h3, lit_val] at h4
  rw [lift, bind_ok]
  have p64 : (2 : ℤ) ^ f.val ∣ 2 ^ 64 := pow_dvd_pow 2 (by omega)
  have tv : (IScalar.hcast .U64 raw &&& i4).val = (raw.val % 2 ^ f.val).toNat := by
    rw [UScalar.val_and, h4, Nat.and_two_pow_sub_one_eq_mod, IScalar.hcast_val_eq, UScalarTy.U64_numBits_eq]
    have nn : 0 ≤ raw.val % 2 ^ 64 := Int.emod_nonneg _ (by positivity)
    have : ((raw.val % 2 ^ 64).toNat % 2 ^ f.val : ℕ) = ((raw.val % 2 ^ 64) % 2 ^ f.val).toNat := by
      rw [Int.toNat_emod nn (by positivity)]; rfl
    rw [this, Int.emod_emod_of_dvd _ p64]
  generalize IScalar.hcast .U64 raw &&& i4 = t at tv ⊢
  have tl : t.val < 2 ^ f.val := by
    rw [tv]
    have a := Int.emod_lt_of_pos raw.val (by positivity : (0 : ℤ) < 2 ^ f.val)
    have b := Int.emod_nonneg raw.val (by positivity : (2 : ℤ) ^ f.val ≠ 0)
    have : ((raw.val % 2 ^ f.val).toNat : ℤ) < ((2 ^ f.val : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg b]; push_cast; exact a
    exact_mod_cast this
  have tR : (t.val : ℝ) = ((raw.val % 2 ^ f.val : ℤ) : ℝ) := by
    rw [tv]; exact_mod_cast Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity))
  have st : fulcrum.tables.exp.STEPS.val = 8 := exp_steps_val
  refine WP.spec_bind (Pₘ := fun m : Std.U128 =>
      |(m.val : ℝ) - (2 : ℝ) ^ ((t.val : ℝ) / 2 ^ f.val) * 2 ^ 126| ≤ 14 / 10 * 2 ^ 56 ∧
        m.val ≤ 2 ^ 127 - 2 ^ 55) ?_ fun m ⟨hm, mtop⟩ => ?_
  · by_cases small : f ≤ fulcrum.tables.exp.STEPS
    · have fs : f.val ≤ 8 := st ▸ small
      rw [ite_eq_left small]
      refine WP.spec_bind (UScalar.sub_spec (x := fulcrum.tables.exp.STEPS) (y := f) (by rw [st]; exact fs))
        fun i5 ⟨h5, _⟩ => ?_
      rw [st] at h5
      have kl : t.val * 2 ^ (8 - f.val) < 256 := by
        calc t.val * 2 ^ (8 - f.val) < 2 ^ f.val * 2 ^ (8 - f.val) := Nat.mul_lt_mul_of_pos_right tl (by positivity)
          _ = 256 := by rw [← pow_add, Nat.add_sub_cancel' fs]; rfl
      refine WP.spec_bind (UScalar.ShiftLeft_spec t i5 _ (by rw [h5, UScalarTy.U64_numBits_eq]; omega) rfl)
        fun i6 ⟨h6, _⟩ => ?_
      rw [h5, Nat.shiftLeft_eq, UScalar.size_def, UScalarTy.U64_numBits_eq, Nat.mod_eq_of_lt (by omega)] at h6
      refine WP.spec_mono (exp2_unit_spec i6 0#u64 f (by omega) (by rw [lit_val]; positivity) hf)
        fun m ⟨hm, mtop⟩ => ⟨?_, mtop⟩
      rw [lit_val, Nat.cast_zero, zero_div, add_zero, h6, angle_scale_up _ _ fs] at hm
      exact hm
    · have fs : 8 < f.val := by have : ¬ f.val ≤ fulcrum.tables.exp.STEPS.val := small; omega
      rw [ite_eq_right small]
      refine WP.spec_bind (UScalar.sub_spec (x := f) (y := fulcrum.tables.exp.STEPS) (by rw [st]; omega))
        fun rest ⟨hr, _⟩ => ?_
      rw [st] at hr
      refine WP.spec_bind (UScalar.ShiftRight_spec t rest (by rw [hr, UScalarTy.U64_numBits_eq]; omega))
        fun i5 ⟨h5, _⟩ => ?_
      rw [Nat.shiftRight_eq_div_pow, hr] at h5
      refine WP.spec_bind (UScalar.ShiftLeft_spec 1#u64 rest _ (by rw [hr, UScalarTy.U64_numBits_eq]; omega) rfl)
        fun i6 ⟨h6, _⟩ => ?_
      rw [hr, lit_val, Nat.shiftLeft_eq, one_mul, UScalar.size_def, UScalarTy.U64_numBits_eq,
        Nat.mod_eq_of_lt (Nat.pow_lt_pow_right one_lt_two (by omega))] at h6
      refine WP.spec_bind (UScalar.sub_spec (x := i6) (y := 1#u64) (by rw [h6, lit_val]; exact Nat.one_le_two_pow))
        fun i7 ⟨h7, _⟩ => ?_
      rw [h6, lit_val] at h7
      rw [lift, bind_ok]
      have bv : (t &&& i7).val = t.val % 2 ^ (f.val - 8) := by
        rw [UScalar.val_and, h7, Nat.and_two_pow_sub_one_eq_mod]
      have pf : (2 : ℕ) ^ f.val = 2 ^ (f.val - 8) * 2 ^ 8 := by rw [← pow_add]; congr 1; omega
      have kl : i5.val < 256 := by
        rw [h5, Nat.div_lt_iff_lt_mul (by positivity)]
        calc t.val < 2 ^ f.val := tl
          _ = 256 * 2 ^ (f.val - 8) := by rw [pf]; ring
      refine WP.spec_mono (exp2_unit_spec i5 _ f kl (by
          rw [bv]
          calc t.val % 2 ^ (f.val - 8) * 2 ^ 8 < 2 ^ (f.val - 8) * 2 ^ 8 :=
                Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ (by positivity)) (by positivity)
            _ = 2 ^ f.val := pf.symm) hf)
        fun m ⟨hm, mtop⟩ => ⟨?_, mtop⟩
      rw [bv, h5] at hm
      have e : ((t.val / 2 ^ (f.val - 8) : ℕ) : ℝ) / 256 + ((t.val % 2 ^ (f.val - 8) : ℕ) : ℝ) / 2 ^ f.val =
          (t.val : ℝ) / 2 ^ f.val := by
        have d : (t.val : ℝ) = ((t.val / 2 ^ (f.val - 8) : ℕ) : ℝ) * 2 ^ (f.val - 8) +
            ((t.val % 2 ^ (f.val - 8) : ℕ) : ℝ) := by
          exact_mod_cast (Nat.div_add_mod' t.val (2 ^ (f.val - 8))).symm
        have q : (2 : ℝ) ^ f.val = 2 ^ (f.val - 8) * 256 := by exact_mod_cast (pf.trans (by norm_num))
        rw [d, q]; field_simp
      rw [e] at hm
      exact hm
  have mlt : m.val < 2 ^ 127 := by omega
  have rawlo : -2 ^ 62 ≤ n.val := by
    rw [hn, Int.le_ediv_iff_mul_le (by positivity)]
    have ⟨l, _⟩ := val_bounds raw IScalarTy.I64_numBits_eq
    have : (2 : ℤ) ≤ 2 ^ f.val := by
      calc (2 : ℤ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f.val := pow_le_pow_right₀ (by norm_num) hf1
    nlinarith
  refine WP.spec_mono (round_mantissa_spec m n f mlt rawlo (by omega) hf) fun r hr => Or.inr ⟨by rw [← hn]; exact nlt, ?_⟩
  rw [hr]
  set X : ℝ := (2 : ℝ) ^ ((raw.val : ℝ) / 2 ^ f.val) * 2 ^ f.val with hX
  set s : ℕ := (126 - f.val - n.val).toNat with hsd
  have sv : (s : ℤ) = 126 - f.val - n.val := Int.toNat_of_nonneg (by omega)
  have split : (raw.val : ℝ) = 2 ^ f.val * (n.val : ℝ) + t.val := by
    rw [tR, hn]; exact_mod_cast (Int.mul_ediv_add_emod raw.val (2 ^ f.val)).symm
  have sc := exp2_scale raw.val n.val f.val s t.val (by exact_mod_cast split) sv
  rw [← hX] at sc
  refine mantissa_round_near m.val n.val f.val X mlt hf (by omega) (by positivity) ?_ (by rw [sc]; exact_mod_cast hm)
  rw [sc]
  refine (mul_le_mul_of_nonneg_right ?_ (by positivity)).trans (by norm_num : (2 : ℝ) * 2 ^ 126 ≤ 2 ^ 128)
  calc (2 : ℝ) ^ ((t.val : ℝ) / 2 ^ f.val) ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le one_le_two (by
        rw [div_le_one (by positivity)]; exact_mod_cast tl.le)
    _ = 2 := Real.rpow_one 2

/-- `exp::REDUCED_FRAC` is `112`. -/
theorem reduced_frac_spec : fulcrum.exp.REDUCED_FRAC ⦃ r => r.val = 112 ⦄ := by
  unfold fulcrum.exp.REDUCED_FRAC
  exact WP.spec_mono (UScalar.add_spec (x := fulcrum.tables.exp.LN_2_FRAC) (y := fulcrum.tables.exp.STEPS)
    (by rw [ln_2_frac_val, exp_steps_val, U32_max_val]; norm_num)) fun r hr => by
      rw [hr, ln_2_frac_val, exp_steps_val]

/-- `x &&& 255` of an `i128` is `x mod 256`. -/
theorem and_255_val (x : Std.I128) : (x &&& 255#i128).val = x.val % 256 := by
  have m : (255#i128 : Std.I128).bv.toNat = 2 ^ 8 - 1 := rfl
  have d : (256 : ℤ) ∣ ((2 ^ IScalarTy.I128.numBits : ℕ) : ℤ) := ⟨2 ^ 120, rfl⟩
  have small : ((x.bv.toNat % 2 ^ 8 : ℕ) : ℤ).bmod (2 ^ IScalarTy.I128.numBits) = ((x.bv.toNat % 2 ^ 8 : ℕ) : ℤ) :=
    Int.bmod_eq_of_le (by rw [IScalarTy.I128_numBits_eq]; omega) (by rw [IScalarTy.I128_numBits_eq]; omega)
  rw [IScalar.val, IScalar.val, IScalar.bv_and, BitVec.toInt_and, m, Nat.and_two_pow_sub_one_eq_mod,
    small, BitVec.toInt_eq_toNat_bmod, ← Int.emod_emod_of_dvd _ d, Int.bmod_emod,
    Int.emod_emod_of_dvd _ d]
  exact Int.natCast_emod _ (2 ^ 8)

/-- `2^n = e^(n ln 2)`. -/
theorem two_pow_eq_exp (n : ℕ) : (2 : ℝ) ^ n = Real.exp (n * Real.log 2) := by
  rw [Real.exp_nat_mul, Real.exp_log two_pos]

/-- `LN_2` is above `ln 2 · 2^104`. -/
theorem ln_2_ge : Real.log 2 * 2 ^ 104 ≤ fulcrum.tables.exp.LN_2.val := by
  have c := (Rat.cast_le (K := ℝ)).mpr (by decide +kernel :
    (ln2Q + 1 / 2 ^ 270) * 2 ^ 104 ≤ (14058695031733113177892216608772 : ℚ))
  simp only [Rat.cast_mul, Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] at c
  rw [ln_2_val, Nat.cast_ofNat]
  have := (abs_le.mp log_two_near).2
  exact (mul_le_mul_of_nonneg_right (sub_le_iff_le_add'.mp this) (by positivity)).trans c

/-- `e^x · 2^f · 2^s = 2^(k/256) · e^Y · 2^126` for `j = 256 n + k`, `Y = x - j · ln 2 / 256`
and `s = 126 - f - n`. -/
theorem exp_scale (x : ℝ) (j n k : ℤ) (f s : ℕ) (hj : j = 256 * n + k) (hs : (s : ℤ) = 126 - f - n) :
    Real.exp x * 2 ^ f * 2 ^ s =
      (2 : ℝ) ^ ((k : ℝ) / 256) * Real.exp (x - j * Real.log 2 / 256) * 2 ^ 126 := by
  have p : (2 : ℝ) ^ n * 2 ^ f * 2 ^ s = 2 ^ 126 := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ two_ne_zero, ← zpow_add₀ two_ne_zero]
    congr 1
    omega
  have en : Real.exp (n * Real.log 2) = (2 : ℝ) ^ n := by
    rw [← Real.rpow_intCast, Real.rpow_def_of_pos two_pos, mul_comm]
  have ek : (2 : ℝ) ^ ((k : ℝ) / 256) = Real.exp (k / 256 * Real.log 2) := by
    rw [Real.rpow_def_of_pos two_pos, mul_comm]
  have ex : Real.exp x = Real.exp (n * Real.log 2) * Real.exp (k / 256 * Real.log 2) *
      Real.exp (x - j * Real.log 2 / 256) := by
    rw [← Real.exp_add, ← Real.exp_add, hj]; congr 1; push_cast; ring
  rw [ex, en, ek, ← p]
  ring

/-- L4 on the code: `exp::exp(raw, f)` with `1 ≤ f ≤ 32` never fails; it returns the mark
`2^(2f)` only when `e^(raw / 2^f) · 2^f ≥ 2^(2f - 1)`, and otherwise a value within
`½ + 1.4 · 2^(2f) / 2^72` of `e^(raw / 2^f) · 2^f`. -/
theorem exp_spec (raw : Std.I64) (f : Std.U32) (hf1 : 1 ≤ f.val) (hf : f.val ≤ 32) :
    fulcrum.exp.exp raw f ⦃ r =>
      (r.val = 2 ^ (2 * f.val) ∧ (2 : ℝ) ^ (2 * f.val - 1) ≤ Real.exp ((raw.val : ℝ) / 2 ^ f.val) * 2 ^ f.val) ∨
      |(r.val : ℝ) - Real.exp ((raw.val : ℝ) / 2 ^ f.val) * 2 ^ f.val| ≤
        1 / 2 + 14 / 10 * 2 ^ (2 * f.val) / 2 ^ 72 ⦄ := by
  unfold fulcrum.exp.exp
  have mn : IScalar.min .I64 = -2 ^ 63 := min_eq_neg_pow IScalarTy.I64_numBits_eq
  have mx : IScalar.max .I64 = 2 ^ 63 - 1 := max_eq_pow_sub_one IScalarTy.I64_numBits_eq
  have mn2 : IScalar.min .I128 = -2 ^ 127 := min_eq_neg_pow IScalarTy.I128_numBits_eq
  have mx2 : IScalar.max .I128 = 2 ^ 127 - 1 := max_eq_pow_sub_one IScalarTy.I128_numBits_eq
  have fc := f_i64_val f hf
  have p32 : (2 : ℤ) ^ f.val ≤ 2 ^ 32 := pow_le_pow_right₀ (by norm_num) hf
  have pp : (0 : ℤ) < 2 ^ f.val := by positivity
  have l0 := log_two_ge'
  have l1 := log_two_le'
  set x : ℝ := (raw.val : ℝ) / 2 ^ f.val with hx
  have fR : (0 : ℝ) < 2 ^ f.val := by positivity
  rw [lift, bind_ok]
  refine WP.spec_bind (IScalar.ShiftLeft_spec (UScalar.hcast .I64 f) f (by rw [IScalarTy.I64_numBits_eq]; omega))
    fun i1 ⟨h1, _⟩ => ?_
  have i1v : i1.val = f.val * 2 ^ f.val := by
    rw [h1, fc, Int.shiftLeft_eq, IScalarTy.I64_numBits_eq]
    exact Int.bmod_eq_of_le (by push_cast; nlinarith) (by push_cast; nlinarith)
  by_cases o1 : raw >= i1
  · have : i1.val ≤ raw.val := o1
    rw [ite_eq_left o1]
    refine WP.spec_mono (overflow_spec f hf) fun r hr => Or.inl ⟨hr, ?_⟩
    have xf : (f.val : ℝ) ≤ x := by
      rw [hx, le_div_iff₀ fR]; exact_mod_cast (show (f.val : ℤ) * 2 ^ f.val ≤ raw.val by omega)
    have : (2 : ℝ) ^ f.val ≤ Real.exp x := by
      rw [two_pow_eq_exp]; exact Real.exp_le_exp.mpr (by nlinarith [(Nat.cast_nonneg f.val : (0 : ℝ) ≤ f.val)])
    calc (2 : ℝ) ^ (2 * f.val - 1) ≤ 2 ^ (2 * f.val) := pow_le_pow_right₀ one_le_two (by omega)
      _ = 2 ^ f.val * 2 ^ f.val := by rw [← pow_add, two_mul]
      _ ≤ Real.exp x * 2 ^ f.val := mul_le_mul_of_nonneg_right this fR.le
  have r1 : raw.val < f.val * 2 ^ f.val := by have : ¬ i1.val ≤ raw.val := o1; omega
  rw [ite_eq_right o1, lift, bind_ok]
  refine WP.spec_bind (IScalar.mul_spec (x := 2#i64) (y := UScalar.hcast .I64 f)
    (by rw [fc, mn, show (2#i64 : Std.I64).val = 2 from rfl]; omega)
    (by rw [fc, mx, show (2#i64 : Std.I64).val = 2 from rfl]; omega)) fun i3 h3 => ?_
  rw [fc, show (2#i64 : Std.I64).val = 2 from rfl] at h3
  refine WP.spec_bind (IScalar.ShiftLeft_spec i3 f (by rw [IScalarTy.I64_numBits_eq]; omega)) fun i4 ⟨h4, _⟩ => ?_
  have i4v : i4.val = 2 * f.val * 2 ^ f.val := by
    rw [h4, h3, Int.shiftLeft_eq, IScalarTy.I64_numBits_eq]
    exact Int.bmod_eq_of_le (by push_cast; nlinarith) (by push_cast; nlinarith)
  refine WP.spec_bind (IScalar.neg_step i4 (fun e => by
    have : i4.val = IScalar.min .I64 := e
    rw [i4v, mn] at this; nlinarith)) fun i5 h5 => ?_
  have i5v : i5.val = -(2 * f.val * 2 ^ f.val) := by rw [h5, i4v]
  by_cases o2 : raw <= i5
  · have : raw.val ≤ i5.val := o2
    rw [ite_eq_left o2, WP.spec_ok]
    right
    rw [show ((0#i128 : Std.I128).val : ℝ) = 0 from by norm_num, zero_sub, abs_neg,
      abs_of_nonneg (by positivity)]
    have xf : x ≤ -(2 * f.val) := by
      rw [hx, div_le_iff₀ fR]
      have : (raw.val : ℝ) ≤ ((-(2 * f.val * 2 ^ f.val) : ℤ) : ℝ) := by exact_mod_cast (show raw.val ≤ -(2 * f.val * 2 ^ f.val) by omega)
      push_cast at this; linarith
    rw [two_pow_eq_exp, ← Real.exp_add]
    have fr : (1 : ℝ) ≤ f.val := by exact_mod_cast hf1
    calc Real.exp (x + f.val * Real.log 2) ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.mpr (by nlinarith)
      _ = 1 / 2 := by rw [Real.exp_neg, Real.exp_log two_pos, one_div]
      _ ≤ _ := le_add_of_nonneg_right (by positivity)
  have r2 : -(2 * f.val * 2 ^ f.val) < raw.val := by have : ¬ raw.val ≤ i5.val := o2; omega
  rw [ite_eq_right o2, lift, bind_ok, lift, bind_ok]
  have rv := cast_i128_val raw
  generalize IScalar.cast .I128 raw = raw1 at rv ⊢
  have Kc : (UScalar.hcast .I128 fulcrum.tables.exp.TWO_LOG2_E).val = 13306513097844322492 := by
    rw [UScalar.hcast_val_eq, IScalarTy.I128_numBits_eq, two_log2_e_val]; decide
  generalize UScalar.hcast .I128 fulcrum.tables.exp.TWO_LOG2_E = i6 at Kc ⊢
  have fr : (f.val : ℤ) ≤ 32 := by exact_mod_cast hf
  have f2 : (f.val : ℤ) * 2 ^ f.val ≤ 32 * 2 ^ f.val := mul_le_mul_of_nonneg_right fr pp.le
  have rlo : -(64 * 2 ^ f.val) ≤ raw.val := by linarith
  have rhi : raw.val ≤ 64 * 2 ^ f.val := by linarith
  have Qb : -(2 ^ 15 * (2 ^ f.val * 2 ^ 55)) ≤ raw.val * 13306513097844322492 ∧
      raw.val * 13306513097844322492 ≤ 2 ^ 15 * (2 ^ f.val * 2 ^ 55) := ⟨by linarith, by linarith⟩
  refine WP.spec_bind (IScalar.mul_spec (x := raw1) (y := i6) (by rw [rv, Kc, mn2]; linarith)
    (by rw [rv, Kc, mx2]; linarith)) fun i7 h7 => ?_
  rw [rv, Kc] at h7
  refine WP.spec_bind (UScalar.add_spec (x := f) (y := fulcrum.tables.exp.FRAC)
    (by rw [exp_frac_val, U32_max_val]; omega)) fun i8 h8 => ?_
  rw [exp_frac_val] at h8
  refine WP.spec_bind (UScalar.add_spec (x := i8) (y := 1#u32) (by rw [lit_val, U32_max_val]; omega)) fun i9 h9 => ?_
  rw [h8, lit_val] at h9
  refine WP.spec_bind (UScalar.sub_spec (x := i9) (y := fulcrum.tables.exp.STEPS)
    (by rw [exp_steps_val]; omega)) fun i10 ⟨h10, _⟩ => ?_
  rw [exp_steps_val, h9] at h10
  refine WP.spec_bind (IScalar.ShiftRight_spec i7 i10 (by rw [IScalarTy.I128_numBits_eq]; omega)) fun j ⟨hj, _⟩ => ?_
  rw [shr_eq_div, h7, h10, show f.val + 62 + 1 - 8 = f.val + 55 by omega] at hj
  set D : ℤ := 2 ^ (f.val + 55) with hD
  have D' : D = 2 ^ f.val * 2 ^ 55 := by rw [hD, pow_add]
  have Dp : 0 < D := by positivity
  have jlo : -2 ^ 15 ≤ j.val := by
    rw [hj, Int.le_ediv_iff_mul_le Dp, D']; linarith [Qb.1]
  have jhi : j.val ≤ 2 ^ 15 := by
    have : j.val < 2 ^ 15 + 1 := by
      have : (0 : ℤ) < 2 ^ f.val * 2 ^ 55 := by positivity
      rw [hj, Int.ediv_lt_iff_lt_mul Dp, D']; linarith [Qb.2]
    omega
  have jD1 : j.val * D ≤ raw.val * 13306513097844322492 := hj ▸ Int.ediv_mul_le _ Dp.ne'
  have jD2 : raw.val * 13306513097844322492 < (j.val + 1) * D := hj ▸ Int.lt_ediv_add_one_mul_self _ Dp
  refine WP.spec_bind reduced_frac_spec fun i11 h11 => ?_
  refine WP.spec_bind (UScalar.sub_spec (x := i11) (y := f) (by omega)) fun i12 ⟨h12, _⟩ => ?_
  rw [h11] at h12
  refine WP.spec_bind (IScalar.ShiftLeft_spec raw1 i12 (by rw [IScalarTy.I128_numBits_eq]; omega)) fun i13 ⟨h13, _⟩ => ?_
  have p112 : (2 : ℤ) ^ (112 - f.val) * 2 ^ f.val = 2 ^ 112 := by rw [← pow_add]; congr 1; omega
  have i13v : i13.val = raw.val * 2 ^ (112 - f.val) := by
    rw [h13, rv, h12, Int.shiftLeft_eq, IScalarTy.I128_numBits_eq]
    have q : (0 : ℤ) < 2 ^ (112 - f.val) := by positivity
    have u := mul_le_mul_of_nonneg_right rhi q.le
    have l := mul_le_mul_of_nonneg_right rlo q.le
    rw [mul_assoc, mul_comm (2 ^ f.val), p112] at u
    rw [neg_mul, mul_assoc, mul_comm (2 ^ f.val), p112] at l
    exact Int.bmod_eq_of_le (by push_cast; linarith) (by push_cast; linarith)
  rw [bind_ok]
  have Lc : (UScalar.hcast .I128 fulcrum.tables.exp.LN_2).val = (fulcrum.tables.exp.LN_2.val : ℤ) := by
    rw [UScalar.hcast_val_eq, IScalarTy.I128_numBits_eq, ln_2_val]; decide
  generalize UScalar.hcast .I128 fulcrum.tables.exp.LN_2 = i14 at Lc ⊢
  set L : ℤ := (fulcrum.tables.exp.LN_2.val : ℤ) with hL
  have Lv : L = 14058695031733113177892216608772 := by rw [hL, ln_2_val]; rfl
  refine WP.spec_bind (IScalar.mul_spec (x := j) (y := i14) (by rw [Lc, mn2, Lv]; linarith)
    (by rw [Lc, mx2, Lv]; linarith)) fun i15 h15 => ?_
  rw [Lc] at h15
  set P : ℤ := raw.val * 2 ^ (112 - f.val) with hP
  have Pb : -(2 ^ 118) ≤ P ∧ P ≤ 2 ^ 118 := by
    have q : (0 : ℤ) < 2 ^ (112 - f.val) := by positivity
    have u := mul_le_mul_of_nonneg_right rhi q.le
    have l := mul_le_mul_of_nonneg_right rlo q.le
    rw [mul_assoc, mul_comm (2 ^ f.val), p112] at u
    rw [neg_mul, mul_assoc, mul_comm (2 ^ f.val), p112] at l
    constructor <;> linarith
  refine WP.spec_bind (IScalar.sub_spec (x := i13) (y := i15) (by rw [i13v, h15, mn2, Lv]; linarith [Pb.1, Pb.2])
    (by rw [i13v, h15, mx2, Lv]; linarith [Pb.1, Pb.2])) fun y hy => ?_
  rw [i13v, h15] at hy
  have PD : P * D = raw.val * 2 ^ 167 := by
    rw [hP, D', mul_assoc, ← mul_assoc (2 ^ (112 - f.val)), p112]; ring
  have dd : (13306513097844322492 : ℤ) * L = 2 ^ 167 + 3595333768577312205446798598896 := by rw [Lv]; norm_num
  have rd : -(D * L) ≤ 2 * (raw.val * 3595333768577312205446798598896) ∧
      2 * (raw.val * 3595333768577312205446798598896) ≤ D * L := by
    have c : (128 : ℤ) * 3595333768577312205446798598896 ≤ 2 ^ 55 * L := by rw [Lv]; norm_num
    have c' := mul_le_mul_of_nonneg_right c pp.le
    rw [D']; constructor <;> linarith
  have yD : y.val * D = raw.val * 2 ^ 167 - j.val * D * L := by rw [hy, ← PD]; ring
  have a1 : j.val * D * L ≤ raw.val * 13306513097844322492 * L := mul_le_mul_of_nonneg_right jD1 (by rw [Lv]; norm_num)
  have a2 : raw.val * 13306513097844322492 * L < (j.val + 1) * D * L := mul_lt_mul_of_pos_right jD2 (by rw [Lv]; norm_num)
  have QL : raw.val * 13306513097844322492 * L = raw.val * 2 ^ 167 + raw.val * 3595333768577312205446798598896 := by
    rw [mul_assoc, dd]; ring
  have ylo : -L < y.val := by
    have : -L * D < y.val * D := by linarith
    exact lt_of_mul_lt_mul_right this Dp.le
  have yhi : y.val < 2 * L := by
    have : y.val * D < 2 * L * D := by linarith
    exact lt_of_mul_lt_mul_right this Dp.le
  refine WP.spec_bind (Pₘ := fun p : Std.I128 × Std.I128 => p.2.val = P - p.1.val * L ∧ 0 ≤ p.2.val ∧
      p.2.val < L ∧ -2 ^ 15 - 1 ≤ p.1.val ∧ p.1.val ≤ 2 ^ 15 + 1) ?_ fun p hp => ?_
  · by_cases c1 : y < 0#i128
    · have : y.val < 0 := c1
      rw [ite_eq_left c1]
      refine WP.spec_bind (IScalar.sub_spec (x := j) (y := 1#i128)
        (by rw [mn2, show (1#i128 : Std.I128).val = 1 from rfl]; omega)
        (by rw [mx2, show (1#i128 : Std.I128).val = 1 from rfl]; omega)) fun j2 h2 => ?_
      rw [show (1#i128 : Std.I128).val = 1 from rfl] at h2
      rw [bind_ok]
      refine WP.spec_bind (IScalar.add_spec (x := y) (y := i14)
        (by rw [Lc, mn2]; omega) (by rw [Lc, mx2, Lv]; omega)) fun y2 hy2 => ?_
      rw [WP.spec_ok]
      rw [Lc] at hy2
      dsimp only
      refine ⟨by rw [hy2, h2, hy]; ring, by omega, by omega, by omega, by omega⟩
    rw [ite_eq_right c1, bind_ok]
    have c1' : 0 ≤ y.val := by have : ¬ y.val < 0 := c1; omega
    by_cases c2 : y >= i14
    · have : L ≤ y.val := by have := (show _ ≤ y.val from c2); rwa [Lc] at this
      rw [ite_eq_left c2]
      refine WP.spec_bind (IScalar.add_spec (x := j) (y := 1#i128)
        (by rw [mn2, show (1#i128 : Std.I128).val = 1 from rfl]; omega)
        (by rw [mx2, show (1#i128 : Std.I128).val = 1 from rfl]; omega)) fun j2 h2 => ?_
      rw [show (1#i128 : Std.I128).val = 1 from rfl] at h2
      rw [bind_ok]
      refine WP.spec_bind (IScalar.sub_spec (x := y) (y := i14)
        (by rw [Lc, mn2, Lv]; omega) (by rw [Lc, mx2]; omega)) fun y2 hy2 => ?_
      rw [WP.spec_ok]
      rw [Lc] at hy2
      dsimp only
      refine ⟨by rw [hy2, h2, hy]; ring, by omega, by omega, by omega, by omega⟩
    · have : y.val < L := by
        have : ¬ (i14).val ≤ y.val := c2
        rw [Lc] at this; omega
      rw [ite_eq_right c2, WP.spec_ok]
      dsimp only
      exact ⟨by rw [hy], c1', this, by omega, by omega⟩
  obtain ⟨j1, y1⟩ := p
  obtain ⟨hy1, y10, y1L, j1lo, j1hi⟩ := hp
  dsimp only at hy1 y10 y1L j1lo j1hi ⊢
  simp only [lift, bind_ok]
  have st := exp_steps_val
  refine WP.spec_bind (IScalar.ShiftRight_spec j1 fulcrum.tables.exp.STEPS
    (by rw [st, IScalarTy.I128_numBits_eq]; norm_num)) fun i16 ⟨h16, _⟩ => ?_
  rw [shr_eq_div, st] at h16
  have nlo : -2 ^ 8 ≤ i16.val := by rw [h16, Int.le_ediv_iff_mul_le (by norm_num)]; omega
  have nhi : i16.val ≤ 2 ^ 8 := by
    have : i16.val < 2 ^ 8 + 1 := by rw [h16, Int.ediv_lt_iff_lt_mul (by norm_num)]; omega
    omega
  have inr : InRange 63 i16.val :=
    ⟨(by unfold minOf; norm_num : minOf 63 ≤ -2 ^ 8).trans nlo, nhi.trans (by unfold maxOf; norm_num)⟩
  have nv : (IScalar.cast .I64 i16).val = j1.val / 256 :=
    ((IScalar.cast_val_eq .I64 i16).trans ((wrap_eq_self_iff 63 _).2 inr)).trans h16
  generalize IScalar.cast .I64 i16 = n at nv ⊢
  refine WP.spec_bind (IScalar.sub_spec (x := UScalar.hcast .I64 f) (y := 1#i64)
    (by rw [fc, mn, show (1#i64 : Std.I64).val = 1 from rfl]; omega)
    (by rw [fc, mx, show (1#i64 : Std.I64).val = 1 from rfl]; omega)) fun i18 h18 => ?_
  rw [fc, show (1#i64 : Std.I64).val = 1 from rfl] at h18
  have xP : x * 2 ^ 112 = (P : ℝ) := by
    rw [hx, hP]; push_cast
    have : (2 : ℝ) ^ 112 = 2 ^ (112 - f.val) * 2 ^ f.val := by rw [← pow_add]; congr 1; omega
    rw [this]; field_simp
  have Lr : (L : ℝ) = fulcrum.tables.exp.LN_2.val := by rw [hL]; push_cast; rfl
  by_cases o3 : n >= i18
  · have : i18.val ≤ n.val := o3
    rw [ite_eq_left o3]
    refine WP.spec_mono (overflow_spec f hf) fun r hr => Or.inl ⟨hr, ?_⟩
    have jb : ((f.val : ℤ) - 1) * 256 ≤ j1.val := by
      rw [← Int.le_ediv_iff_mul_le (by norm_num)]; omega
    have jb' : (((f.val : ℤ) - 1) * 256 : ℝ) ≤ j1.val := by exact_mod_cast jb
    have f1 : (0 : ℝ) ≤ (f.val : ℝ) - 1 := sub_nonneg.mpr (by exact_mod_cast hf1)
    have xlo : ((f.val : ℝ) - 1) * Real.log 2 ≤ x := by
      have e1 : (P : ℝ) = j1.val * L + y1.val := by rw [hy1]; push_cast; ring
      have Lg := ln_2_ge
      rw [← Lr] at Lg
      have y0 : (0 : ℝ) ≤ y1.val := by exact_mod_cast y10
      have Lp : (0 : ℝ) ≤ L := by rw [Lr]; positivity
      have : ((f.val : ℝ) - 1) * Real.log 2 * 2 ^ 112 ≤ x * 2 ^ 112 := by
        rw [xP, e1]
        have h1 : ((f.val : ℝ) - 1) * 256 * (Real.log 2 * 2 ^ 104) ≤ ((f.val : ℝ) - 1) * 256 * L :=
          mul_le_mul_of_nonneg_left Lg (by positivity)
        have h2 : ((f.val : ℝ) - 1) * 256 * L ≤ (j1.val : ℝ) * L := mul_le_mul_of_nonneg_right jb' Lp
        linarith only [h1, h2, y0]
      exact le_of_mul_le_mul_right this (by positivity)
    have : (2 : ℝ) ^ (2 * f.val - 1) = 2 ^ (f.val - 1) * 2 ^ f.val := by rw [← pow_add]; congr 1; omega
    rw [this]
    refine mul_le_mul_of_nonneg_right ?_ fR.le
    rw [two_pow_eq_exp, Nat.cast_sub hf1, Nat.cast_one]
    exact Real.exp_le_exp.mpr xlo
  have nle : n.val ≤ (f.val : ℤ) - 2 := by have : ¬ i18.val ≤ n.val := o3; omega
  rw [ite_eq_right o3]
  refine WP.spec_bind (IScalar.ShiftLeft_spec 1#i128 fulcrum.tables.exp.STEPS
    (by rw [st, IScalarTy.I128_numBits_eq]; norm_num)) fun i19 ⟨h19, _⟩ => ?_
  rw [st, show ((1#i128 : Std.I128).val) = 1 from rfl, Int.shiftLeft_eq, one_mul, IScalarTy.I128_numBits_eq] at h19
  have i19v : i19.val = 256 := by rw [h19]; rfl
  refine WP.spec_bind (IScalar.sub_spec (x := i19) (y := 1#i128)
    (by rw [i19v, mn2, show (1#i128 : Std.I128).val = 1 from rfl]; norm_num)
    (by rw [i19v, mx2, show (1#i128 : Std.I128).val = 1 from rfl]; norm_num)) fun i20 h20 => ?_
  have e255 : i20 = 255#i128 := IScalar.eq_of_val_eq (by rw [h20, i19v]; rfl)
  subst e255
  have kv : (IScalar.hcast .U64 (j1 &&& 255#i128)).val = (j1.val % 256).toNat := by
    rw [IScalar.hcast_val_eq, and_255_val, UScalarTy.U64_numBits_eq,
      Int.emod_eq_of_lt (Int.emod_nonneg _ (by norm_num)) ((Int.emod_lt_of_pos _ (by norm_num)).trans (by norm_num))]
  generalize IScalar.hcast .U64 (j1 &&& 255#i128) = k at kv ⊢
  have k256 : k.val < 256 := by rw [kv]; have := Int.emod_lt_of_pos j1.val (by norm_num : (0 : ℤ) < 256); omega
  refine WP.spec_bind (UScalar.sub_spec (x := i11) (y := fulcrum.exp.EXPM1_FRAC)
    (by rw [h11, expm1_frac_val]; norm_num)) fun i22 ⟨h22, _⟩ => ?_
  rw [h11, expm1_frac_val] at h22
  refine WP.spec_bind (IScalar.ShiftRight_spec y1 i22 (by rw [h22, IScalarTy.I128_numBits_eq]; norm_num))
    fun i23 ⟨h23, _⟩ => ?_
  rw [shr_eq_div, h22] at h23
  have q0 : 0 ≤ i23.val := by rw [h23]; exact Int.ediv_nonneg y10 (by norm_num)
  have qL : i23.val ≤ L / 2 ^ 40 := by rw [h23]; exact Int.ediv_le_ediv (by norm_num) y1L.le
  have L40 : L / 2 ^ 40 = ((fulcrum.tables.exp.LN_2.val / 2 ^ 40 : ℕ) : ℤ) := by rw [hL]; push_cast; rfl
  have yv : (IScalar.hcast .U64 i23).val = i23.val.toNat := by
    rw [IScalar.hcast_val_eq, UScalarTy.U64_numBits_eq, Int.emod_eq_of_lt q0 (by
      rw [L40, ln_2_val] at qL; push_cast at qL; omega)]
  generalize IScalar.hcast .U64 i23 = y2 at yv ⊢
  have y2L : y2.val ≤ fulcrum.tables.exp.LN_2.val / 2 ^ 40 := by
    rw [yv]; rw [L40] at qL; omega
  refine WP.spec_bind (exp_unit_spec k y2 k256 y2L) fun m ⟨hm, mtop⟩ => ?_
  have mlt : m.val < 2 ^ 127 := by omega
  refine WP.spec_mono (round_mantissa_spec m n f mlt (by omega) (by omega) hf) fun r hr => Or.inr ?_
  rw [hr]
  set s : ℕ := (126 - f.val - n.val).toNat with hsd
  have sv : (s : ℤ) = 126 - f.val - n.val := Int.toNat_of_nonneg (by omega)
  have jsplit : j1.val = 256 * n.val + j1.val % 256 := by rw [nv]; exact (Int.mul_ediv_add_emod _ _).symm
  have sc := exp_scale x j1.val n.val (j1.val % 256) f.val s jsplit sv
  have kR : ((j1.val % 256 : ℤ) : ℝ) = k.val := by
    rw [kv]; exact_mod_cast (Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))).symm
  rw [kR] at sc
  set Y : ℝ := x - j1.val * Real.log 2 / 256 with hY
  have eL := ln_2_entry
  rw [← Lr] at eL
  have Yr : Y = ((y1.val : ℝ) + j1.val * ((L : ℝ) - Real.log 2 * 2 ^ 104)) / 2 ^ 112 := by
    have e1 : (P : ℝ) = j1.val * L + y1.val := by rw [hy1]; push_cast; ring
    rw [hY, eq_div_iff (by positivity), sub_mul, xP, e1]; ring
  have jR : |(j1.val : ℝ)| ≤ 2 ^ 15 + 1 := by
    rw [abs_le]; constructor
    · have : ((-2 ^ 15 - 1 : ℤ) : ℝ) ≤ j1.val := by exact_mod_cast j1lo
      push_cast at this; linarith only [this]
    · have : (j1.val : ℝ) ≤ ((2 ^ 15 + 1 : ℤ) : ℝ) := by exact_mod_cast j1hi
      push_cast at this; linarith only [this]
  have jL : |(j1.val : ℝ) * ((L : ℝ) - Real.log 2 * 2 ^ 104)| ≤ (2 ^ 15 + 1) * (1 / 2) := by
    rw [abs_mul]; exact mul_le_mul jR eL (abs_nonneg _) (by positivity)
  set A : ℝ := (y2.val : ℝ) / 2 ^ 72 with hA
  have y2R : (y2.val : ℝ) = ((y1.val / 2 ^ 40 : ℤ) : ℝ) := by
    rw [yv, ← h23]; exact_mod_cast Int.toNat_of_nonneg q0
  have dAY : |A - Y| ≤ 1 / 2 ^ 72 + 1 / 2 ^ 97 := by
    have ⟨fl1, fl2⟩ : ((y1.val / 2 ^ 40 : ℤ) : ℝ) ≤ (y1.val : ℝ) / 2 ^ 40 ∧
        (y1.val : ℝ) / 2 ^ 40 < ((y1.val / 2 ^ 40 : ℤ) : ℝ) + 1 := by
      have a := Int.ediv_mul_le y1.val (by norm_num : (2 : ℤ) ^ 40 ≠ 0)
      have b := Int.lt_ediv_add_one_mul_self y1.val (by norm_num : (0 : ℤ) < 2 ^ 40)
      constructor
      · rw [le_div_iff₀ (by positivity)]; exact_mod_cast a
      · rw [div_lt_iff₀ (by positivity)]; exact_mod_cast b
    rw [hA, y2R, Yr]
    have : ((y1.val / 2 ^ 40 : ℤ) : ℝ) / 2 ^ 72 - ((y1.val : ℝ) + j1.val * ((L : ℝ) - Real.log 2 * 2 ^ 104)) / 2 ^ 112 =
        (((y1.val / 2 ^ 40 : ℤ) : ℝ) - (y1.val : ℝ) / 2 ^ 40) / 2 ^ 72 -
          (j1.val * ((L : ℝ) - Real.log 2 * 2 ^ 104)) / 2 ^ 112 := by ring
    rw [this]
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 72)]
      exact div_le_div_of_nonneg_right (abs_le.mpr ⟨by linarith only [fl2], by linarith only [fl1]⟩) (by positivity)
    · rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 112), div_le_iff₀ (by positivity)]
      exact jL.trans (by norm_num)
  have es := exp_shift_near A Y _ dAY (by norm_num)
  have Ytop : (k.val : ℝ) / 256 * Real.log 2 + Y ≤ Real.log 2 + 1 / 2 ^ 90 := by
    have kk : (k.val : ℝ) ≤ 255 := by exact_mod_cast Nat.le_of_lt_succ k256
    have y1R : (y1.val : ℝ) < L := by exact_mod_cast y1L
    have Lu : (L : ℝ) ≤ Real.log 2 * 2 ^ 104 + 1 / 2 := by linarith only [(abs_le.mp eL).2]
    have jj := (abs_le.mp jL).2
    have a1 : Y ≤ (L + (2 ^ 15 + 1) * (1 / 2)) / 2 ^ 112 := by
      rw [Yr]; exact div_le_div_of_nonneg_right (by linarith only [y1R, jj]) (by positivity)
    have a2 : (k.val : ℝ) / 256 * Real.log 2 ≤ 255 / 256 * Real.log 2 :=
      mul_le_mul_of_nonneg_right (by linarith only [kk]) (by linarith only [log_two_ge'])
    have a3 : (L + (2 ^ 15 + 1) * (1 / 2) : ℝ) / 2 ^ 112 ≤ Real.log 2 / 256 + 1 / 2 ^ 90 := by
      rw [div_le_iff₀ (by positivity)]; linarith only [Lu]
    linarith only [a1, a2, a3]
  have T2 : (2 : ℝ) ^ ((k.val : ℝ) / 256) * Real.exp Y ≤ 2 + 1 / 2 ^ 80 := by
    rw [Real.rpow_def_of_pos two_pos, ← Real.exp_add]
    have z0 : |(1 : ℝ) / 2 ^ 90| ≤ 1 := by norm_num
    have := (abs_le.mp (Real.abs_exp_sub_one_le z0)).2
    calc Real.exp (Real.log 2 * ((k.val : ℝ) / 256) + Y) ≤ Real.exp (Real.log 2 + 1 / 2 ^ 90) :=
          Real.exp_le_exp.mpr (by linarith only [Ytop])
      _ = 2 * Real.exp (1 / 2 ^ 90) := by rw [Real.exp_add, Real.exp_log two_pos]
      _ ≤ 2 * (1 + 2 * |(1 : ℝ) / 2 ^ 90|) := by linarith only [this]
      _ ≤ 2 + 1 / 2 ^ 80 := by norm_num
  have T0 : (0 : ℝ) ≤ (2 : ℝ) ^ ((k.val : ℝ) / 256) := by positivity
  refine mantissa_round_near m.val n.val f.val _ mlt hf nle (by positivity) ?_ ?_
  · rw [sc, mul_assoc]
    calc (2 : ℝ) ^ ((k.val : ℝ) / 256) * (Real.exp Y * 2 ^ 126) = (2 : ℝ) ^ ((k.val : ℝ) / 256) * Real.exp Y * 2 ^ 126 := by ring
      _ ≤ (2 + 1 / 2 ^ 80) * 2 ^ 126 := mul_le_mul_of_nonneg_right T2 (by positivity)
      _ ≤ 2 ^ 128 := by norm_num
  rw [sc]
  calc |(m.val : ℝ) - (2 : ℝ) ^ ((k.val : ℝ) / 256) * Real.exp Y * 2 ^ 126|
      ≤ |(m.val : ℝ) - (2 : ℝ) ^ ((k.val : ℝ) / 256) * Real.exp A * 2 ^ 126| +
        |(2 : ℝ) ^ ((k.val : ℝ) / 256) * 2 ^ 126 * (Real.exp A - Real.exp Y)| := by
        rw [show (m.val : ℝ) - (2 : ℝ) ^ ((k.val : ℝ) / 256) * Real.exp Y * 2 ^ 126 =
          ((m.val : ℝ) - (2 : ℝ) ^ ((k.val : ℝ) / 256) * Real.exp A * 2 ^ 126) +
            (2 : ℝ) ^ ((k.val : ℝ) / 256) * 2 ^ 126 * (Real.exp A - Real.exp Y) by ring]
        exact abs_add_le _ _
    _ ≤ 81 / 100 * 2 ^ 56 + 2 ^ 126 * ((2 + 1 / 2 ^ 80) * ((1 + 1 / 2 ^ 60) * (1 / 2 ^ 72 + 1 / 2 ^ 97))) := by
        refine add_le_add hm ?_
        rw [abs_mul, abs_of_nonneg (by positivity), show (2 : ℝ) ^ ((k.val : ℝ) / 256) * 2 ^ 126 *
          |Real.exp A - Real.exp Y| = 2 ^ 126 * ((2 : ℝ) ^ ((k.val : ℝ) / 256) * |Real.exp A - Real.exp Y|) by ring]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc (2 : ℝ) ^ ((k.val : ℝ) / 256) * |Real.exp A - Real.exp Y|
            ≤ (2 : ℝ) ^ ((k.val : ℝ) / 256) * (Real.exp Y * ((1 + 1 / 2 ^ 60) * (1 / 2 ^ 72 + 1 / 2 ^ 97))) :=
              mul_le_mul_of_nonneg_left es T0
          _ = (2 : ℝ) ^ ((k.val : ℝ) / 256) * Real.exp Y * ((1 + 1 / 2 ^ 60) * (1 / 2 ^ 72 + 1 / 2 ^ 97)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right T2 (by positivity)
    _ ≤ 14 / 10 * 2 ^ 56 := by norm_num

end Fulcrum

end
