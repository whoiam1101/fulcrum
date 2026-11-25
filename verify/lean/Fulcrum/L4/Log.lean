module

public import Fulcrum.L4.Angle
public import Fulcrum.Math.Log
public import Fulcrum.Tables.Exp

/-!
# L4: `exp::log2_unit`, `split_log2`, `log2`, `ln` (INTERNALS §3.16)

On the code extracted by Aeneas, with `raw > 0` and `f ≤ 32`.

- `log2_unit(U)` of a mantissa `2^62 ≤ U < 2^63` takes the point `C = 2^62 + k · 2^54`
  of the top 8 fractional bits, the exact quotient `s = ⌊(U - C) · 2^62 / (U + C)⌋` and the
  entry `k` of `LOG2`; the result is `log2N` of `Math/Log.lean`, within `7.6` units of
  `log₂ (U / 2^62) · 2^62` (`log2_split`: `(1 + σ)/(1 - σ) = U / C`).
- `split_log2` shifts `raw` to the mantissa by its exponent `e = ⌊log₂ raw⌋ ≤ 62`, exactly.
- `log2` rounds the mantissa part once and adds `(e - f) · 2^f`: within
  `½ + 7.6 / 2^(62 - f)` of `log₂ (raw / 2^f) · 2^f`.
- `ln` sums `(e - f) · LN_2` and the mantissa part times `⌊LN_2 / 2^40⌋` at 104 bits
  (`ln_part_near`, within `5.52 · 2^42`) and rounds once: within `½ + 5.6 / 2^(62 - f)`.
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace Fulcrum

set_option maxRecDepth 10000

/-- `tables::exp::FRAC` is `62`. -/
theorem exp_frac_val : fulcrum.tables.exp.FRAC.val = 62 := by
  unfold fulcrum.tables.exp.FRAC; rfl

/-- `tables::exp::STEPS` is `8`. -/
theorem exp_steps_val : fulcrum.tables.exp.STEPS.val = 8 := by
  unfold fulcrum.tables.exp.STEPS; rfl

/-- `exp::ONE` is `2^62`. -/
theorem exp_one_spec : fulcrum.exp.ONE ⦃ r => r.val = 2 ^ 62 ⦄ := by
  unfold fulcrum.exp.ONE
  refine WP.spec_mono (UScalar.ShiftLeft_spec 1#u64 fulcrum.tables.exp.FRAC _
    (by rw [exp_frac_val]; exact Nat.le_of_ble_eq_true rfl) rfl) fun r ⟨hr, _⟩ => ?_
  rw [hr, exp_frac_val, lit_val, Nat.shiftLeft_eq, one_mul, UScalar.size_def, UScalarTy.U64_numBits_eq]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right one_lt_two (Nat.le_of_ble_eq_true rfl))

/-- `exp::mul` is `⌊a · b / 2^62⌋` when the quotient fits `u64`. -/
theorem exp_mul_spec (a b : Std.U64) (h : a.val * b.val < 2 ^ 126) :
    fulcrum.exp.mul a b ⦃ r => r.val = mul62 a.val b.val ⦄ := by
  unfold fulcrum.exp.mul
  have ca : (UScalar.cast .U128 a).val = a.val :=
    UScalar.cast_val_mod_pow_greater_numBits_eq _ _ (Nat.le_of_ble_eq_true rfl)
  have cb : (UScalar.cast .U128 b).val = b.val :=
    UScalar.cast_val_mod_pow_greater_numBits_eq _ _ (Nat.le_of_ble_eq_true rfl)
  rw [lift, bind_ok, lift, bind_ok]
  refine WP.spec_bind (UScalar.mul_spec (x := UScalar.cast .U128 a) (y := UScalar.cast .U128 b)
    (by rw [ca, cb, U128_max_val]
        exact Nat.le_pred_of_lt (h.trans (Nat.pow_lt_pow_right one_lt_two (Nat.le_of_ble_eq_true rfl : 126 < 128)))))
    fun i hi => ?_
  refine WP.spec_bind (UScalar.ShiftRight_spec i fulcrum.tables.exp.FRAC
    (by rw [exp_frac_val]; exact Nat.le_of_ble_eq_true rfl)) fun j ⟨hj, _⟩ => ?_
  have jv : j.val = mul62 a.val b.val := by
    rw [hj, exp_frac_val, hi, ca, cb, Nat.shiftRight_eq_div_pow]; rfl
  rw [WP.spec_ok, UScalar.cast_val_mod_pow_of_inBounds_eq _ _ ?_, jv]
  rw [jv]
  exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 62)).mpr (h.trans_eq (by norm_num))

/-- `exp::mul` of operands at most `A`, `B` with `A · B < 2^126`. -/
theorem exp_mul_le_spec (a b : Std.U64) (A B : ℕ) (ha : a.val ≤ A) (hb : b.val ≤ B)
    (h : A * B < 2 ^ 126) : fulcrum.exp.mul a b ⦃ r => r.val = mul62 a.val b.val ⦄ :=
  exp_mul_spec a b ((Nat.mul_le_mul ha hb).trans_lt h)

/-- The value of `tables::exp::TWO_LOG2_E`. -/
theorem two_log2_e_val : fulcrum.tables.exp.TWO_LOG2_E.val = 13306513097844322492 := by
  unfold fulcrum.tables.exp.TWO_LOG2_E; rfl

/-- An entry `k < 256` of `LOG2`, read by `index_usize`: within `½` of
`log₂ (1 + k/256) · 2^62`, and at most `2^62`. -/
theorem log2_table_spec (i : Std.Usize) (hi : i.val < 256) :
    Array.index_usize fulcrum.tables.exp.LOG2 i ⦃ x =>
      |(x.val : ℝ) - Real.logb 2 (1 + (i.val : ℝ) / 256) * 2 ^ 62| ≤ 1 / 2 ∧ x.val ≤ 2 ^ 62 ⦄ := by
  have hl : i.val < fulcrum.tables.exp.LOG2.length := by
    rw [Array.length, fulcrum.tables.exp.LOG2.property]; exact hi
  refine WP.spec_mono (Array.index_usize_spec _ i hl) fun x hx => ?_
  have e := log2_entry i.val hi
  rw [getElem!_pos fulcrum.tables.exp.LOG2.val i.val
    (show i.val < fulcrum.tables.exp.LOG2.val.length from hl), ← hx] at e
  refine ⟨e, ?_⟩
  have lb : Real.logb 2 (1 + (i.val : ℝ) / 256) < 1 := by
    rw [Real.logb_lt_iff_lt_rpow (by norm_num) (by positivity), Real.rpow_one]
    have : (i.val : ℝ) < 256 := by exact_mod_cast hi
    linarith
  have u : (x.val : ℝ) < 2 ^ 62 + 1 := by
    have := (abs_le.mp e).2
    nlinarith
  exact Nat.lt_succ_iff.mp (by exact_mod_cast u)

/-- `log₂ c + (log (1 + σ) - log (1 - σ)) / ln 2 = log₂ (U / 2^62)` for
`σ = (U - C)/(U + C)`, `c = C / 2^62`, `0 < C ≤ U`. -/
theorem log2_split (U C : ℝ) (hC : 0 < C) (hCU : C ≤ U) :
    Real.logb 2 (C / 2 ^ 62) + (Real.log (1 + (U - C) / (U + C)) - Real.log (1 - (U - C) / (U + C))) / Real.log 2 =
      Real.logb 2 (U / 2 ^ 62) := by
  have hU : 0 < U := hC.trans_le hCU
  have d : U + C ≠ 0 := by positivity
  have e1 : 1 + (U - C) / (U + C) = 2 * U / (U + C) := by field_simp; ring
  have e2 : 1 - (U - C) / (U + C) = 2 * C / (U + C) := by field_simp; ring
  rw [e1, e2, Real.log_div (by positivity) d, Real.log_div (by positivity) d, Real.log_mul two_ne_zero hU.ne',
    Real.log_mul two_ne_zero hC.ne', Real.logb, Real.logb, Real.log_div hC.ne' (by positivity),
    Real.log_div hU.ne' (by positivity)]
  ring

/-- L4 on the code: `exp::log2_unit(U)` of `2^62 ≤ U < 2^63` never fails and is within
`7.6` units of `log₂ (U / 2^62) · 2^62`, at most `2^62 + 8`. -/
theorem log2_unit_spec (u : Std.U64) (hu : 2 ^ 62 ≤ u.val) (hu' : u.val < 2 ^ 63) :
    fulcrum.exp.log2_unit u ⦃ r =>
      |(r.val : ℝ) - Real.logb 2 (u.val / 2 ^ 62) * 2 ^ 62| ≤ 76 / 10 ∧ r.val ≤ 2 ^ 62 + 8 ⦄ := by
  have n128 : UScalarTy.U128.numBits = 128 := rfl
  have n64 : UScalarTy.U64.numBits = 64 := rfl
  unfold fulcrum.exp.log2_unit
  refine WP.spec_bind (UScalar.sub_spec (x := fulcrum.tables.exp.FRAC) (y := fulcrum.tables.exp.STEPS)
    (by rw [exp_frac_val, exp_steps_val]; norm_num)) fun i ⟨hi, _⟩ => ?_
  rw [exp_frac_val, exp_steps_val] at hi
  norm_num at hi
  refine WP.spec_bind (UScalar.ShiftRight_spec u i (by rw [hi, n64]; norm_num)) fun i1 ⟨h1, _⟩ => ?_
  rw [hi, Nat.shiftRight_eq_div_pow] at h1
  refine WP.spec_bind (UScalar.ShiftLeft_spec 1#u64 fulcrum.tables.exp.STEPS _
    (by rw [exp_steps_val, n64]; norm_num) rfl) fun i2 ⟨h2, _⟩ => ?_
  rw [exp_steps_val, lit_val, Nat.shiftLeft_eq, one_mul, UScalar.size_def, n64] at h2
  norm_num at h2
  have q1 : 256 ≤ i1.val := by rw [h1]; exact (Nat.le_div_iff_mul_le (by positivity)).mpr (by omega)
  have q2 : i1.val < 512 := by rw [h1, Nat.div_lt_iff_lt_mul (by positivity)]; omega
  refine WP.spec_bind (UScalar.sub_spec (x := i1) (y := i2) (by omega)) fun k ⟨hk, _⟩ => ?_
  have k256 : k.val < 256 := by omega
  refine WP.spec_bind (UScalar.ShiftLeft_spec k i _ (by rw [hi, n64]; norm_num) rfl) fun i3 ⟨h3, _⟩ => ?_
  rw [hi, Nat.shiftLeft_eq, UScalar.size_def, n64, Nat.mod_eq_of_lt (by omega)] at h3
  refine WP.spec_bind exp_one_spec fun i4 h4 => ?_
  refine WP.spec_bind (UScalar.add_spec (x := i4) (y := i3) (by rw [h4, h3, U64_max_val]; omega)) fun c hc => ?_
  have cv : c.val = 2 ^ 62 + k.val * 2 ^ 54 := by rw [hc, h4, h3]
  have Cle : c.val ≤ u.val := by
    rw [cv, hk, h1, h2]
    have := Nat.div_mul_le_self u.val (2 ^ 54)
    omega
  have rl : u.val - c.val < 2 ^ 54 := by
    rw [cv, hk, h1, h2]
    have := Nat.lt_div_mul_add (a := u.val) (b := 2 ^ 54) (by positivity)
    omega
  refine WP.spec_bind (UScalar.sub_spec (x := u) (y := c) Cle) fun i5 ⟨h5, _⟩ => ?_
  rw [lift, bind_ok]
  refine WP.spec_bind (UScalar.ShiftLeft_spec (UScalar.cast .U128 i5) fulcrum.tables.exp.FRAC _
    (by rw [exp_frac_val, n128]; norm_num) rfl) fun i7 ⟨h7, _⟩ => ?_
  have rb : i5.val * 2 ^ 62 < 2 ^ 128 := by
    rw [h5]
    calc (u.val - c.val) * 2 ^ 62 < 2 ^ 54 * 2 ^ 62 := Nat.mul_lt_mul_of_pos_right rl (by positivity)
      _ < 2 ^ 128 := by norm_num
  rw [cast_u128_val, exp_frac_val, Nat.shiftLeft_eq, UScalar.size_def, n128, Nat.mod_eq_of_lt rb] at h7
  refine WP.spec_bind (UScalar.add_spec (x := u) (y := c) (by rw [U64_max_val]; omega)) fun i8 h8 => ?_
  rw [lift, bind_ok]
  have dpos : 0 < (UScalar.cast .U128 i8).val := by rw [cast_u128_val, h8]; omega
  obtain ⟨s, es, hs⟩ := UScalar.div_spec i7 (y := UScalar.cast .U128 i8) dpos.ne'
  rw [es, bind_ok, lift, bind_ok]
  rw [cast_u128_val, h8, h7, h5] at hs
  have sl : s.val < 2 ^ 53 := by
    rw [hs, Nat.div_lt_iff_lt_mul (by omega)]
    calc (u.val - c.val) * 2 ^ 62 < 2 ^ 54 * 2 ^ 62 := Nat.mul_lt_mul_of_pos_right rl (by positivity)
      _ = 2 ^ 53 * 2 ^ 63 := by norm_num
      _ ≤ 2 ^ 53 * (u.val + c.val) := Nat.mul_le_mul_left _ (by omega)
  have s1v : (UScalar.cast .U64 s).val = s.val := by
    rw [cast_u64_val, Nat.mod_eq_of_lt (sl.trans (by norm_num))]
  generalize UScalar.cast .U64 s = s1 at s1v ⊢
  have s53 : s1.val ≤ 2 ^ 53 := by omega
  have zl : mul62 s1.val s1.val ≤ 2 ^ 44 :=
    Nat.div_le_of_le_mul ((Nat.mul_le_mul s53 s53).trans (by norm_num))
  refine WP.spec_bind (exp_mul_le_spec s1 s1 _ _ s53 s53 (by norm_num)) fun z hz => ?_
  refine WP.spec_bind (u64_div_spec i4 3#u64 3 (lit_val _ (by decide)) (by norm_num)) fun i10 h10 => ?_
  refine WP.spec_bind (u64_div_spec i4 5#u64 5 (lit_val _ (by decide)) (by norm_num)) fun i11 h11 => ?_
  rw [h4] at h10 h11
  refine WP.spec_bind (exp_mul_le_spec z i11 (2 ^ 44) (2 ^ 62) (hz ▸ zl) (by rw [h11]; omega) (by norm_num))
    fun i12 h12 => ?_
  rw [hz, h11] at h12
  have i12l : i12.val ≤ 2 ^ 44 := by rw [h12]; exact (mul62_le_left _ _ (by omega)).trans zl
  refine WP.spec_bind (UScalar.add_spec (x := i10) (y := i12) (by rw [U64_max_val, h10]; omega)) fun i13 h13 => ?_
  rw [h10, h12] at h13
  refine WP.spec_bind (exp_mul_le_spec z i13 (2 ^ 44) (2 ^ 62) (hz ▸ zl) (by rw [h13]; omega) (by norm_num))
    fun i14 h14 => ?_
  rw [hz, h13] at h14
  have i14l : i14.val ≤ 2 ^ 44 := by rw [h14]; exact (mul62_le_left _ _ (by omega)).trans zl
  refine WP.spec_bind (exp_mul_le_spec s1 i14 (2 ^ 53) (2 ^ 44) s53 i14l (by norm_num)) fun i15 h15 => ?_
  rw [h14] at h15
  have i15l : i15.val ≤ 2 ^ 53 := by rw [h15]; exact (mul62_le_left _ _ (by omega)).trans s53
  refine WP.spec_bind (UScalar.add_spec (x := s1) (y := i15) (by rw [U64_max_val]; omega)) fun sr hsr => ?_
  rw [lift, bind_ok]
  have ck := usize_cast_val k (by omega)
  refine WP.spec_bind (log2_table_spec _ (by rw [ck]; exact k256)) fun T ⟨hT, TU⟩ => ?_
  rw [ck] at hT
  have srl : sr.val ≤ 2 ^ 54 := by omega
  refine WP.spec_bind (exp_mul_le_spec sr fulcrum.tables.exp.TWO_LOG2_E (2 ^ 54) (2 ^ 64) srl
    (by rw [two_log2_e_val]; norm_num) (by norm_num)) fun i18 h18 => ?_
  have i18l : i18.val ≤ 2 ^ 56 := by
    rw [h18, two_log2_e_val]
    exact Nat.div_le_of_le_mul ((Nat.mul_le_mul srl (le_refl 13306513097844322492)).trans (by norm_num))
  refine WP.spec_mono (UScalar.add_spec (x := T) (y := i18) (by rw [U64_max_val]; omega)) fun r hr => ?_
  set σ : ℝ := ((u.val : ℝ) - c.val) / ((u.val : ℝ) + c.val) with hσ
  have Cp : (0 : ℝ) < c.val := by rw [cv]; positivity
  have CU : (c.val : ℝ) ≤ u.val := by exact_mod_cast Cle
  have σ0 : 0 ≤ σ := div_nonneg (by linarith) (by positivity)
  have σM : σ ≤ 1 / 512 := by
    rw [hσ, div_le_iff₀ (by positivity)]
    have : ((u.val - c.val : ℕ) : ℝ) < 2 ^ 54 := by exact_mod_cast rl
    rw [Nat.cast_sub Cle] at this
    have : (2 : ℝ) ^ 62 ≤ u.val := by exact_mod_cast hu
    have : (2 : ℝ) ^ 62 ≤ c.val := by exact_mod_cast (show 2 ^ 62 ≤ c.val by omega)
    linarith
  have ⟨fl, fu⟩ := floor_div_near ((u.val - c.val) * 2 ^ 62) (u.val + c.val) (by omega)
  rw [← hs] at fl fu
  rw [Nat.cast_mul, Nat.cast_sub Cle, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat] at fl fu
  have hsσ : (s1.val : ℝ) ≤ σ * 2 ^ 62 := by rw [s1v, hσ]; rw [div_mul_eq_mul_div]; exact fl
  have hsσ' : σ * 2 ^ 62 < s1.val + 1 := by rw [s1v, hσ, div_mul_eq_mul_div]; linarith
  have cR : (1 : ℝ) + (k.val : ℝ) / 256 = c.val / 2 ^ 62 := by rw [cv]; push_cast; field_simp; ring
  rw [cR] at hT
  have near := log2_series_near T.val s1.val fulcrum.tables.exp.TWO_LOG2_E.val _ σ hT two_log2_e_entry σ0 σM hsσ hsσ'
  rw [hσ, log2_split _ _ Cp CU] at near
  have rv : r.val = log2N T.val s1.val fulcrum.tables.exp.TWO_LOG2_E.val := by
    rw [hr, h18, hsr, h15]; rfl
  rw [rv]
  refine ⟨near, ?_⟩
  have lb : Real.logb 2 ((u.val : ℝ) / 2 ^ 62) < 1 := by
    rw [Real.logb_lt_iff_lt_rpow (by norm_num) (by positivity), Real.rpow_one, div_lt_iff₀ (by positivity)]
    have : (u.val : ℝ) < 2 ^ 63 := by exact_mod_cast hu'
    linarith
  have : (log2N T.val s1.val fulcrum.tables.exp.TWO_LOG2_E.val : ℝ) < 2 ^ 62 + 9 := by
    have := (abs_le.mp near).2; nlinarith
  have : log2N T.val s1.val fulcrum.tables.exp.TWO_LOG2_E.val < 2 ^ 62 + 9 := by exact_mod_cast this
  omega

/-- L4 on the code: `exp::split_log2(raw)` of `raw > 0` never fails and returns the exponent
`e = ⌊log₂ raw⌋` and `log2_unit` of the mantissa: within `7.6` units of
`log₂ (raw / 2^e) · 2^62`, at most `2^62 + 8`. -/
theorem split_log2_spec (raw : Std.I64) (hr : 0 < raw.val) :
    fulcrum.exp.split_log2 raw ⦃ p =>
      p.1.val = (Nat.log 2 raw.val.toNat : ℤ) ∧ Nat.log 2 raw.val.toNat ≤ 62 ∧
      |(p.2.val : ℝ) - Real.logb 2 ((raw.val : ℝ) / 2 ^ Nat.log 2 raw.val.toNat) * 2 ^ 62| ≤ 76 / 10 ∧
      p.2.val ≤ 2 ^ 62 + 8 ⦄ := by
  unfold fulcrum.exp.split_log2
  have ⟨_, ru⟩ := val_bounds raw IScalarTy.I64_numBits_eq
  rw [lift, bind_ok]
  have av : (IScalar.hcast .U64 raw).val = raw.val.toNat := by
    rw [IScalar.hcast_val_eq, UScalarTy.U64_numBits_eq, Int.emod_eq_of_lt hr.le (by omega)]
  generalize IScalar.hcast .U64 raw = a at av ⊢
  have a0 : a.val ≠ 0 := by omega
  set L := Nat.log 2 a.val with hL
  have hlo : 2 ^ L ≤ a.val := Nat.pow_log_le_self 2 a0
  have hhi : a.val < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two _
  have L62 : L ≤ 62 := by
    have : a.val < 2 ^ 63 := by omega
    exact Nat.le_of_lt_succ ((Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp (hlo.trans_lt this))
  have hlz : (core.num.U64.leading_zeros a).val = 64 - L - 1 := leading_zeros_val a a0 (Nat.le_of_ble_eq_true rfl)
  rw [lift, bind_ok]
  refine WP.spec_bind (UScalar.sub_spec (x := 63#u32) (y := core.num.U64.leading_zeros a)
    (by rw [hlz, lit_val]; omega)) fun e ⟨he, _⟩ => ?_
  rw [hlz, lit_val] at he
  have ev : e.val = L := by omega
  rw [lift, bind_ok]
  refine WP.spec_bind (UScalar.sub_spec (x := fulcrum.tables.exp.FRAC) (y := e)
    (by rw [exp_frac_val, ev]; exact L62)) fun i2 ⟨h2, _⟩ => ?_
  rw [exp_frac_val, ev] at h2
  have Ul : a.val * 2 ^ (62 - L) < 2 ^ 63 := by
    calc a.val * 2 ^ (62 - L) < 2 ^ (L + 1) * 2 ^ (62 - L) := Nat.mul_lt_mul_of_pos_right hhi (by positivity)
      _ = 2 ^ 63 := by rw [← pow_add]; congr 1; omega
  have Ug : 2 ^ 62 ≤ a.val * 2 ^ (62 - L) := by
    calc 2 ^ 62 = 2 ^ L * 2 ^ (62 - L) := by rw [← pow_add]; congr 1; omega
      _ ≤ a.val * 2 ^ (62 - L) := Nat.mul_le_mul_right _ hlo
  refine WP.spec_bind (UScalar.ShiftLeft_spec a i2 _ (by rw [h2, UScalarTy.U64_numBits_eq]; omega) rfl)
    fun i3 ⟨h3, _⟩ => ?_
  rw [h2, Nat.shiftLeft_eq, UScalar.size_def, UScalarTy.U64_numBits_eq, Nat.mod_eq_of_lt (Ul.trans (by norm_num))] at h3
  refine WP.spec_bind (log2_unit_spec i3 (h3 ▸ Ug) (h3 ▸ Ul)) fun l ⟨hl, lu⟩ => ?_
  rw [WP.spec_ok]
  dsimp only
  have ec : (UScalar.hcast .I64 e).val = (L : ℤ) := by
    rw [UScalar.hcast_val_eq, IScalarTy.I64_numBits_eq, ev]
    exact Int.bmod_eq_of_le (by push_cast; omega) (by push_cast; omega)
  rw [← av]
  refine ⟨ec, L62, ?_, lu⟩
  rw [h3] at hl
  have e2 : ((a.val * 2 ^ (62 - L) : ℕ) : ℝ) / 2 ^ 62 = ((a.val : ℤ) : ℝ) / 2 ^ L := by
    have : (2 : ℝ) ^ 62 = 2 ^ (62 - L) * 2 ^ L := by rw [← pow_add]; congr 1; omega
    rw [this]; push_cast; field_simp
  have araw : ((raw.val : ℤ) : ℝ) = ((a.val : ℤ) : ℝ) := by
    have t : ((raw.val.toNat : ℕ) : ℤ) = raw.val := Int.toNat_of_nonneg hr.le
    rw [av, t]
  rw [araw, ← e2]
  exact hl

/-- `log₂ (x / 2^n) = log₂ x - n` for `x > 0`. -/
theorem logb2_div_pow (x : ℝ) (hx : 0 < x) (n : ℕ) : Real.logb 2 (x / 2 ^ n) = Real.logb 2 x - n := by
  rw [Real.logb_div hx.ne' (by positivity), Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one]

/-- L4 on the code: `exp::log2(raw, f)` of `raw > 0`, `f ≤ 32`, never fails and is within
`½ + 7.6 / 2^(62 - f)` of `log₂ (raw / 2^f) · 2^f`. -/
theorem log2_spec (raw : Std.I64) (f : Std.U32) (hr : 0 < raw.val) (hf : f.val ≤ 32) :
    fulcrum.exp.log2 raw f ⦃ r =>
      |(r.val : ℝ) - Real.logb 2 ((raw.val : ℝ) / 2 ^ f.val) * 2 ^ f.val| ≤ 1 / 2 + 76 / 10 / 2 ^ (62 - f.val) ⦄ := by
  unfold fulcrum.exp.log2
  refine WP.spec_bind (split_log2_spec raw hr) fun p ⟨he, L62, hl, lu⟩ => ?_
  obtain ⟨e, l⟩ := p
  dsimp only at he hl lu ⊢
  set L := Nat.log 2 raw.val.toNat
  refine WP.spec_bind (Pₘ := fun x => x = UScalar.hcast .I128 l) (by rw [lift, WP.spec_ok]) fun i hi => ?_
  subst hi
  have hc : (UScalar.hcast .I128 l).val = l.val := by
    rw [UScalar.hcast_val_eq, IScalarTy.I128_numBits_eq]
    exact Int.bmod_eq_of_le ((neg_nonpos.mpr (by positivity)).trans (Int.natCast_nonneg _))
      ((by exact_mod_cast lu : (l.val : ℤ) ≤ 2 ^ 62 + 8).trans_lt (by norm_num))
  refine WP.spec_bind (UScalar.sub_spec (x := fulcrum.tables.exp.FRAC) (y := f)
    (by rw [exp_frac_val]; omega)) fun i1 ⟨h1, _⟩ => ?_
  rw [exp_frac_val] at h1
  refine WP.spec_bind (shr_round_spec _ i1) fun i2 h2 => ?_
  rw [hc, h1] at h2
  set S := Real.logb 2 ((raw.val : ℝ) / 2 ^ L) with hS
  have near := round_shift_near l.val (62 - f.val) f.val (by omega) S (76 / 10) (by exact_mod_cast hl)
  rw [← h2] at near
  have rawp : (0 : ℝ) < raw.val := by exact_mod_cast hr
  have S0 : 0 ≤ S := by
    rw [hS, logb2_div_pow _ rawp]
    have : (2 : ℝ) ^ L ≤ raw.val := by
      have := Nat.pow_log_le_self 2 (show raw.val.toNat ≠ 0 by omega)
      have t : ((raw.val.toNat : ℕ) : ℝ) = raw.val := by exact_mod_cast Int.toNat_of_nonneg hr.le
      rw [← t]; exact_mod_cast this
    have := Real.logb_le_logb_of_le (b := 2) one_lt_two (by positivity) this
    rw [Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one] at this
    linarith
  have S1 : S ≤ 1 := by
    rw [hS, logb2_div_pow _ rawp]
    have : (raw.val : ℝ) ≤ 2 ^ (L + 1) := by
      have := (Nat.lt_pow_succ_log_self Nat.one_lt_two raw.val.toNat).le
      have t : ((raw.val.toNat : ℕ) : ℝ) = raw.val := by exact_mod_cast Int.toNat_of_nonneg hr.le
      rw [← t]; exact_mod_cast this
    have := Real.logb_le_logb_of_le (b := 2) one_lt_two rawp this
    rw [Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one] at this
    push_cast at this; linarith
  have err : 1 / 2 + 76 / 10 / 2 ^ (62 - f.val) ≤ (9 : ℝ) :=
    (add_le_add le_rfl (div_le_self (by norm_num) (one_le_pow₀ one_le_two))).trans (by norm_num)
  have pf : (2 : ℝ) ^ f.val ≤ 2 ^ 32 := pow_le_pow_right₀ one_le_two hf
  have ib : 0 ≤ (i2.val : ℝ) + 9 ∧ (i2.val : ℝ) ≤ 2 ^ 32 + 9 := by
    have ⟨a1, a2⟩ := abs_le.mp (near.trans err)
    have m0 : 0 ≤ S * 2 ^ f.val := mul_nonneg S0 (by positivity)
    have m1 : S * 2 ^ f.val ≤ 1 * 2 ^ 32 := mul_le_mul S1 pf (by positivity) zero_le_one
    constructor <;> linarith
  have i2l : -9 ≤ i2.val ∧ i2.val ≤ 2 ^ 32 + 9 := ⟨by have := ib.1; exact_mod_cast (by linarith : (-9 : ℝ) ≤ i2.val),
    by exact_mod_cast ib.2⟩
  have inr : InRange 63 i2.val :=
    ⟨(by unfold minOf; norm_num : minOf 63 ≤ -9).trans i2l.1, i2l.2.trans (by unfold maxOf; norm_num)⟩
  have cv : (IScalar.cast .I64 i2).val = i2.val :=
    (IScalar.cast_val_eq .I64 i2).trans ((wrap_eq_self_iff 63 _).2 inr)
  rw [lift, bind_ok, lift, bind_ok]
  have fc : (UScalar.hcast .I64 f).val = (f.val : ℤ) := by
    rw [UScalar.hcast_val_eq, IScalarTy.I64_numBits_eq]
    exact Int.bmod_eq_of_le (by push_cast; omega) (by push_cast; omega)
  have mn : IScalar.min .I64 = -2 ^ 63 := min_eq_neg_pow IScalarTy.I64_numBits_eq
  have mx : IScalar.max .I64 = 2 ^ 63 - 1 := max_eq_pow_sub_one IScalarTy.I64_numBits_eq
  refine WP.spec_bind (IScalar.sub_spec (x := e) (y := UScalar.hcast .I64 f) (by rw [he, fc, mn]; omega)
    (by rw [he, fc, mx]; omega)) fun i4 h4 => ?_
  rw [he, fc] at h4
  refine WP.spec_bind (IScalar.ShiftLeft_spec i4 f (by rw [IScalarTy.I64_numBits_eq]; omega)) fun i5 ⟨h5, _⟩ => ?_
  have p32 : (2 : ℤ) ^ f.val ≤ 2 ^ 32 := pow_le_pow_right₀ (by norm_num) hf
  have pp : (0 : ℤ) < 2 ^ f.val := by positivity
  have i5v : i5.val = ((L : ℤ) - f.val) * 2 ^ f.val := by
    rw [h5, Int.shiftLeft_eq, h4, IScalarTy.I64_numBits_eq]
    have lb : -(32 : ℤ) * 2 ^ 32 ≤ ((L : ℤ) - f.val) * 2 ^ f.val := by nlinarith
    have ub : ((L : ℤ) - f.val) * 2 ^ f.val ≤ 62 * 2 ^ 32 := by nlinarith
    exact Int.bmod_eq_of_le (by push_cast; omega) (by push_cast; omega)
  refine WP.spec_mono (IScalar.add_spec (x := i5) (y := IScalar.cast .I64 i2)
    (by rw [i5v, cv, mn]; nlinarith) (by rw [i5v, cv, mx]; nlinarith)) fun r hr' => ?_
  rw [hr', i5v, cv]
  have tgt : Real.logb 2 ((raw.val : ℝ) / 2 ^ f.val) * 2 ^ f.val = ((L : ℝ) - f.val) * 2 ^ f.val + S * 2 ^ f.val := by
    rw [hS, logb2_div_pow _ rawp, logb2_div_pow _ rawp]; ring
  rw [tgt]
  push_cast
  rw [show ((L : ℝ) - f.val) * 2 ^ f.val + (i2.val : ℝ) - (((L : ℝ) - f.val) * 2 ^ f.val + S * 2 ^ f.val) =
    (i2.val : ℝ) - S * 2 ^ f.val by ring]
  exact near

/-- `tables::exp::LN_2_FRAC` is `104`. -/
theorem ln_2_frac_val : fulcrum.tables.exp.LN_2_FRAC.val = 104 := by
  unfold fulcrum.tables.exp.LN_2_FRAC; rfl

/-- The value of `tables::exp::LN_2`. -/
theorem ln_2_val : fulcrum.tables.exp.LN_2.val = 14058695031733113177892216608772 := by
  unfold fulcrum.tables.exp.LN_2; rfl

/-- The mantissa part of `exp::ln`: `⌊l · ⌊LN_2 / 2^40⌋ / 2^22⌋` for `l` within `7.6` of
`S · 2^62`, `0 ≤ S ≤ 1`, is within `5.52 · 2^42` of `S · ln 2 · 2^104`. -/
theorem ln_part_near (l : ℕ) (S : ℝ) (hS0 : 0 ≤ S) (hS1 : S ≤ 1) (hl : |(l : ℝ) - S * 2 ^ 62| ≤ 76 / 10) :
    |((l * (fulcrum.tables.exp.LN_2.val / 2 ^ 40) / 2 ^ 22 : ℕ) : ℝ) - S * Real.log 2 * 2 ^ 104| ≤
      552 / 100 * 2 ^ 42 := by
  have hL := ln_2_entry
  have l1 := log_two_le'
  have l0 := log_two_ge'
  set lam := fulcrum.tables.exp.LN_2.val / 2 ^ 40 with hlam
  have ⟨fl, fu⟩ := floor_div_near fulcrum.tables.exp.LN_2.val (2 ^ 40) (by positivity)
  rw [← hlam] at fl fu
  push_cast at fl fu
  have elam : |(lam : ℝ) - Real.log 2 * 2 ^ 64| ≤ 1001 / 1000 := by
    have : |(fulcrum.tables.exp.LN_2.val : ℝ) / 2 ^ 40 - Real.log 2 * 2 ^ 64| ≤ 1 / 2 / 2 ^ 40 := by
      rw [show (fulcrum.tables.exp.LN_2.val : ℝ) / 2 ^ 40 - Real.log 2 * 2 ^ 64 =
        ((fulcrum.tables.exp.LN_2.val : ℝ) - Real.log 2 * 2 ^ 104) / 2 ^ 40 by ring, abs_div,
        abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 40)]
      exact div_le_div_of_nonneg_right hL (by positivity)
    have ⟨a, b⟩ := abs_le.mp this
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  have lamM : (lam : ℝ) ≤ 6932 / 10000 * 2 ^ 64 := by nlinarith [(abs_le.mp elam).2]
  have ⟨pl, pu⟩ := floor_div_near (l * lam) (2 ^ 22) (by positivity)
  push_cast at pl pu
  have core : |(l : ℝ) * lam / 2 ^ 22 - S * Real.log 2 * 2 ^ 104| ≤ 5519 / 1000 * 2 ^ 42 := by
    rw [show (l : ℝ) * lam / 2 ^ 22 - S * Real.log 2 * 2 ^ 104 =
      (((l : ℝ) - S * 2 ^ 62) * lam + S * 2 ^ 62 * ((lam : ℝ) - Real.log 2 * 2 ^ 64)) / 2 ^ 22 by ring,
      abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 22), div_le_iff₀ (by positivity)]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) lam), abs_of_nonneg (by positivity : (0 : ℝ) ≤ S * 2 ^ 62)]
    have t1 : |(l : ℝ) - S * 2 ^ 62| * (lam : ℝ) ≤ 76 / 10 * (6932 / 10000 * 2 ^ 64) :=
      mul_le_mul hl lamM (Nat.cast_nonneg _) (by norm_num)
    have t2 : S * 2 ^ 62 * |(lam : ℝ) - Real.log 2 * 2 ^ 64| ≤ 2 ^ 62 * (1001 / 1000) :=
      mul_le_mul (by nlinarith) elam (abs_nonneg _) (by positivity)
    nlinarith
  have ⟨cl, cu⟩ := abs_le.mp core
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

/-- L4 on the code: `exp::ln(raw, f)` of `raw > 0`, `f ≤ 32`, never fails and is within
`½ + 5.6 / 2^(62 - f)` of `ln (raw / 2^f) · 2^f`. -/
theorem ln_spec (raw : Std.I64) (f : Std.U32) (hr : 0 < raw.val) (hf : f.val ≤ 32) :
    fulcrum.exp.ln raw f ⦃ r =>
      |(r.val : ℝ) - Real.log ((raw.val : ℝ) / 2 ^ f.val) * 2 ^ f.val| ≤ 1 / 2 + 56 / 10 / 2 ^ (62 - f.val) ⦄ := by
  have n128 : UScalarTy.U128.numBits = 128 := rfl
  unfold fulcrum.exp.ln
  refine WP.spec_bind (split_log2_spec raw hr) fun p ⟨he, L62, hl, lu⟩ => ?_
  obtain ⟨e, l⟩ := p
  dsimp only at he hl lu ⊢
  set L := Nat.log 2 raw.val.toNat
  have fc : (UScalar.hcast .I64 f).val = (f.val : ℤ) := by
    rw [UScalar.hcast_val_eq, IScalarTy.I64_numBits_eq]
    exact Int.bmod_eq_of_le (by push_cast; omega) (by push_cast; omega)
  refine WP.spec_bind (Pₘ := fun x => x = UScalar.hcast .I64 f) (by rw [lift, WP.spec_ok]) fun i hi => ?_
  subst hi
  have mn : IScalar.min .I64 = -2 ^ 63 := min_eq_neg_pow IScalarTy.I64_numBits_eq
  have mx : IScalar.max .I64 = 2 ^ 63 - 1 := max_eq_pow_sub_one IScalarTy.I64_numBits_eq
  refine WP.spec_bind (IScalar.sub_spec (x := e) (y := UScalar.hcast .I64 f) (by rw [he, fc, mn]; omega)
    (by rw [he, fc, mx]; omega)) fun i1 h1 => ?_
  rw [he, fc] at h1
  rw [lift, bind_ok, lift, bind_ok]
  have Lc : (UScalar.hcast .I128 fulcrum.tables.exp.LN_2).val = (fulcrum.tables.exp.LN_2.val : ℤ) := by
    rw [UScalar.hcast_val_eq, IScalarTy.I128_numBits_eq, ln_2_val]; decide
  have mn2 : IScalar.min .I128 = -2 ^ 127 := min_eq_neg_pow IScalarTy.I128_numBits_eq
  have mx2 : IScalar.max .I128 = 2 ^ 127 - 1 := max_eq_pow_sub_one IScalarTy.I128_numBits_eq
  have wb : |((L : ℤ) - f.val) * (fulcrum.tables.exp.LN_2.val : ℤ)| ≤ 62 * 2 ^ 104 := by
    rw [abs_mul, ln_2_val]
    exact mul_le_mul (abs_le.mpr ⟨by omega, by omega⟩) (by norm_num) (by positivity) (by norm_num)
  refine WP.spec_bind (IScalar.mul_spec (x := IScalar.cast .I128 i1) (y := UScalar.hcast .I128 fulcrum.tables.exp.LN_2)
    (by rw [cast_i128_val, h1, Lc, mn2]; have := (abs_le.mp wb).1; omega)
    (by rw [cast_i128_val, h1, Lc, mx2]; have := (abs_le.mp wb).2; omega)) fun whole hw => ?_
  rw [cast_i128_val, h1, Lc] at hw
  rw [lift, bind_ok]
  refine WP.spec_bind (UScalar.sub_spec (x := fulcrum.tables.exp.LN_2_FRAC) (y := 64#u32)
    (by rw [ln_2_frac_val, lit_val]; norm_num)) fun i5 ⟨h5, _⟩ => ?_
  rw [ln_2_frac_val, lit_val] at h5
  refine WP.spec_bind (UScalar.ShiftRight_spec fulcrum.tables.exp.LN_2 i5 (by rw [h5, n128]; norm_num)) fun i6 ⟨h6, _⟩ => ?_
  rw [h5, Nat.shiftRight_eq_div_pow, show (104 - 64 : ℕ) = 40 from rfl] at h6
  have i6l : i6.val < 2 ^ 64 := by rw [h6, ln_2_val]; norm_num
  refine WP.spec_bind (UScalar.mul_spec (x := UScalar.cast .U128 l) (y := i6) (by
    rw [cast_u128_val, U128_max_val]
    calc l.val * i6.val ≤ (2 ^ 62 + 8) * 2 ^ 64 := Nat.mul_le_mul lu i6l.le
      _ ≤ 2 ^ 128 - 1 := by norm_num)) fun i7 h7 => ?_
  rw [cast_u128_val] at h7
  refine WP.spec_bind (UScalar.add_spec (x := fulcrum.tables.exp.FRAC) (y := 64#u32)
    (by rw [exp_frac_val, lit_val, U32_max_val]; norm_num)) fun i8 h8 => ?_
  rw [exp_frac_val, lit_val] at h8
  refine WP.spec_bind (UScalar.sub_spec (x := i8) (y := fulcrum.tables.exp.LN_2_FRAC)
    (by rw [h8, ln_2_frac_val]; norm_num)) fun i9 ⟨h9, _⟩ => ?_
  rw [h8, ln_2_frac_val] at h9
  refine WP.spec_bind (UScalar.ShiftRight_spec i7 i9 (by rw [h9, n128]; norm_num)) fun i10 ⟨h10, _⟩ => ?_
  rw [h9, Nat.shiftRight_eq_div_pow, h7, h6, show (62 + 64 - 104 : ℕ) = 22 from rfl] at h10
  have i10l : i10.val < 2 ^ 106 := by
    rw [h10, Nat.div_lt_iff_lt_mul (by positivity)]
    calc l.val * (fulcrum.tables.exp.LN_2.val / 2 ^ 40) < (2 ^ 62 + 9) * 2 ^ 64 :=
          Nat.mul_lt_mul_of_le_of_lt (by omega) (by rw [ln_2_val]; norm_num) (by positivity)
      _ ≤ 2 ^ 106 * 2 ^ 22 := by norm_num
  rw [lift, bind_ok]
  have pc : (UScalar.hcast .I128 i10).val = (i10.val : ℤ) := by
    rw [UScalar.hcast_val_eq, IScalarTy.I128_numBits_eq]
    exact Int.bmod_eq_of_le ((neg_nonpos.mpr (by positivity)).trans (Int.natCast_nonneg _))
      ((by exact_mod_cast i10l : (i10.val : ℤ) < 2 ^ 106).trans_le (by norm_num))
  refine WP.spec_bind (IScalar.add_spec (x := whole) (y := UScalar.hcast .I128 i10)
    (by rw [hw, pc, mn2]; have := (abs_le.mp wb).1; omega)
    (by rw [hw, pc, mx2]; have := (abs_le.mp wb).2; omega)) fun i11 h11 => ?_
  rw [hw, pc] at h11
  refine WP.spec_bind (UScalar.sub_spec (x := fulcrum.tables.exp.LN_2_FRAC) (y := f)
    (by rw [ln_2_frac_val]; omega)) fun i12 ⟨h12, _⟩ => ?_
  rw [ln_2_frac_val] at h12
  refine WP.spec_bind (shr_round_spec i11 i12) fun i13 h13 => ?_
  rw [h12] at h13
  set S := Real.logb 2 ((raw.val : ℝ) / 2 ^ L) with hS
  have rawp : (0 : ℝ) < raw.val := by exact_mod_cast hr
  have tR : ((raw.val.toNat : ℕ) : ℝ) = raw.val := by exact_mod_cast Int.toNat_of_nonneg hr.le
  have S0 : 0 ≤ S := by
    rw [hS, logb2_div_pow _ rawp]
    have : (2 : ℝ) ^ L ≤ raw.val := by
      rw [← tR]; exact_mod_cast Nat.pow_log_le_self 2 (show raw.val.toNat ≠ 0 by omega)
    have := Real.logb_le_logb_of_le (b := 2) one_lt_two (by positivity) this
    rw [Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one] at this
    linarith
  have S1 : S ≤ 1 := by
    rw [hS, logb2_div_pow _ rawp]
    have : (raw.val : ℝ) ≤ 2 ^ (L + 1) := by
      rw [← tR]; exact_mod_cast (Nat.lt_pow_succ_log_self Nat.one_lt_two raw.val.toNat).le
    have := Real.logb_le_logb_of_le (b := 2) one_lt_two rawp this
    rw [Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one] at this
    push_cast at this; linarith
  have part := ln_part_near l.val S S0 S1 hl
  rw [← h10] at part
  set X := Real.log ((raw.val : ℝ) / 2 ^ f.val) with hX
  have Xe : X = ((L : ℝ) - f.val + S) * Real.log 2 := by
    rw [hX, hS, logb2_div_pow _ rawp, ← Real.log_div_log, Real.log_div rawp.ne' (by positivity), Real.log_pow]
    field_simp; ring
  have l0 := log_two_ge'
  have l1 := log_two_le'
  have kf : 104 - f.val + f.val = 104 := by omega
  have near := round_div_near i11.val (104 - f.val) (X * 2 ^ f.val) (552 / 100 * 2 ^ 42 + 47) (by
    rw [h11, mul_assoc, ← pow_add, show f.val + (104 - f.val) = 104 by omega, Xe]
    push_cast
    rw [show ((L : ℝ) - f.val) * fulcrum.tables.exp.LN_2.val + i10.val - ((L : ℝ) - f.val + S) * Real.log 2 * 2 ^ 104 =
      ((L : ℝ) - f.val) * ((fulcrum.tables.exp.LN_2.val : ℝ) - Real.log 2 * 2 ^ 104) +
        ((i10.val : ℝ) - S * Real.log 2 * 2 ^ 104) by ring]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
    have : |(L : ℝ) - f.val| * |(fulcrum.tables.exp.LN_2.val : ℝ) - Real.log 2 * 2 ^ 104| ≤ 94 * (1 / 2) :=
      mul_le_mul (abs_le.mpr ⟨by linarith [(show (L : ℝ) ≥ 0 by positivity),
        (show (f.val : ℝ) ≤ 32 by exact_mod_cast hf)], by
          have : (L : ℝ) ≤ 62 := by exact_mod_cast L62
          linarith [(show (f.val : ℝ) ≥ 0 by positivity)]⟩) ln_2_entry (abs_nonneg _) (by norm_num)
    linarith)
  rw [← h13] at near
  have eb : (552 / 100 * 2 ^ 42 + 47 : ℝ) / 2 ^ (104 - f.val) ≤ 56 / 10 / 2 ^ (62 - f.val) := by
    have : (2 : ℝ) ^ (104 - f.val) = 2 ^ (62 - f.val) * 2 ^ 42 := by rw [← pow_add]; congr 1; omega
    rw [this, div_le_div_iff₀ (by positivity) (by positivity)]
    have : (0 : ℝ) < 2 ^ (62 - f.val) := by positivity
    nlinarith
  have bound := near.trans (add_le_add le_rfl eb)
  have Xb : |X * 2 ^ f.val| ≤ 2 ^ 38 := by
    rw [Xe, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ f.val), abs_of_pos (by linarith : 0 < Real.log 2)]
    have h1 : |(L : ℝ) - f.val + S| ≤ 64 := by
      have : (L : ℝ) ≤ 62 := by exact_mod_cast L62
      have : (f.val : ℝ) ≤ 32 := by exact_mod_cast hf
      exact abs_le.mpr ⟨by linarith [(show (L : ℝ) ≥ 0 by positivity)], by linarith [(show (f.val : ℝ) ≥ 0 by positivity)]⟩
    have pf : (2 : ℝ) ^ f.val ≤ 2 ^ 32 := pow_le_pow_right₀ one_le_two hf
    calc |(L : ℝ) - f.val + S| * Real.log 2 * 2 ^ f.val ≤ 64 * 1 * 2 ^ 32 :=
          mul_le_mul (mul_le_mul h1 (by linarith) (by linarith) (by norm_num)) pf (by positivity) (by norm_num)
      _ ≤ 2 ^ 38 := by norm_num
  have err : 1 / 2 + 56 / 10 / 2 ^ (62 - f.val) ≤ (7 : ℝ) :=
    (add_le_add le_rfl (div_le_self (by norm_num) (one_le_pow₀ one_le_two))).trans (by norm_num)
  have ib : |(i13.val : ℝ)| ≤ 2 ^ 39 := by
    have := (abs_sub_abs_le_abs_sub (i13.val : ℝ) (X * 2 ^ f.val)).trans (bound.trans err)
    linarith
  have ib' : -(2 ^ 39) ≤ i13.val ∧ i13.val ≤ 2 ^ 39 := by
    have ⟨a, b⟩ := abs_le.mp ib
    exact ⟨by exact_mod_cast a, by exact_mod_cast b⟩
  have inr : InRange 63 i13.val :=
    ⟨(by unfold minOf; norm_num : minOf 63 ≤ -(2 ^ 39)).trans ib'.1, ib'.2.trans (by unfold maxOf; norm_num)⟩
  have cv : (IScalar.cast .I64 i13).val = i13.val :=
    (IScalar.cast_val_eq .I64 i13).trans ((wrap_eq_self_iff 63 _).2 inr)
  rw [WP.spec_ok, cv]
  exact bound

end Fulcrum

end
