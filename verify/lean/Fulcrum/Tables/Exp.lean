module

public import Fulcrum.Tables.Trig
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The tables of `src/tables/exp.rs`, within half a unit

Every constant and every entry of `EXP2`, `LOG2` and `LOG2_WIDE`, as Aeneas
extracts them, is within `½` of the true value times `2^62`, `2^104` or `2^126`:
correctly rounded. `ln 2` comes from `log_two_near`; `2 / ln 2` and
`log₂ (1 + k/256) = log (1 + k/256) / ln 2` from a quotient of two near values
(`div_near`), the logarithm by the series of `log (1 + x) - log (1 - x)` at
`x = k / (512 + k)`; `2^(k/256) = exp (k/256 · ln 2)` by the series of `exp` at
`k · ln2Q / 256` and `|exp a - exp q| ≤ exp q · 2 |a - q|`.
-/

@[expose] public section

open Aeneas Aeneas.Std

namespace Fulcrum

/-- `ln 2 ≥ 0.69`. -/
theorem log_two_ge : (69 / 100 : ℝ) ≤ Real.log 2 := by
  have c := (Rat.cast_le (K := ℝ)).mpr (by decide +kernel : (69 / 100 : ℚ) ≤ ln2Q - 1 / 2 ^ 270)
  push_cast at c
  exact c.trans (sub_le_iff_le_add.mpr (neg_le_sub_iff_le_add.mp (abs_le.mp log_two_near).1))

/-- A quotient of values near `S` and `q`, both at least `0.69`, `|S| ≤ 2`. -/
theorem div_near (L l S q r e : ℝ) (hL : |L - S| ≤ r) (hl : |l - q| ≤ e) (hl0 : 69 / 100 ≤ l)
    (hq0 : 69 / 100 ≤ q) (hS : |S| ≤ 2) : |L / l - S / q| ≤ 2 * r + 5 * e := by
  have lp : 0 < l := (by norm_num : (0 : ℝ) < 69 / 100).trans_le hl0
  have qp : 0 < q := (by norm_num : (0 : ℝ) < 69 / 100).trans_le hq0
  have e1 : L / l - S / q = (L - S) / l + S * (q - l) / (l * q) := by field_simp; ring
  have r0 : 0 ≤ r := (abs_nonneg _).trans hL
  have e0 : 0 ≤ e := (abs_nonneg _).trans hl
  rw [e1]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_div, abs_of_pos lp, div_le_iff₀ lp]
    rw [mul_comm 2 r, mul_assoc]
    exact hL.trans (le_mul_of_one_le_right r0 ((by norm_num : (1 : ℝ) ≤ 2 * (69 / 100)).trans
      (mul_le_mul_of_nonneg_left hl0 zero_le_two)))
  · rw [abs_div, abs_mul, abs_of_pos (mul_pos lp qp), abs_sub_comm, div_le_iff₀ (mul_pos lp qp)]
    have lq : (69 / 100 : ℝ) * (69 / 100) ≤ l * q := mul_le_mul hl0 hq0 (by norm_num) lp.le
    calc |S| * |l - q| ≤ 2 * e := mul_le_mul hS hl (abs_nonneg _) zero_le_two
      _ ≤ 5 * e * ((69 / 100) * (69 / 100)) := by
        rw [mul_comm 5 e, mul_assoc, mul_comm 2 e]
        exact mul_le_mul_of_nonneg_left (by norm_num) e0
      _ ≤ 5 * e * (l * q) := mul_le_mul_of_nonneg_left lq (by positivity)

/-- `ln2Q ≥ 0.69`. -/
theorem ln2Q_ge : (69 / 100 : ℝ) ≤ ln2Q := by
  have c := (Rat.cast_le (K := ℝ)).mpr (by decide +kernel : (69 / 100 : ℚ) ≤ ln2Q)
  push_cast at c
  exact c

/-- `2 / ln 2` is within `5 · 2^-270` of `2 / ln2Q`. -/
theorem two_div_log_two_near : |2 / Real.log 2 - ((2 / ln2Q : ℚ) : ℝ)| ≤ ((5 / 2 ^ 270 : ℚ) : ℝ) := by
  have h := div_near 2 (Real.log 2) 2 ln2Q 0 (1 / 2 ^ 270) (by rw [sub_self, abs_zero])
    log_two_near log_two_ge ln2Q_ge (by rw [abs_two])
  push_cast
  rw [mul_zero, zero_add, mul_one_div] at h
  exact h

/-- `LN_2` is `ln 2 · 2^104` rounded to nearest. -/
theorem ln_2_entry : |(fulcrum.tables.exp.LN_2.val : ℝ) - Real.log 2 * 2 ^ 104| ≤ 1 / 2 :=
  entry_near _ 104 _ ln2Q (1 / 2 ^ 270) (by push_cast; exact log_two_near) (by decide +kernel)

/-- `TWO_LOG2_E` is `2 / ln 2 · 2^62` rounded to nearest. -/
theorem two_log2_e_entry :
    |(fulcrum.tables.exp.TWO_LOG2_E.val : ℝ) - 2 / Real.log 2 * 2 ^ 62| ≤ 1 / 2 :=
  entry_near _ 62 _ _ _ two_div_log_two_near (by decide +kernel)

/-- `TWO_LOG2_E_WIDE` is `2 / ln 2 · 2^126` rounded to nearest. -/
theorem two_log2_e_wide_entry :
    |(fulcrum.tables.exp.TWO_LOG2_E_WIDE.val : ℝ) - 2 / Real.log 2 * 2 ^ 126| ≤ 1 / 2 :=
  entry_near _ 126 _ _ _ two_div_log_two_near (by decide +kernel)

/-- `2^(k/256)` is within `expRem + 6 · 2^-270` of the series of `exp` at
`k · ln2Q / 256`, when that series is at most `3`. -/
theorem exp2_near (k : ℕ) (hk : k ≤ 256) (n : ℕ) (hq : |(k * ln2Q / 256 : ℚ)| < n + 1)
    (h3 : expSum (k * ln2Q / 256) n + expRem (k * ln2Q / 256) n ≤ 3) :
    |(2 : ℝ) ^ ((k : ℝ) / 256) - expSum (k * ln2Q / 256) n| ≤
      ((expRem (k * ln2Q / 256) n + 6 / 2 ^ 270 : ℚ) : ℝ) := by
  set q : ℚ := k * ln2Q / 256
  have b := exp_near q n hq
  have aq : |Real.log 2 * ((k : ℝ) / 256) - q| ≤ 1 / 2 ^ 270 := by
    have e : Real.log 2 * ((k : ℝ) / 256) - q = k / 256 * (Real.log 2 - ln2Q) := by
      simp only [q]; push_cast; ring
    rw [e, abs_mul, abs_of_nonneg (by positivity)]
    exact (mul_le_of_le_one_left (abs_nonneg _) ((div_le_one (by norm_num)).mpr
      (by exact_mod_cast hk))).trans log_two_near
  have eq3 : Real.exp q ≤ 3 := by
    have c := (Rat.cast_le (K := ℝ)).mpr h3
    push_cast at c
    exact (sub_le_iff_le_add'.mp ((le_abs_self _).trans b)).trans c
  have a1 : |Real.log 2 * ((k : ℝ) / 256) - q| ≤ 1 :=
    aq.trans (by rw [div_le_one (by positivity)]; exact one_le_pow₀ one_le_two)
  have d : |Real.exp (Real.log 2 * ((k : ℝ) / 256)) - Real.exp q| ≤ 6 / 2 ^ 270 := by
    rw [show Real.exp (Real.log 2 * ((k : ℝ) / 256)) - Real.exp q =
        Real.exp q * (Real.exp (Real.log 2 * ((k : ℝ) / 256) - q) - 1) by
      rw [mul_sub, ← Real.exp_add, add_sub_cancel, mul_one],
      abs_mul, abs_of_pos (Real.exp_pos _)]
    calc Real.exp q * |Real.exp (Real.log 2 * ((k : ℝ) / 256) - q) - 1|
        ≤ 3 * (2 * (1 / 2 ^ 270)) := mul_le_mul eq3 ((Real.abs_exp_sub_one_le a1).trans
          (mul_le_mul_of_nonneg_left aq zero_le_two)) (abs_nonneg _) (by norm_num)
      _ = 6 / 2 ^ 270 := by rw [← mul_assoc, mul_one_div, show (3 : ℝ) * 2 = 6 by norm_num]
  rw [Real.rpow_def_of_pos two_pos]
  push_cast
  exact (abs_sub_le _ _ _).trans ((add_le_add d b).trans_eq (add_comm _ _))

/-- `EXP2` is `2^(k/256) · 2^126` rounded to nearest at every `k < 256`. -/
theorem exp2_entry (k : ℕ) (hk : k < 256) :
    |((fulcrum.tables.exp.EXP2.val[k]!).val : ℝ) - (2 : ℝ) ^ ((k : ℝ) / 256) * 2 ^ 126| ≤ 1 / 2 := by
  have all : ∀ k : ℕ, k < 256 → (|(k * ln2Q / 256 : ℚ)| < 35 + 1 ∧
      expSum (k * ln2Q / 256) 35 + expRem (k * ln2Q / 256) 35 ≤ 3 ∧
      |((fulcrum.tables.exp.EXP2.val[k]!).val : ℚ) - expSum (k * ln2Q / 256) 35 * 2 ^ 126| +
        (expRem (k * ln2Q / 256) 35 + 6 / 2 ^ 270) * 2 ^ 126 ≤ 1 / 2) := by decide +kernel
  have ⟨hq, h3, h⟩ := all k hk
  exact entry_near _ 126 _ _ _ (exp2_near k (by omega) 35 (by exact_mod_cast hq) h3) h

/-- `log (1 + x) - log (1 - x) = log (1 + k/256)` at `x = k / (512 + k)`. -/
theorem log_artanh_point (k : ℕ) :
    Real.log (1 + ((k / (512 + k) : ℚ) : ℝ)) - Real.log (1 - ((k / (512 + k) : ℚ) : ℝ)) =
      Real.log (1 + (k : ℝ) / 256) := by
  have p : (0 : ℝ) < 512 + k := by positivity
  push_cast
  rw [← Real.log_div (by positivity)
    (sub_pos.mpr ((div_lt_one p).mpr (lt_add_of_pos_left _ (by norm_num)))).ne']
  congr 1
  field_simp
  ring

/-- `log₂ (1 + k/256)` is within `2 · logRem + 5 · 2^-270` of `logSum / ln2Q`. -/
theorem log2_near (k n : ℕ) (hx : |(k / (512 + k) : ℚ)| < 1) (hS : |logSum (k / (512 + k)) n| ≤ 2) :
    |Real.logb 2 (1 + (k : ℝ) / 256) - ((logSum (k / (512 + k)) n / ln2Q : ℚ) : ℝ)| ≤
      ((2 * logRem (k / (512 + k)) n + 5 / 2 ^ 270 : ℚ) : ℝ) := by
  have b := log_near _ n hx
  rw [log_artanh_point] at b
  have hS' : |((logSum (k / (512 + k)) n : ℚ) : ℝ)| ≤ 2 := by exact_mod_cast hS
  have h := div_near _ _ _ _ _ _ b log_two_near log_two_ge ln2Q_ge hS'
  rw [← Real.log_div_log]
  push_cast
  rw [mul_one_div] at h
  exact h

/-- `LOG2` is `log₂ (1 + k/256) · 2^62` rounded to nearest at every `k < 256`. -/
theorem log2_entry (k : ℕ) (hk : k < 256) :
    |((fulcrum.tables.exp.LOG2.val[k]!).val : ℝ) - Real.logb 2 (1 + (k : ℝ) / 256) * 2 ^ 62| ≤
      1 / 2 := by
  have all : ∀ k : ℕ, k < 256 → (|(k / (512 + k) : ℚ)| < 1 ∧ |logSum (k / (512 + k)) 30| ≤ 2 ∧
      |((fulcrum.tables.exp.LOG2.val[k]!).val : ℚ) - logSum (k / (512 + k)) 30 / ln2Q * 2 ^ 62| +
        (2 * logRem (k / (512 + k)) 30 + 5 / 2 ^ 270) * 2 ^ 62 ≤ 1 / 2) := by decide +kernel
  have ⟨hx, hS, h⟩ := all k hk
  exact entry_near _ 62 _ _ _ (log2_near k 30 hx hS) h

/-- `LOG2_WIDE` is `log₂ (1 + k/256) · 2^126` rounded to nearest at every `k < 256`. -/
theorem log2_wide_entry (k : ℕ) (hk : k < 256) :
    |((fulcrum.tables.exp.LOG2_WIDE.val[k]!).val : ℝ) - Real.logb 2 (1 + (k : ℝ) / 256) * 2 ^ 126| ≤
      1 / 2 := by
  have all : ∀ k : ℕ, k < 256 → (|(k / (512 + k) : ℚ)| < 1 ∧ |logSum (k / (512 + k)) 48| ≤ 2 ∧
      |((fulcrum.tables.exp.LOG2_WIDE.val[k]!).val : ℚ) - logSum (k / (512 + k)) 48 / ln2Q * 2 ^ 126| +
        (2 * logRem (k / (512 + k)) 48 + 5 / 2 ^ 270) * 2 ^ 126 ≤ 1 / 2) := by decide +kernel
  have ⟨hx, hS, h⟩ := all k hk
  exact entry_near _ 126 _ _ _ (log2_near k 48 hx hS) h

end Fulcrum

end
