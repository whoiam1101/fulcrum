module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Fulcrum.Math.Series

/-!
# `π` and `ln 2` to `2^-270`

The tables of `src/tables/trig.rs` and `src/tables/exp.rs` hold `π`, `2/π` and
`ln 2` to up to 192 bits, so the `20` digits of `π` and `10` of `ln 2` in
Mathlib are not enough. `π` comes from Machin's formula
`π = 16 arctan (1/5) - 4 arctan (1/239)` with 60 and 18 terms of the series,
`ln 2 = log (1 + 1/3) - log (1 - 1/3)` with 87 terms; the kernel checks the
rational sums (`decide +kernel`). `entry_near` turns such a rational bound into the bound of
a table entry, for the tables of trig and exp alike.
-/

@[expose] public section

namespace Fulcrum

/-- `16 x - 4 y` with `x`, `y` within `r`, `q` of `s`, `t` is within `e` of `p`
when `16 s - 4 t` is within `e - 16 r - 4 q` of it. -/
theorem machin_combine (x y s t p r q e : ℝ) (hx : |x - s| ≤ r) (hy : |y - t| ≤ q)
    (h : |16 * s - 4 * t - p| + 16 * r + 4 * q ≤ e) : |16 * x - 4 * y - p| ≤ e := by
  have k : 16 * x - 4 * y - p = 16 * (x - s) - 4 * (y - t) + (16 * s - 4 * t - p) := by ring
  rw [k]
  have a : |16 * (x - s) - 4 * (y - t)| ≤ 16 * r + 4 * q := (abs_sub _ _).trans (by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 16),
      abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    exact add_le_add (mul_le_mul_of_nonneg_left hx (by norm_num))
      (mul_le_mul_of_nonneg_left hy (by norm_num)))
  have h' : 16 * r + 4 * q + |16 * s - 4 * t - p| ≤ e := by rw [add_comm, ← add_assoc]; exact h
  exact (abs_add_le _ _).trans ((add_le_add a le_rfl).trans h')

/-- `π · 2^270` rounded to nearest, over `2^270`. -/
def piQ : ℚ :=
  5960033515794699457007369302470326069713197094148381572444522923916310846933979466 / 2 ^ 270

/-- `piQ` is within `2^-270` of `π`. -/
theorem pi_near : |Real.pi - piQ| ≤ 1 / 2 ^ 270 := by
  have c5 : ((1 / 5 : ℚ) : ℝ) = 5⁻¹ := by push_cast; exact one_div 5
  have c239 : ((1 / 239 : ℚ) : ℝ) = 239⁻¹ := by push_cast; exact one_div 239
  have h5 := arctan_near (1 / 5) 60 (by decide +kernel)
  have h239 := arctan_near (1 / 239) 18 (by decide +kernel)
  rw [c5] at h5
  rw [c239] at h239
  have key : |16 * atanSum (1 / 5) 60 - 4 * atanSum (1 / 239) 18 - piQ| + 16 * atanRem (1 / 5) 60 +
      4 * atanRem (1 / 239) 18 ≤ 1 / 2 ^ 270 := by decide +kernel
  have key' := (Rat.cast_le (K := ℝ)).mpr key
  push_cast at key'
  rw [show Real.pi = 4 * (Real.pi / 4) by ring, ← Real.four_mul_arctan_inv_5_sub_arctan_inv_239,
    show 4 * (4 * Real.arctan 5⁻¹ - Real.arctan 239⁻¹) =
      16 * Real.arctan 5⁻¹ - 4 * Real.arctan 239⁻¹ by ring]
  exact machin_combine _ _ _ _ _ _ _ _ h5 h239 key'

/-- `ln 2 · 2^270` rounded to nearest, over `2^270`. -/
def ln2Q : ℚ :=
  1314995571687281604398840286516184195628903098148289685194717061208800575097600494 / 2 ^ 270

/-- `ln2Q` is within `2^-270` of `ln 2`. -/
theorem log_two_near : |Real.log 2 - ln2Q| ≤ 1 / 2 ^ 270 := by
  have h := log_near (1 / 3) 87 (by decide +kernel)
  have e : Real.log (1 + ((1 / 3 : ℚ) : ℝ)) - Real.log (1 - ((1 / 3 : ℚ) : ℝ)) = Real.log 2 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]; norm_num
  rw [e] at h
  have key : |logSum (1 / 3) 87 - ln2Q| + logRem (1 / 3) 87 ≤ 1 / 2 ^ 270 := by decide +kernel
  have key' := (Rat.cast_le (K := ℝ)).mpr key
  push_cast at key'
  calc |Real.log 2 - ln2Q| ≤ |Real.log 2 - logSum (1 / 3) 87| + |(logSum (1 / 3) 87 : ℝ) - ln2Q| :=
        abs_sub_le _ _ _
    _ ≤ logRem (1 / 3) 87 + |(logSum (1 / 3) 87 : ℝ) - ln2Q| := add_le_add h le_rfl
    _ ≤ 1 / 2 ^ 270 := by rw [add_comm]; exact key'

/-- A natural `T` is within `½` of `v · 2^N` when `v` is within `R` of a rational
`S` and `|T - S · 2^N| + R · 2^N ≤ ½`. -/
theorem entry_near (T N : ℕ) (v : ℝ) (S R : ℚ) (hv : |v - S| ≤ R)
    (h : |(T : ℚ) - S * 2 ^ N| + R * 2 ^ N ≤ 1 / 2) : |(T : ℝ) - v * 2 ^ N| ≤ 1 / 2 := by
  have h' := (Rat.cast_le (K := ℝ)).mpr h
  push_cast at h'
  have p : (0 : ℝ) < 2 ^ N := pow_pos two_pos N
  have e : (T : ℝ) - v * 2 ^ N = ((T : ℝ) - S * 2 ^ N) + (S - v) * 2 ^ N := by ring
  rw [e]
  refine (abs_add_le _ _).trans ((add_le_add le_rfl ?_).trans h')
  rw [abs_mul, abs_of_pos p, abs_sub_comm]
  exact mul_le_mul_of_nonneg_right hv p.le

end Fulcrum

end
