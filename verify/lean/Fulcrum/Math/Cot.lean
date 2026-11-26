module

public import Mathlib.Analysis.Complex.Trigonometric
import Fulcrum.Math.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The cotangent near zero

`cot θ = 1/θ - θ/3 - θ³/45 - 2θ⁵/945 - …`; for `0 < θ ≤ 1/512` the first three
terms are within `θ⁵ / 390` of it (`cot_near`). The proof cuts the series of
`sin` after `θ⁵` and of `cos` after `θ⁶` (`Series.lean`): with
`P = 1/θ - θ/3 - θ³/45` the polynomial parts give
`cos θ - P · sin θ = -θ⁶/432 + θ⁸/5400` up to the tails, and `sin θ ≥ θ - θ³/6`
divides it. No code here: the math of `trig::tan` near a pole (INTERNALS §3.12).
-/

@[expose] public section

open Finset

namespace Fulcrum

/-- The first three terms of the cotangent, `1/θ - θ/3 - θ³/45`, are within
`θ⁵ / 390` of `cos θ / sin θ` for `0 < θ ≤ 1/512`. -/
theorem cot_near (θ : ℝ) (h0 : 0 < θ) (h1 : θ ≤ 1 / 512) :
    |Real.cos θ / Real.sin θ - (1 / θ - θ / 3 - θ ^ 3 / 45)| ≤ θ ^ 5 / 390 := by
  have t2 : θ ^ 2 ≤ 1 / 512 ^ 2 := by
    rw [show (1 : ℝ) / 512 ^ 2 = (1 / 512) ^ 2 by norm_num]; exact pow_le_pow_left₀ h0.le h1 2
  have hs := sin_sub_sum_le θ 3 (by norm_num; nlinarith only [h0, h1, t2])
  have hc := cos_sub_sum_le θ 4 (by norm_num; nlinarith only [h0, h1, t2])
  simp only [sum_range_succ, sum_range_zero, Nat.factorial, Nat.succ_eq_add_one] at hs hc
  norm_num at hs hc
  rw [abs_of_pos h0] at hs hc
  set s := Real.sin θ
  set c := Real.cos θ
  have sl : θ - θ ^ 3 / 6 ≤ s := Real.sin_ge_sub_cube h0.le
  have hs' : |s - (θ - θ ^ 3 / 6 + θ ^ 5 / 120)| ≤ θ ^ 7 / 5039 := by
    rw [show θ - θ ^ 3 / 6 + θ ^ 5 / 120 = θ + -θ ^ 3 / 6 + θ ^ 5 / 120 by ring]
    refine hs.trans ?_
    rw [div_div, div_le_div_iff₀ (by nlinarith only [h0, h1, t2]) (by norm_num)]
    have : (0 : ℝ) ≤ θ ^ 7 := by positivity
    nlinarith only [h0, h1, t2, this]
  have hc' : |c - (1 - θ ^ 2 / 2 + θ ^ 4 / 24 - θ ^ 6 / 720)| ≤ θ ^ 8 / 40319 := by
    rw [show 1 - θ ^ 2 / 2 + θ ^ 4 / 24 - θ ^ 6 / 720 = 1 + -θ ^ 2 / 2 + θ ^ 4 / 24 + -θ ^ 6 / 720 by ring]
    refine hc.trans ?_
    rw [div_div, div_le_div_iff₀ (by nlinarith only [h0, h1, t2]) (by norm_num)]
    have : (0 : ℝ) ≤ θ ^ 8 := by positivity
    nlinarith only [h0, h1, t2, this]
  set P := 1 / θ - θ / 3 - θ ^ 3 / 45 with hP
  have P0 : 0 ≤ P := by
    rw [hP, one_div]
    have : θ * θ⁻¹ = 1 := mul_inv_cancel₀ h0.ne'
    nlinarith [inv_pos.mpr h0]
  have P1 : P ≤ 1 / θ := by rw [hP]; nlinarith [pow_pos h0 3]
  have poly : (1 - θ ^ 2 / 2 + θ ^ 4 / 24 - θ ^ 6 / 720) - P * (θ - θ ^ 3 / 6 + θ ^ 5 / 120) =
      -θ ^ 6 / 432 + θ ^ 8 / 5400 := by
    rw [hP]; field_simp; ring
  have num : |c - P * s| ≤ θ ^ 6 / 432 + θ ^ 8 / 5400 + θ ^ 8 / 40319 + θ ^ 6 / 5039 := by
    have e : c - P * s = (-θ ^ 6 / 432 + θ ^ 8 / 5400) + (c - (1 - θ ^ 2 / 2 + θ ^ 4 / 24 - θ ^ 6 / 720)) -
        P * (s - (θ - θ ^ 3 / 6 + θ ^ 5 / 120)) := by rw [← poly]; ring
    rw [e]
    have p1 : |-θ ^ 6 / 432 + θ ^ 8 / 5400| ≤ θ ^ 6 / 432 + θ ^ 8 / 5400 := by
      refine (abs_add_le _ _).trans (le_of_eq ?_)
      rw [neg_div, abs_neg, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    have p3 : |P * (s - (θ - θ ^ 3 / 6 + θ ^ 5 / 120))| ≤ θ ^ 6 / 5039 := by
      rw [abs_mul, abs_of_nonneg P0]
      calc P * |s - (θ - θ ^ 3 / 6 + θ ^ 5 / 120)| ≤ 1 / θ * (θ ^ 7 / 5039) :=
            mul_le_mul P1 hs' (abs_nonneg _) (by positivity)
        _ = θ ^ 6 / 5039 := by field_simp
    calc _ ≤ |-θ ^ 6 / 432 + θ ^ 8 / 5400 + (c - (1 - θ ^ 2 / 2 + θ ^ 4 / 24 - θ ^ 6 / 720))| +
          |P * (s - (θ - θ ^ 3 / 6 + θ ^ 5 / 120))| := abs_sub _ _
      _ ≤ θ ^ 6 / 432 + θ ^ 8 / 5400 + θ ^ 8 / 40319 + θ ^ 6 / 5039 :=
          add_le_add ((abs_add_le _ _).trans (add_le_add p1 hc')) p3
  have spos : 0 < θ - θ ^ 3 / 6 := by nlinarith
  have s0 : 0 < s := spos.trans_le sl
  rw [show c / s - P = (c - P * s) / s by field_simp, abs_div, abs_of_pos s0,
    div_le_iff₀ s0]
  refine num.trans ?_
  have : θ ^ 6 / 432 + θ ^ 8 / 5400 + θ ^ 8 / 40319 + θ ^ 6 / 5039 ≤ θ ^ 5 / 390 * (θ - θ ^ 3 / 6) := by
    have e6 : (0 : ℝ) ≤ θ ^ 6 := by positivity
    have : θ ^ 8 = θ ^ 6 * θ ^ 2 := by ring
    have : θ ^ 5 / 390 * (θ - θ ^ 3 / 6) = θ ^ 6 / 390 - θ ^ 6 * θ ^ 2 / 2340 := by ring
    nlinarith [mul_le_mul_of_nonneg_left t2 e6]
  exact this.trans (mul_le_mul_of_nonneg_left sl (by positivity))

end Fulcrum

end
