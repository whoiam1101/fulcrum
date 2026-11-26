module

public import Fulcrum.Math.Fixed
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Fulcrum.Math.Const
import Fulcrum.Math.Quarter
import Fulcrum.Math.Series
import Mathlib.Algebra.Order.Ring.Star

/-!
# `log₂ (c (1 + σ)/(1 - σ))` of the table (INTERNALS §3.16)

`log2N` is `log2_unit` off the table points on naturals: to the entry `T ≈ log₂ c` of
`LOG2` it adds `K · (s + s z (⅓ + z/5))`, `z = s²`, `K ≈ 2 / ln 2`, every product truncated
to 62 bits. `log2_series_near`: for `s` the floor of `σ · 2^62`, `σ ≤ 2^-9`, the result
is within `7.6` units of `(log₂ c + (log (1 + σ) - log (1 - σ)) / ln 2) · 2^62`. The steps
follow the error budget of §3.16: `z` within `1.004`, `z/5` within `1.201`, the bracket
within `2.201`, `z` times it within `1.335`, `s` times that within `1.0001`, the series
within `2.08` with the dropped term `σ⁷/7`, the product with `K` within `7.03`.
No code here: the math of L4.
-/

@[expose] public section

open Finset

namespace Fulcrum

/-- `ln 2 ≥ 0.693147`. -/
theorem log_two_ge' : (693147 / 1000000 : ℝ) ≤ Real.log 2 := by
  have c := (Rat.cast_le (K := ℝ)).mpr (by decide +kernel : (693147 / 1000000 : ℚ) ≤ ln2Q - 1 / 2 ^ 270)
  push_cast at c
  exact c.trans (sub_le_iff_le_add.mpr (neg_le_sub_iff_le_add.mp (abs_le.mp log_two_near).1))

/-- `ln 2 ≤ 0.69315`. -/
theorem log_two_le' : Real.log 2 ≤ 69315 / 100000 := by
  have c := (Rat.cast_le (K := ℝ)).mpr (by decide +kernel : ln2Q + 1 / 2 ^ 270 ≤ (69315 / 100000 : ℚ))
  push_cast at c
  exact (le_add_of_sub_left_le (abs_le.mp log_two_near).2).trans c

/-- `log2_unit` off the table points on naturals: the entry `T`, the quotient `s`, the
constant `K`. -/
def log2N (T s K : ℕ) : ℕ :=
  let z := mul62 s s
  T + mul62 (s + mul62 s (mul62 z (2 ^ 62 / 3 + mul62 z (2 ^ 62 / 5)))) K

set_option maxRecDepth 10000 in
/-- `log2_unit` off the table points: from the entry `T` within `½` of `log₂ c · 2^62`,
`K` within `½` of `2 / ln 2 · 2^62` and `s = ⌊σ · 2^62⌋`, `0 ≤ σ ≤ 2^-9`, `log2N T s K` is
within `7.6` units of `(log₂ c + (log (1 + σ) - log (1 - σ)) / ln 2) · 2^62`. -/
theorem log2_series_near (T s K : ℕ) (c σ : ℝ) (hT : |(T : ℝ) - Real.logb 2 c * 2 ^ 62| ≤ 1 / 2)
    (hK : |(K : ℝ) - 2 / Real.log 2 * 2 ^ 62| ≤ 1 / 2) (hσ0 : 0 ≤ σ) (hσ : σ ≤ 1 / 512)
    (hs : (s : ℝ) ≤ σ * 2 ^ 62) (hs1 : σ * 2 ^ 62 < s + 1) :
    |(log2N T s K : ℝ) - (Real.logb 2 c + (Real.log (1 + σ) - Real.log (1 - σ)) / Real.log 2) * 2 ^ 62| ≤
      76 / 10 := by
  have U0 : (0 : ℝ) < 2 ^ 62 := by positivity
  have ln2 := log_two_ge'
  have ln0 : 0 < Real.log 2 := by linarith only [ln2]
  set Sg : ℝ := σ * 2 ^ 62 with hSg
  have Sg0 : 0 ≤ Sg := by positivity
  have SgM : Sg ≤ 2 ^ 53 := by
    rw [hSg]; exact (mul_le_mul_of_nonneg_right hσ U0.le).trans (by norm_num)
  have sM : (s : ℝ) ≤ 2 ^ 53 := hs.trans SgM
  have sl : s ≤ 2 ^ 53 := by exact_mod_cast sM
  have es : |(s : ℝ) - Sg| ≤ 1 := abs_le.mpr ⟨by linarith only [hs1], by linarith only [hs]⟩
  set! Z : ℝ := Sg * Sg / 2 ^ 62 with hZ
  have Z0 : 0 ≤ Z := by positivity
  have ZM : Z ≤ 2 ^ 44 := by
    rw [hZ, div_le_iff₀ U0]; exact (mul_le_mul SgM SgM Sg0 (by positivity)).trans (by norm_num)
  have zl : mul62 s s ≤ 2 ^ 44 := Nat.div_le_of_le_mul ((Nat.mul_le_mul sl sl).trans (by norm_num))
  generalize hz : mul62 s s = z at zl ⊢
  have zM : (z : ℝ) ≤ 2 ^ 44 := by exact_mod_cast zl
  have ez : |(z : ℝ) - Z| ≤ 1004 / 1000 := by
    have h := mul62_near s s Sg Sg 1 1 (2 ^ 53) (2 ^ 53) es es Sg0 SgM sM
    rw [hz] at h; exact h.trans (by norm_num)
  have e11 : |((2 ^ 62 / 5 : ℕ) : ℝ) - 2 ^ 62 / 5| ≤ 1 := by
    have h := div_near (2 ^ 62) 5 (2 ^ 62) 0 (by norm_num) (by norm_num)
    push_cast at h; exact h.trans (by norm_num)
  have e10 : |((2 ^ 62 / 3 : ℕ) : ℝ) - 2 ^ 62 / 3| ≤ 1 := by
    have h := div_near (2 ^ 62) 3 (2 ^ 62) 0 (by norm_num) (by norm_num)
    push_cast at h; exact h.trans (by norm_num)
  have i11M : ((2 ^ 62 / 5 : ℕ) : ℝ) ≤ 2 ^ 62 / 5 := by norm_num
  have e12 := mul62_near z (2 ^ 62 / 5) Z (2 ^ 62 / 5) _ _ (2 ^ 44) _ ez e11 Z0 ZM i11M
  have e12' := e12.trans (show _ ≤ (1201 / 1000 : ℝ) by norm_num)
  have i12l : mul62 z (2 ^ 62 / 5) ≤ 2 ^ 44 := mul62_le_left _ _ (by norm_num) |>.trans zl
  have e13 : |((2 ^ 62 / 3 + mul62 z (2 ^ 62 / 5) : ℕ) : ℝ) - (2 ^ 62 / 3 + Z * (2 ^ 62 / 5) / 2 ^ 62)| ≤
      2201 / 1000 := by
    rw [Nat.cast_add, show ((2 ^ 62 / 3 : ℕ) : ℝ) + mul62 z (2 ^ 62 / 5) - (2 ^ 62 / 3 + Z * (2 ^ 62 / 5) / 2 ^ 62) =
      (((2 ^ 62 / 3 : ℕ) : ℝ) - 2 ^ 62 / 3) + ((mul62 z (2 ^ 62 / 5) : ℝ) - Z * (2 ^ 62 / 5) / 2 ^ 62) by ring]
    exact (abs_add_le _ _).trans ((add_le_add e10 e12').trans (by norm_num))
  have i13M : ((2 ^ 62 / 3 + mul62 z (2 ^ 62 / 5) : ℕ) : ℝ) ≤ 2 ^ 62 / 3 + 2 ^ 44 := by
    push_cast
    have : ((2 ^ 62 / 3 : ℕ) : ℝ) ≤ 2 ^ 62 / 3 := by norm_num
    have : ((mul62 z (2 ^ 62 / 5) : ℕ) : ℝ) ≤ 2 ^ 44 := by exact_mod_cast i12l
    linarith only [this]
  have e14 := mul62_near z _ Z _ _ _ (2 ^ 44) _ ez e13 Z0 ZM i13M
  have e14' := e14.trans (show _ ≤ (1335 / 1000 : ℝ) by norm_num)
  set I13 : ℝ := 2 ^ 62 / 3 + Z * (2 ^ 62 / 5) / 2 ^ 62 with hI13
  set I14 : ℝ := Z * I13 / 2 ^ 62 with hI14
  have I13M : I13 ≤ 2 ^ 62 / 3 + 2 ^ 44 := by
    rw [hI13]
    have : Z * (2 ^ 62 / 5) / 2 ^ 62 ≤ 2 ^ 44 := by
      rw [mul_div_assoc, div_div_cancel_left₀ (by positivity : (2 : ℝ) ^ 62 ≠ 0)]
      linarith only [ZM]
    linarith only [ZM]
  have I14M : I14 ≤ 2 ^ 43 - 2 := by
    rw [hI14, div_le_iff₀ U0]
    exact (mul_le_mul ZM I13M (by positivity) (by positivity)).trans (by norm_num)
  have I140 : 0 ≤ I14 := by positivity
  have i14l : mul62 z (2 ^ 62 / 3 + mul62 z (2 ^ 62 / 5)) ≤ 2 ^ 43 := by
    have h : ((mul62 z (2 ^ 62 / 3 + mul62 z (2 ^ 62 / 5)) : ℕ) : ℝ) ≤ 2 ^ 43 := by
      have := (abs_le.mp e14').2; linarith only [I14M, this]
    exact_mod_cast h
  have i14M : ((mul62 z (2 ^ 62 / 3 + mul62 z (2 ^ 62 / 5)) : ℕ) : ℝ) ≤ 2 ^ 43 := by exact_mod_cast i14l
  have e15 := mul62_near s _ Sg I14 1 _ (2 ^ 53) (2 ^ 43) es e14' Sg0 SgM i14M
  have e15' := e15.trans (show _ ≤ (10027 / 10000 : ℝ) by norm_num)
  set! Sr : ℝ := Sg + Sg * I14 / 2 ^ 62 with hSr
  have eser : |((s + mul62 s (mul62 z (2 ^ 62 / 3 + mul62 z (2 ^ 62 / 5))) : ℕ) : ℝ) - Sr| ≤ 20027 / 10000 := by
    rw [Nat.cast_add, hSr, show (s : ℝ) + mul62 s (mul62 z (2 ^ 62 / 3 + mul62 z (2 ^ 62 / 5))) -
      (Sg + Sg * I14 / 2 ^ 62) = ((s : ℝ) - Sg) +
        ((mul62 s (mul62 z (2 ^ 62 / 3 + mul62 z (2 ^ 62 / 5))) : ℝ) - Sg * I14 / 2 ^ 62) by ring]
    exact (abs_add_le _ _).trans ((add_le_add es e15').trans (by norm_num))
  set! L : ℝ := (Real.log (1 + σ) - Real.log (1 - σ)) / 2 * 2 ^ 62 with hL
  have tail : |L - Sr| ≤ 8 / 100 := by
    have h := log_sub_sum_le σ 3 (by rw [abs_of_nonneg hσ0]; linarith only [hσ])
    norm_num [sum_range_succ, abs_of_nonneg hσ0] at h
    have poly : Sr = 2 ^ 62 * (σ + σ ^ 3 / 3 + σ ^ 5 / 5) := by
      rw [hSr, hI14, hI13, hZ, hSg]; field_simp; ring
    rw [poly, hL, show (Real.log (1 + σ) - Real.log (1 - σ)) / 2 * 2 ^ 62 - 2 ^ 62 * (σ + σ ^ 3 / 3 + σ ^ 5 / 5) =
      2 ^ 62 / 2 * ((Real.log (1 + σ) - Real.log (1 - σ)) - (2 * σ + 2 * (1 / 3) * σ ^ 3 + 2 * (1 / 5) * σ ^ 5)) by ring,
      abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 62 / 2)]
    have s2 : σ ^ 2 ≤ (1 / 512) ^ 2 := pow_le_pow_left₀ hσ0 hσ 2
    have s7 : σ ^ 7 ≤ (1 / 512) ^ 7 := pow_le_pow_left₀ hσ0 hσ 7
    have d : (99 / 100 : ℝ) ≤ 1 - σ ^ 2 := by linarith only [show ((1 : ℝ) / 512) ^ 2 ≤ 1 / 100 by norm_num, hZ, ZM]
    have hh : |(Real.log (1 + σ) - Real.log (1 - σ)) - (2 * σ + 2 * (1 / 3) * σ ^ 3 + 2 * (1 / 5) * σ ^ 5)| ≤
        2 * σ ^ 7 / 7 / (1 - σ ^ 2) := by
      convert h using 2; ring
    calc 2 ^ 62 / 2 * |(Real.log (1 + σ) - Real.log (1 - σ)) - (2 * σ + 2 * (1 / 3) * σ ^ 3 + 2 * (1 / 5) * σ ^ 5)|
        ≤ 2 ^ 62 / 2 * (2 * (1 / 512) ^ 7 / 7 / (99 / 100)) :=
          mul_le_mul_of_nonneg_left (hh.trans (div_le_div₀ (by positivity)
            (div_le_div_of_nonneg_right (by linarith only [s7]) (by norm_num)) (by norm_num) d)) (by positivity)
      _ ≤ 8 / 100 := by norm_num
  have eL : |((s + mul62 s (mul62 z (2 ^ 62 / 3 + mul62 z (2 ^ 62 / 5))) : ℕ) : ℝ) - L| ≤ 209 / 100 := by
    calc _ ≤ |((s + mul62 s (mul62 z (2 ^ 62 / 3 + mul62 z (2 ^ 62 / 5))) : ℕ) : ℝ) - Sr| + |Sr - L| :=
          abs_sub_le _ _ _
      _ ≤ 20027 / 10000 + 8 / 100 := add_le_add eser (by rw [abs_sub_comm]; exact tail)
      _ ≤ 209 / 100 := by norm_num
  have L0 : 0 ≤ L := by
    rw [hL]
    have : Real.log (1 - σ) ≤ Real.log (1 + σ) := Real.log_le_log (by linarith only [hσ]) (by linarith only [hσ0])
    have : 0 ≤ (Real.log (1 + σ) - Real.log (1 - σ)) / 2 := by linarith only [this]
    positivity
  have SrM : Sr ≤ 2 ^ 53 + 2 ^ 34 := by
    rw [hSr]
    have : Sg * I14 / 2 ^ 62 ≤ 2 ^ 34 := by
      rw [div_le_iff₀ U0]
      exact (mul_le_mul SgM I14M I140 (by positivity)).trans (by norm_num)
    linarith only [hσ, this]
  have LM : L ≤ 2 ^ 53 + 2 ^ 35 := by linarith only [(abs_le.mp tail).2, SrM]
  have KM : (K : ℝ) ≤ 28855 / 10000 * 2 ^ 62 := by
    have h1 : 2 / Real.log 2 ≤ 288545 / 100000 := by rw [div_le_iff₀ ln0]; linarith only [ln2, ln0]
    have h2 := (abs_le.mp hK).2
    have h3 : 2 / Real.log 2 * 2 ^ 62 ≤ 288545 / 100000 * 2 ^ 62 := mul_le_mul_of_nonneg_right h1 U0.le
    linarith only [h1, h2]
  have e18 := mul62_near _ K L (2 / Real.log 2 * 2 ^ 62) _ _ (2 ^ 53 + 2 ^ 35) _ eL hK L0 LM KM
  have e18' := e18.trans (show _ ≤ (704 / 100 : ℝ) by norm_num)
  unfold log2N
  dsimp only
  rw [hz, Nat.cast_add]
  have key : (T : ℝ) + mul62 (s + mul62 s (mul62 z (2 ^ 62 / 3 + mul62 z (2 ^ 62 / 5)))) K -
      (Real.logb 2 c + (Real.log (1 + σ) - Real.log (1 - σ)) / Real.log 2) * 2 ^ 62 =
      ((T : ℝ) - Real.logb 2 c * 2 ^ 62) +
        ((mul62 (s + mul62 s (mul62 z (2 ^ 62 / 3 + mul62 z (2 ^ 62 / 5)))) K : ℝ) -
          L * (2 / Real.log 2 * 2 ^ 62) / 2 ^ 62) := by
    rw [hL]
    generalize ((mul62 (s + mul62 s (mul62 z (2 ^ 62 / 3 + mul62 z (2 ^ 62 / 5)))) K : ℕ) : ℝ) = M
    generalize Real.log (1 + σ) - Real.log (1 - σ) = D
    generalize Real.logb 2 c = lb
    have l0 := ln0.ne'
    generalize Real.log 2 = l at l0 ⊢
    generalize (2 : ℝ) ^ 62 = W
    field_simp; ring
  rw [key]
  exact (abs_add_le _ _).trans ((add_le_add hT e18').trans (by norm_num))

end Fulcrum

end
