module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Fulcrum.Math.Log
import Fulcrum.Math.Series
import Mathlib.Algebra.Order.Ring.Star

/-!
# The wide logarithm of `pow` (INTERNALS §3.16)

`log2WideN` is `exp::log2_wide` off the table points on naturals at 128 fractional bits:
to the entry `T ≈ log₂ c · 2^126` of `LOG2_WIDE` it adds `K · artanh s`, `K ≈ 2 / ln 2 · 2^126`,
where `atanhWideN s` is `s + s z g`, `z = s²` and `g = ⅓ + z/5 + … + z⁵/13` by Horner with the
coefficients `⌊(2^128 - 1)/n⌋`, every product the top half `⌊a · b / 2^128⌋`.
`log2_wide_series_near`: for `s` the floor of `σ · 2^128`, `σ ≤ 2^-9`, the result is within `3`
units of `(log₂ c + (log (1 + σ) - log (1 - σ)) / ln 2) · 2^126`. The steps: `z` within
`1.004`, every Horner step within `3`, `z g` within `1.51`, `s z g` within `1.01`, the series
within `2.02` with the dropped term `σ^15/15`, the product with `K` within `2.46`, the entry `½`.
No code here: the math of L4.
-/

@[expose] public section

open Finset

namespace Fulcrum

/-- `⌊a · b / 2^128⌋`: `exp::mul_hi` on naturals. -/
def mul128 (a b : ℕ) : ℕ := a * b / 2 ^ 128

/-- The truncated product `⌊a · b / 2^128⌋` of values within `ea`, `eb` of `A ≥ 0`, `B` is
within `(ea · Mb + MA · eb) / 2^128 + 1` of `A · B / 2^128`, for `A ≤ MA` and `b ≤ Mb`. -/
theorem mul128_near (a b : ℕ) (A B ea eb MA Mb : ℝ) (ha : |(a : ℝ) - A| ≤ ea)
    (hb : |(b : ℝ) - B| ≤ eb) (hA0 : 0 ≤ A) (hA : A ≤ MA) (hbM : (b : ℝ) ≤ Mb) :
    |(mul128 a b : ℝ) - A * B / 2 ^ 128| ≤ (ea * Mb + MA * eb) / 2 ^ 128 + 1 := by
  have h := div_near (a * b) (2 ^ 128) (A * B) (ea * Mb + MA * eb) (by positivity) (by
    rw [Nat.cast_mul, show (a : ℝ) * b - A * B = (a - A) * b + A * (b - B) by ring]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, Nat.abs_cast b]
      exact mul_le_mul ha hbM (Nat.cast_nonneg b) ((abs_nonneg _).trans ha)
    · rw [abs_mul, abs_of_nonneg hA0]
      exact mul_le_mul hA hb (abs_nonneg _) (hA0.trans hA))
  rw [Nat.cast_pow, Nat.cast_ofNat] at h
  exact h

/-- `⌊a · b / 2^128⌋ ≤ a` for `b ≤ 2^128`. -/
theorem mul128_le_left (a b : ℕ) (hb : b ≤ 2 ^ 128) : mul128 a b ≤ a :=
  Nat.div_le_of_le_mul (by rw [mul_comm]; exact Nat.mul_le_mul_right a hb)

/-- `⌊(2^128 - 1)/n⌋` is within `1 + 1/n ≤ 4/3` of `2^128 / n`, for `n ≥ 3`. -/
theorem coeff128_near (n : ℕ) (hn : 3 ≤ n) :
    |(((2 ^ 128 - 1) / n : ℕ) : ℝ) - 2 ^ 128 / n| ≤ 4 / 3 := by
  have np : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have n3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have ⟨l, u⟩ := floor_div_near (2 ^ 128 - 1) n (by omega)
  have c : (((2 ^ 128 - 1 : ℕ)) : ℝ) = 2 ^ 128 - 1 := by norm_num
  rw [c] at l u
  have i : 1 / (n : ℝ) ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) n3
  have e : ((2 : ℝ) ^ 128 - 1) / n = 2 ^ 128 / n - 1 / n := by ring
  rw [e] at l u
  exact abs_le.mpr ⟨by linarith only [u, i], by linarith only [show (0 : ℝ) < 1 / n by positivity, l]⟩

/-- One Horner step of `atanhWideN`: `⌊(2^128 - 1)/n⌋ + ⌊z g / 2^128⌋` against
`2^128 / n + Z G / 2^128`, for `z` within `1.004` of `Z ≤ 2^110` and `g` within `3` of
`0 ≤ G`, both at most `2^127`: within `3`, and both again at most `2^127`. -/
theorem horner128_step (z g n : ℕ) (Z G : ℝ) (hn : 3 ≤ n) (hz : |(z : ℝ) - Z| ≤ 1004 / 1000)
    (Z0 : 0 ≤ Z) (ZM : Z ≤ 2 ^ 110) (zl : z ≤ 2 ^ 110) (hg : |(g : ℝ) - G| ≤ 3) (gl : g ≤ 2 ^ 127)
    (G0 : 0 ≤ G) (GM : G ≤ 2 ^ 127) :
    |((((2 ^ 128 - 1) / n + mul128 z g : ℕ)) : ℝ) - (2 ^ 128 / n + Z * G / 2 ^ 128)| ≤ 3 ∧
      (2 ^ 128 - 1) / n + mul128 z g ≤ 2 ^ 127 ∧ 0 ≤ 2 ^ 128 / (n : ℝ) + Z * G / 2 ^ 128 ∧
      2 ^ 128 / (n : ℝ) + Z * G / 2 ^ 128 ≤ 2 ^ 127 := by
  have gM : (g : ℝ) ≤ 2 ^ 127 := by exact_mod_cast gl
  have m := mul128_near z g Z G _ _ (2 ^ 110) _ hz hg Z0 ZM gM
  have c := coeff128_near n hn
  have n3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have cM : (2 : ℝ) ^ 128 / n ≤ 2 ^ 128 / 3 := div_le_div_of_nonneg_left (by positivity) (by norm_num) n3
  have ZG : Z * G / 2 ^ 128 ≤ 2 ^ 109 := by
    rw [div_le_iff₀ (by positivity)]
    exact (mul_le_mul ZM GM G0 (by positivity)).trans (by norm_num)
  refine ⟨?_, ?_, by positivity, by linarith only [cM, ZG]⟩
  · rw [Nat.cast_add, show (((2 ^ 128 - 1) / n : ℕ) : ℝ) + (mul128 z g : ℝ) - (2 ^ 128 / n + Z * G / 2 ^ 128) =
      ((((2 ^ 128 - 1) / n : ℕ) : ℝ) - 2 ^ 128 / n) + ((mul128 z g : ℝ) - Z * G / 2 ^ 128) by ring]
    exact (abs_add_le _ _).trans ((add_le_add c m).trans (by norm_num))
  · have a : (2 ^ 128 - 1) / n ≤ (2 ^ 128 - 1) / 3 := Nat.div_le_div_left hn (by norm_num)
    have b : mul128 z g ≤ 2 ^ 109 :=
      Nat.div_le_of_le_mul ((Nat.mul_le_mul zl gl).trans (by norm_num))
    have : (2 ^ 128 - 1) / 3 + 2 ^ 109 ≤ 2 ^ 127 := by norm_num
    omega

/-- `artanh s` of `log2_wide` on naturals, `s` at 128 fractional bits. -/
def atanhWideN (s : ℕ) : ℕ :=
  let z := mul128 s s
  let g := (2 ^ 128 - 1) / 13
  let g := (2 ^ 128 - 1) / 11 + mul128 z g
  let g := (2 ^ 128 - 1) / 9 + mul128 z g
  let g := (2 ^ 128 - 1) / 7 + mul128 z g
  let g := (2 ^ 128 - 1) / 5 + mul128 z g
  let g := (2 ^ 128 - 1) / 3 + mul128 z g
  s + mul128 s (mul128 z g)

/-- `log2_wide` off the table points on naturals: the entry `T`, the quotient `s`, the
constant `K`, at 126 fractional bits. -/
def log2WideN (T s K : ℕ) : ℕ := T + mul128 (atanhWideN s) K

set_option maxRecDepth 10000 in
/-- `log2_wide` off the table points: from the entry `T` within `½` of `log₂ c · 2^126`,
`K` within `½` of `2 / ln 2 · 2^126` and `s = ⌊σ · 2^128⌋`, `0 ≤ σ ≤ 2^-9`, `log2WideN T s K`
is within `3` units of `(log₂ c + (log (1 + σ) - log (1 - σ)) / ln 2) · 2^126`. -/
theorem log2_wide_series_near (T s K : ℕ) (c σ : ℝ) (hT : |(T : ℝ) - Real.logb 2 c * 2 ^ 126| ≤ 1 / 2)
    (hK : |(K : ℝ) - 2 / Real.log 2 * 2 ^ 126| ≤ 1 / 2) (hσ0 : 0 ≤ σ) (hσ : σ ≤ 1 / 512)
    (hs : (s : ℝ) ≤ σ * 2 ^ 128) (hs1 : σ * 2 ^ 128 < s + 1) :
    |(log2WideN T s K : ℝ) - (Real.logb 2 c + (Real.log (1 + σ) - Real.log (1 - σ)) / Real.log 2) * 2 ^ 126| ≤
      3 := by
  have U0 : (0 : ℝ) < 2 ^ 128 := by positivity
  have ln2 := log_two_ge'
  have ln0 : 0 < Real.log 2 := by linarith only [ln2]
  set Sg : ℝ := σ * 2 ^ 128 with hSg
  have Sg0 : 0 ≤ Sg := by positivity
  have SgM : Sg ≤ 2 ^ 119 := by
    rw [hSg]; exact (mul_le_mul_of_nonneg_right hσ U0.le).trans (by norm_num)
  have sM : (s : ℝ) ≤ 2 ^ 119 := hs.trans SgM
  have sl : s ≤ 2 ^ 119 := by exact_mod_cast sM
  have es : |(s : ℝ) - Sg| ≤ 1 := abs_le.mpr ⟨by linarith only [hs1], by linarith only [hs]⟩
  set! Z : ℝ := Sg * Sg / 2 ^ 128 with hZ
  have Z0 : 0 ≤ Z := by positivity
  have ZM : Z ≤ 2 ^ 110 := by
    rw [hZ, div_le_iff₀ U0]; exact (mul_le_mul SgM SgM Sg0 (by positivity)).trans (by norm_num)
  have zl : mul128 s s ≤ 2 ^ 110 := Nat.div_le_of_le_mul ((Nat.mul_le_mul sl sl).trans (by norm_num))
  generalize hz : mul128 s s = z at zl ⊢
  have ez : |(z : ℝ) - Z| ≤ 1004 / 1000 := by
    have h := mul128_near s s Sg Sg 1 1 (2 ^ 119) (2 ^ 119) es es Sg0 SgM sM
    rw [hz] at h; exact h.trans (by norm_num)
  set! G13 : ℝ := 2 ^ 128 / 13
  have e13 : |((((2 ^ 128 - 1) / 13 : ℕ)) : ℝ) - G13| ≤ 3 := (coeff128_near 13 (by norm_num)).trans (by norm_num)
  have h11 := horner128_step z ((2 ^ 128 - 1) / 13) 11 Z G13 (by norm_num) ez Z0 ZM zl e13 (by norm_num)
    (by positivity) (by norm_num)
  set G11 : ℝ := 2 ^ 128 / (11 : ℕ) + Z * G13 / 2 ^ 128
  have h9 := horner128_step z _ 9 Z G11 (by norm_num) ez Z0 ZM zl h11.1 h11.2.1 h11.2.2.1 h11.2.2.2
  set G9 : ℝ := 2 ^ 128 / (9 : ℕ) + Z * G11 / 2 ^ 128
  have h7 := horner128_step z _ 7 Z G9 (by norm_num) ez Z0 ZM zl h9.1 h9.2.1 h9.2.2.1 h9.2.2.2
  set G7 : ℝ := 2 ^ 128 / (7 : ℕ) + Z * G9 / 2 ^ 128
  have h5 := horner128_step z _ 5 Z G7 (by norm_num) ez Z0 ZM zl h7.1 h7.2.1 h7.2.2.1 h7.2.2.2
  set G5 : ℝ := 2 ^ 128 / (5 : ℕ) + Z * G7 / 2 ^ 128
  have h3 := horner128_step z _ 3 Z G5 (by norm_num) ez Z0 ZM zl h5.1 h5.2.1 h5.2.2.1 h5.2.2.2
  set G3 : ℝ := 2 ^ 128 / (3 : ℕ) + Z * G5 / 2 ^ 128
  generalize hg : (2 ^ 128 - 1) / 3 + mul128 z ((2 ^ 128 - 1) / 5 + mul128 z ((2 ^ 128 - 1) / 7 +
    mul128 z ((2 ^ 128 - 1) / 9 + mul128 z ((2 ^ 128 - 1) / 11 + mul128 z ((2 ^ 128 - 1) / 13))))) = g at h3
  have ⟨eg, gl, G30, G3M⟩ := h3
  have gM : (g : ℝ) ≤ 2 ^ 127 := by exact_mod_cast gl
  have e22 := mul128_near z g Z G3 _ _ (2 ^ 110) _ ez eg Z0 ZM gM
  have e22' := e22.trans (show _ ≤ (151 / 100 : ℝ) by norm_num)
  have i22l : mul128 z g ≤ 2 ^ 109 := Nat.div_le_of_le_mul ((Nat.mul_le_mul zl gl).trans (by norm_num))
  have i22M : ((mul128 z g : ℕ) : ℝ) ≤ 2 ^ 109 := by exact_mod_cast i22l
  set I22 : ℝ := Z * G3 / 2 ^ 128 with hI22
  have I220 : 0 ≤ I22 := by positivity
  have I22M : I22 ≤ 2 ^ 109 := by
    rw [hI22, div_le_iff₀ U0]; exact (mul_le_mul ZM G3M G30 (by positivity)).trans (by norm_num)
  have e23 := mul128_near s _ Sg I22 1 _ (2 ^ 119) (2 ^ 109) es e22' Sg0 SgM i22M
  have e23' := e23.trans (show _ ≤ (101 / 100 : ℝ) by norm_num)
  set! Sr : ℝ := Sg + Sg * I22 / 2 ^ 128 with hSr
  have eser : |((s + mul128 s (mul128 z g) : ℕ) : ℝ) - Sr| ≤ 201 / 100 := by
    rw [Nat.cast_add, hSr, show (s : ℝ) + mul128 s (mul128 z g) - (Sg + Sg * I22 / 2 ^ 128) =
      ((s : ℝ) - Sg) + ((mul128 s (mul128 z g) : ℝ) - Sg * I22 / 2 ^ 128) by ring]
    exact (abs_add_le _ _).trans ((add_le_add es e23').trans (by norm_num))
  set! L : ℝ := (Real.log (1 + σ) - Real.log (1 - σ)) / 2 * 2 ^ 128 with hL
  have tail : |L - Sr| ≤ 1 / 100 := by
    have h := log_sub_sum_le σ 7 (by rw [abs_of_nonneg hσ0]; linarith only [hσ])
    norm_num [sum_range_succ, abs_of_nonneg hσ0] at h
    have poly : Sr = 2 ^ 128 * (σ + σ ^ 3 / 3 + σ ^ 5 / 5 + σ ^ 7 / 7 + σ ^ 9 / 9 + σ ^ 11 / 11 + σ ^ 13 / 13) := by
      rw [hSr, hI22]; simp only [G3, G5, G7, G9, G11, G13, hZ, hSg]; push_cast; field_simp; ring
    rw [poly, hL, show (Real.log (1 + σ) - Real.log (1 - σ)) / 2 * 2 ^ 128 -
        2 ^ 128 * (σ + σ ^ 3 / 3 + σ ^ 5 / 5 + σ ^ 7 / 7 + σ ^ 9 / 9 + σ ^ 11 / 11 + σ ^ 13 / 13) =
      2 ^ 128 / 2 * ((Real.log (1 + σ) - Real.log (1 - σ)) - (2 * σ + 2 * (1 / 3) * σ ^ 3 + 2 * (1 / 5) * σ ^ 5 +
        2 * (1 / 7) * σ ^ 7 + 2 * (1 / 9) * σ ^ 9 + 2 * (1 / 11) * σ ^ 11 + 2 * (1 / 13) * σ ^ 13)) by ring,
      abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 128 / 2)]
    have s2 : σ ^ 2 ≤ (1 / 512) ^ 2 := pow_le_pow_left₀ hσ0 hσ 2
    have s15 : σ ^ 15 ≤ (1 / 512) ^ 15 := pow_le_pow_left₀ hσ0 hσ 15
    have d : (99 / 100 : ℝ) ≤ 1 - σ ^ 2 := by linarith only [show ((1 : ℝ) / 512) ^ 2 ≤ 1 / 100 by norm_num, hZ, ZM]
    have hh : |(Real.log (1 + σ) - Real.log (1 - σ)) - (2 * σ + 2 * (1 / 3) * σ ^ 3 + 2 * (1 / 5) * σ ^ 5 +
        2 * (1 / 7) * σ ^ 7 + 2 * (1 / 9) * σ ^ 9 + 2 * (1 / 11) * σ ^ 11 + 2 * (1 / 13) * σ ^ 13)| ≤
        2 * σ ^ 15 / 15 / (1 - σ ^ 2) := by
      convert h using 2; ring
    calc 2 ^ 128 / 2 * |(Real.log (1 + σ) - Real.log (1 - σ)) - (2 * σ + 2 * (1 / 3) * σ ^ 3 + 2 * (1 / 5) * σ ^ 5 +
          2 * (1 / 7) * σ ^ 7 + 2 * (1 / 9) * σ ^ 9 + 2 * (1 / 11) * σ ^ 11 + 2 * (1 / 13) * σ ^ 13)|
        ≤ 2 ^ 128 / 2 * (2 * (1 / 512) ^ 15 / 15 / (99 / 100)) :=
          mul_le_mul_of_nonneg_left (hh.trans (div_le_div₀ (by positivity)
            (div_le_div_of_nonneg_right (by linarith only [s15]) (by norm_num)) (by norm_num) d)) (by positivity)
      _ ≤ 1 / 100 := by norm_num
  have eL : |((s + mul128 s (mul128 z g) : ℕ) : ℝ) - L| ≤ 202 / 100 := by
    calc _ ≤ |((s + mul128 s (mul128 z g) : ℕ) : ℝ) - Sr| + |Sr - L| := abs_sub_le _ _ _
      _ ≤ 201 / 100 + 1 / 100 := add_le_add eser (by rw [abs_sub_comm]; exact tail)
      _ ≤ 202 / 100 := by norm_num
  have L0 : 0 ≤ L := by
    rw [hL]
    have : Real.log (1 - σ) ≤ Real.log (1 + σ) := Real.log_le_log (by linarith only [hσ]) (by linarith only [hσ0])
    have : 0 ≤ (Real.log (1 + σ) - Real.log (1 - σ)) / 2 := by linarith only [this]
    positivity
  have SrM : Sr ≤ 2 ^ 119 + 2 ^ 100 := by
    rw [hSr]
    have : Sg * I22 / 2 ^ 128 ≤ 2 ^ 100 := by
      rw [div_le_iff₀ U0]
      exact (mul_le_mul SgM I22M I220 (by positivity)).trans (by norm_num)
    linarith only [hσ, this]
  have LM : L ≤ 2 ^ 119 + 2 ^ 101 := by linarith only [(abs_le.mp tail).2, SrM]
  have KM : (K : ℝ) ≤ 28855 / 10000 * 2 ^ 126 := by
    have h1 : 2 / Real.log 2 ≤ 288545 / 100000 := by rw [div_le_iff₀ ln0]; linarith only [ln2, ln0]
    have h2 := (abs_le.mp hK).2
    have h3 : 2 / Real.log 2 * 2 ^ 126 ≤ 288545 / 100000 * 2 ^ 126 := mul_le_mul_of_nonneg_right h1 (by positivity)
    linarith only [h1, h2]
  have e18 := mul128_near _ K L (2 / Real.log 2 * 2 ^ 126) _ _ (2 ^ 119 + 2 ^ 101) _ eL hK L0 LM KM
  have e18' := e18.trans (show _ ≤ (246 / 100 : ℝ) by norm_num)
  have av : atanhWideN s = s + mul128 s (mul128 z g) := by
    unfold atanhWideN; dsimp only; rw [hz, hg]
  unfold log2WideN
  rw [av, Nat.cast_add]
  have key : (T : ℝ) + mul128 (s + mul128 s (mul128 z g)) K -
      (Real.logb 2 c + (Real.log (1 + σ) - Real.log (1 - σ)) / Real.log 2) * 2 ^ 126 =
      ((T : ℝ) - Real.logb 2 c * 2 ^ 126) +
        ((mul128 (s + mul128 s (mul128 z g)) K : ℝ) - L * (2 / Real.log 2 * 2 ^ 126) / 2 ^ 128) := by
    rw [hL]
    generalize ((mul128 (s + mul128 s (mul128 z g)) K : ℕ) : ℝ) = M
    generalize Real.log (1 + σ) - Real.log (1 - σ) = D
    generalize Real.logb 2 c = lb
    have l0 := ln0.ne'
    generalize Real.log 2 = l at l0 ⊢
    field_simp; ring
  rw [key]
  exact (abs_add_le _ _).trans ((add_le_add hT e18').trans (by norm_num))

end Fulcrum

end
