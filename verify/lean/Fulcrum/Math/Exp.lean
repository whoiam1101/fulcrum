module

public import Fulcrum.Math.Fixed
public import Fulcrum.Math.Series

/-!
# `e^y - 1` of the remainder (INTERNALS §3.16)

`expm1N` is `exp::expm1` on naturals: `y` with 72 fractional bits, the Horner steps
`G = 1/720 + y/5040`, `1/120 + y G`, `1/24 + y G`, `1/6 + y G` and `H = 1/2 + y G` at
64 fractional bits, `z = y²` at 72 bits, then `y + z H`, every product truncated.
`expm1_series_near`: for `y ≤ 2^64` (`y / 2^72 ≤ 2^-8`) the result is within `1.6` units
of `(e^(y / 2^72) - 1) · 2^72`. Each Horner step adds two floors to `2^-8` of the error
before it, so `H` is within `2.01` units of its exact value; the product `z H` is within
`1.52`, the dropped terms from `y^8/8!` below `0.02`. `exp_unit_near`: a table entry within
`½` of `T` plus the products of its halves with `e` within `1.6` of `E · 2^72` is within
`0.81 · 2^56` of `T (1 + E)`. No code here: the math of L4.
-/

@[expose] public section

open Finset

namespace Fulcrum

/-- `exp::expm1` on naturals. -/
def expm1N (y : ℕ) : ℕ :=
  let g := 2 ^ 64 / 720 + y * (2 ^ 64 / 5040) / 2 ^ 72
  let g := 2 ^ 64 / 120 + y * g / 2 ^ 72
  let g := 2 ^ 64 / 24 + y * g / 2 ^ 72
  let g := 2 ^ 64 / 6 + y * g / 2 ^ 72
  let h := 2 ^ 64 / 2 + y * g / 2 ^ 72
  y + y * y / 2 ^ 72 * h / 2 ^ 64

/-- `2^64 / n` truncated is within `1` of `2^64 / N` for `N = n`. -/
theorem pow64_div_near (n : ℕ) (N : ℝ) (hN : (n : ℝ) = N) (hn : 0 < n) :
    |((2 ^ 64 / n : ℕ) : ℝ) - 2 ^ 64 / N| ≤ 1 := by
  have h := div_near (2 ^ 64) n (2 ^ 64) 0 hn (by norm_num)
  rw [zero_div, zero_add, hN] at h
  exact h

/-- One Horner step `c + ⌊y g / 2^72⌋` of a `c` within `1` of `C` and a `g` within `e` of
`G`, `y ≤ 2^64`: within `2 + e / 2^8` of `C + y G / 2^72`. -/
theorem horner_step (c y g : ℕ) (C G e : ℝ) (hc : |(c : ℝ) - C| ≤ 1) (hg : |(g : ℝ) - G| ≤ e)
    (hy : y ≤ 2 ^ 64) :
    |((c + y * g / 2 ^ 72 : ℕ) : ℝ) - (C + y * G / 2 ^ 72)| ≤ 2 + e / 2 ^ 8 := by
  have yM : (y : ℝ) ≤ 2 ^ 64 := by exact_mod_cast hy
  have d := div_near (y * g) (2 ^ 72) (y * G) (2 ^ 64 * e) (by positivity) (by
    rw [Nat.cast_mul, ← mul_sub, abs_mul, Nat.abs_cast]
    exact mul_le_mul yM hg (abs_nonneg _) (by positivity))
  simp only [Nat.cast_pow, Nat.cast_ofNat] at d
  rw [Nat.cast_add, show (c : ℝ) + ((y * g / 2 ^ 72 : ℕ) : ℝ) - (C + y * G / 2 ^ 72) =
    ((c : ℝ) - C) + (((y * g / 2 ^ 72 : ℕ) : ℝ) - y * G / 2 ^ 72) by ring]
  refine (abs_add_le _ _).trans ?_
  have : 2 ^ 64 * e / 2 ^ 72 = e / 2 ^ 8 := by field_simp
  rw [this] at d
  linarith

/-- A Horner step is at most `c + g` when `y ≤ 2^72`. -/
theorem horner_step_le (c y g : ℕ) (hy : y ≤ 2 ^ 72) : c + y * g / 2 ^ 72 ≤ c + g :=
  Nat.add_le_add_left (Nat.div_le_of_le_mul (Nat.mul_le_mul_right g hy)) _

/-- `exp::expm1` off the code: for `y ≤ 2^64`, `expm1N y` is within `1.6` units of
`(e^(y / 2^72) - 1) · 2^72`, and at most `y + 2^56`. -/
theorem expm1_series_near (y : ℕ) (hy : y ≤ 2 ^ 64) :
    |(expm1N y : ℝ) - (Real.exp (y / 2 ^ 72) - 1) * 2 ^ 72| ≤ 16 / 10 ∧ expm1N y ≤ y + 2 ^ 56 := by
  have yM : (y : ℝ) ≤ 2 ^ 64 := by exact_mod_cast hy
  have y0 : (0 : ℝ) ≤ y := Nat.cast_nonneg y
  set u : ℝ := y / 2 ^ 72 with hu
  have u0 : 0 ≤ u := by positivity
  have yu : (y : ℝ) = u * 2 ^ 72 := by rw [hu]; field_simp
  have u1 : u ≤ 1 / 2 ^ 8 := by
    rw [hu, div_le_div_iff₀ (by positivity) (by positivity)]; linarith
  set G0 : ℝ := 2 ^ 64 / 720 + y * (2 ^ 64 / 5040) / 2 ^ 72
  set G1 : ℝ := 2 ^ 64 / 120 + y * G0 / 2 ^ 72
  set G2 : ℝ := 2 ^ 64 / 24 + y * G1 / 2 ^ 72
  set G3 : ℝ := 2 ^ 64 / 6 + y * G2 / 2 ^ 72
  set H : ℝ := 2 ^ 64 / 2 + y * G3 / 2 ^ 72 with hH
  set g0 : ℕ := 2 ^ 64 / 720 + y * (2 ^ 64 / 5040) / 2 ^ 72 with hg0
  set g1 : ℕ := 2 ^ 64 / 120 + y * g0 / 2 ^ 72 with hg1
  set g2 : ℕ := 2 ^ 64 / 24 + y * g1 / 2 ^ 72 with hg2
  set g3 : ℕ := 2 ^ 64 / 6 + y * g2 / 2 ^ 72 with hg3
  set h : ℕ := 2 ^ 64 / 2 + y * g3 / 2 ^ 72 with hh
  have e0 : |(g0 : ℝ) - G0| ≤ 2 + 1 / 2 ^ 8 := horner_step _ y _ _ _ 1
    (pow64_div_near 720 720 (by norm_num) (by norm_num)) (pow64_div_near 5040 5040 (by norm_num) (by norm_num)) hy
  have e1 : |(g1 : ℝ) - G1| ≤ _ := horner_step _ y _ _ _ _ (pow64_div_near 120 120 (by norm_num) (by norm_num)) e0 hy
  have e2 : |(g2 : ℝ) - G2| ≤ _ := horner_step _ y _ _ _ _ (pow64_div_near 24 24 (by norm_num) (by norm_num)) e1 hy
  have e3 : |(g3 : ℝ) - G3| ≤ _ := horner_step _ y _ _ _ _ (pow64_div_near 6 6 (by norm_num) (by norm_num)) e2 hy
  have e4 : |(h : ℝ) - H| ≤ _ := horner_step _ y _ _ _ _ (pow64_div_near 2 2 (by norm_num) (by norm_num)) e3 hy
  have eH : |(h : ℝ) - H| ≤ 201 / 100 := e4.trans (by norm_num)
  have Hp : H = 2 ^ 64 * (1 / 2 + u / 6 + u ^ 2 / 24 + u ^ 3 / 120 + u ^ 4 / 720 + u ^ 5 / 5040) := by
    simp only [hH, G3, G2, G1, G0]; rw [yu]; ring
  have H0 : 0 ≤ H := by rw [Hp]; positivity
  have HM : H ≤ 2 ^ 64 * (1 / 2 + 1 / 2 ^ 8) := by
    rw [Hp]
    have u2 : u ^ 2 ≤ u := pow_le_of_le_one u0 (u1.trans (by norm_num)) two_ne_zero
    have u3 : u ^ 3 ≤ u := pow_le_of_le_one u0 (u1.trans (by norm_num)) (by norm_num)
    have u4 : u ^ 4 ≤ u := pow_le_of_le_one u0 (u1.trans (by norm_num)) (by norm_num)
    have u5 : u ^ 5 ≤ u := pow_le_of_le_one u0 (u1.trans (by norm_num)) (by norm_num)
    have : (0 : ℝ) < 2 ^ 64 := by positivity
    nlinarith
  have hM : (h : ℝ) ≤ 2 ^ 64 * (1 / 2 + 1 / 2 ^ 8) + 201 / 100 := by linarith [(abs_le.mp eH).2]
  set Z : ℝ := (y : ℝ) * y / 2 ^ 72 with hZ
  have Z0 : 0 ≤ Z := by positivity
  have ZM : Z ≤ 2 ^ 56 := by
    rw [hZ, div_le_iff₀ (by positivity)]
    exact (mul_le_mul yM yM y0 (by positivity)).trans (by norm_num)
  have ez : |((y * y / 2 ^ 72 : ℕ) : ℝ) - Z| ≤ 1 := by
    have := div_near (y * y) (2 ^ 72) ((y : ℝ) * y) 0 (by positivity) (by simp)
    simp only [Nat.cast_pow, Nat.cast_ofNat, zero_div, zero_add] at this; exact this
  have zl : y * y / 2 ^ 72 ≤ 2 ^ 56 := Nat.div_le_of_le_mul ((Nat.mul_le_mul hy hy).trans (by norm_num))
  generalize hz : y * y / 2 ^ 72 = z at ez zl
  have zM : (z : ℝ) ≤ 2 ^ 56 := by exact_mod_cast zl
  have ep := div_near (z * h) (2 ^ 64) (Z * H) (1 * (2 ^ 64 * (1 / 2 + 1 / 2 ^ 8) + 201 / 100) + 2 ^ 56 * (201 / 100))
    (by positivity) (by
      rw [Nat.cast_mul, show (z : ℝ) * h - Z * H = (z - Z) * h + Z * (h - H) by ring]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul, Nat.abs_cast]; exact mul_le_mul ez hM (Nat.cast_nonneg _) zero_le_one
      · rw [abs_mul, abs_of_nonneg Z0]; exact mul_le_mul ZM eH (abs_nonneg _) (by positivity))
  simp only [Nat.cast_pow, Nat.cast_ofNat] at ep
  have tail : |(Real.exp u - 1) * 2 ^ 72 - (y + Z * H / 2 ^ 64)| ≤ 2 / 100 := by
    have t := exp_sub_sum_le u 8 (by rw [abs_of_nonneg u0]; linarith)
    norm_num [sum_range_succ, Nat.factorial, abs_of_nonneg u0] at t
    have poly : (y : ℝ) + Z * H / 2 ^ 64 =
        2 ^ 72 * (u + u ^ 2 / 2 + u ^ 3 / 6 + u ^ 4 / 24 + u ^ 5 / 120 + u ^ 6 / 720 + u ^ 7 / 5040) := by
      rw [Hp, hZ, yu]; ring
    rw [poly, show (Real.exp u - 1) * 2 ^ 72 -
        2 ^ 72 * (u + u ^ 2 / 2 + u ^ 3 / 6 + u ^ 4 / 24 + u ^ 5 / 120 + u ^ 6 / 720 + u ^ 7 / 5040) =
        2 ^ 72 * (Real.exp u - (1 + u + u ^ 2 / 2 + u ^ 3 / 6 + u ^ 4 / 24 + u ^ 5 / 120 + u ^ 6 / 720 +
          u ^ 7 / 5040)) by ring, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 72)]
    have u8 : u ^ 8 ≤ (1 / 2 ^ 8) ^ 8 := pow_le_pow_left₀ u0 u1 8
    have d : (1 : ℝ) / 2 ≤ 1 - u / 9 := by linarith
    have hh : |Real.exp u - (1 + u + u ^ 2 / 2 + u ^ 3 / 6 + u ^ 4 / 24 + u ^ 5 / 120 + u ^ 6 / 720 +
        u ^ 7 / 5040)| ≤ u ^ 8 / 40320 / (1 - u / 9) := by
      convert t using 2
    calc 2 ^ 72 * |Real.exp u - (1 + u + u ^ 2 / 2 + u ^ 3 / 6 + u ^ 4 / 24 + u ^ 5 / 120 + u ^ 6 / 720 +
          u ^ 7 / 5040)| ≤ 2 ^ 72 * ((1 / 2 ^ 8) ^ 8 / 40320 / (1 / 2)) :=
          mul_le_mul_of_nonneg_left (hh.trans (div_le_div₀ (by positivity)
            (div_le_div_of_nonneg_right u8 (by norm_num)) (by norm_num) d)) (by positivity)
      _ ≤ 2 / 100 := by norm_num
  have code : expm1N y = y + z * h / 2 ^ 64 := by
    unfold expm1N; dsimp only; rw [← hz]
  rw [code]
  refine ⟨?_, ?_⟩
  · rw [Nat.cast_add, show (y : ℝ) + ((z * h / 2 ^ 64 : ℕ) : ℝ) - (Real.exp (y / 2 ^ 72) - 1) * 2 ^ 72 =
      (((z * h / 2 ^ 64 : ℕ) : ℝ) - Z * H / 2 ^ 64) - ((Real.exp u - 1) * 2 ^ 72 - (y + Z * H / 2 ^ 64)) by
        rw [hu]; ring]
    refine (abs_sub _ _).trans ?_
    have : (1 * (2 ^ 64 * (1 / 2 + 1 / 2 ^ 8) + 201 / 100) + 2 ^ 56 * (201 / 100) : ℝ) / 2 ^ 64 + 1 + 2 / 100 ≤
        16 / 10 := by norm_num
    linarith
  · have : ((z * h / 2 ^ 64 : ℕ) : ℝ) ≤ 2 ^ 56 := by
      have := (abs_le.mp ep).2
      have : Z * H / 2 ^ 64 ≤ 2 ^ 56 * (2 ^ 64 * (1 / 2 + 1 / 2 ^ 8)) / 2 ^ 64 :=
        div_le_div_of_nonneg_right (mul_le_mul ZM HM H0 (by positivity)) (by positivity)
      have : (1 * (2 ^ 64 * (1 / 2 + 1 / 2 ^ 8) + 201 / 100) + 2 ^ 56 * (201 / 100) : ℝ) / 2 ^ 64 + 1 ≤ 2 := by
        norm_num
      have : (2 ^ 56 * (2 ^ 64 * (1 / 2 + 1 / 2 ^ 8)) / 2 ^ 64 : ℝ) ≤ 2 ^ 56 - 2 := by norm_num
      linarith
    have : z * h / 2 ^ 64 ≤ 2 ^ 56 := by exact_mod_cast this
    omega

/-- `expm1N` is monotone. -/
theorem expm1N_mono (y y' : ℕ) (h : y ≤ y') : expm1N y ≤ expm1N y' := by
  have st : ∀ c g g' : ℕ, g ≤ g' → c + y * g / 2 ^ 72 ≤ c + y' * g' / 2 ^ 72 := fun c g g' hg =>
    Nat.add_le_add_left (Nat.div_le_div_right (Nat.mul_le_mul h hg)) c
  unfold expm1N
  dsimp only
  exact Nat.add_le_add h (Nat.div_le_div_right (Nat.mul_le_mul (Nat.div_le_div_right (Nat.mul_le_mul h h))
    (st _ _ _ (st _ _ _ (st _ _ _ (st _ _ _ (st _ _ _ le_rfl)))))))

/-- `exp::exp_unit` off the code: the table entry `t < 2^127` within `½` of `T`, plus the
products of its halves with `e` within `1.6` of `E · 2^72`, `0 ≤ E ≤ 1`, is within
`0.81 · 2^56` of `T · (1 + E)`, and at most `t + ⌊t · e / 2^72⌋`. -/
theorem exp_unit_near (t e : ℕ) (T E : ℝ) (ht : |(t : ℝ) - T| ≤ 1 / 2) (he : |(e : ℝ) - E * 2 ^ 72| ≤ 16 / 10)
    (htM : t < 2 ^ 127) (E0 : 0 ≤ E) (E1 : E ≤ 1) :
    |((t + t / 2 ^ 64 * e / 2 ^ 8 + t % 2 ^ 64 * e / 2 ^ 72 : ℕ) : ℝ) - T * (1 + E)| ≤ 81 / 100 * 2 ^ 56 ∧
      t + t / 2 ^ 64 * e / 2 ^ 8 + t % 2 ^ 64 * e / 2 ^ 72 ≤ t + t * e / 2 ^ 72 := by
  have split : (t : ℝ) * e / 2 ^ 72 = ((t / 2 ^ 64 : ℕ) : ℝ) * e / 2 ^ 8 + ((t % 2 ^ 64 : ℕ) : ℝ) * e / 2 ^ 72 := by
    have : (t : ℝ) = ((t / 2 ^ 64 : ℕ) : ℝ) * 2 ^ 64 + ((t % 2 ^ 64 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.div_add_mod' t (2 ^ 64)).symm
    rw [this]; field_simp
  have ⟨a1, a2⟩ := floor_div_near (t / 2 ^ 64 * e) (2 ^ 8) (by positivity)
  have ⟨b1, b2⟩ := floor_div_near (t % 2 ^ 64 * e) (2 ^ 72) (by positivity)
  push_cast at a1 a2 b1 b2
  have tM : (t : ℝ) ≤ 2 ^ 127 := by exact_mod_cast htM.le
  have core : |(t : ℝ) + t * e / 2 ^ 72 - T * (1 + E)| ≤ 1 + 2 ^ 127 * (16 / 10) / 2 ^ 72 := by
    rw [show (t : ℝ) + t * e / 2 ^ 72 - T * (1 + E) = ((t : ℝ) - T) * (1 + E) + t * (((e : ℝ) - E * 2 ^ 72) / 2 ^ 72) by
      field_simp; ring]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 + E)]
      exact (mul_le_mul ht (by linarith : 1 + E ≤ 2) (by linarith) (by norm_num)).trans (by norm_num)
    · rw [abs_mul, Nat.abs_cast, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 72), mul_div_assoc']
      exact div_le_div_of_nonneg_right (mul_le_mul tM he (abs_nonneg _) (by positivity)) (by positivity)
  refine ⟨?_, ?_⟩
  · push_cast
    have ⟨c1, c2⟩ := abs_le.mp core
    have : (1 + 2 ^ 127 * (16 / 10) / 2 ^ 72 : ℝ) + 2 ≤ 81 / 100 * 2 ^ 56 := by norm_num
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · have : t / 2 ^ 64 * e / 2 ^ 8 + t % 2 ^ 64 * e / 2 ^ 72 ≤ t * e / 2 ^ 72 := by
      have h1 : t / 2 ^ 64 * e / 2 ^ 8 = t / 2 ^ 64 * 2 ^ 64 * e / 2 ^ 72 := by
        rw [show t / 2 ^ 64 * 2 ^ 64 * e = t / 2 ^ 64 * e * 2 ^ 64 by ring,
          show (2 : ℕ) ^ 72 = 2 ^ 8 * 2 ^ 64 by norm_num, Nat.mul_div_mul_right _ _ (by positivity)]
      rw [h1]
      refine Nat.div_add_div_le_add_div.trans (Nat.div_le_div_right (le_of_eq ?_))
      rw [← add_mul, Nat.div_add_mod' t (2 ^ 64)]
    omega

end Fulcrum

end
