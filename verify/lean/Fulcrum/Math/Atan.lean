module

public import Fulcrum.Math.Quarter
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# `atan (c + δ)` of the table (INTERNALS §3.13)

`atanN` is `atan_unit` off the table points on naturals: to the entry
`T ≈ atan c` of `ATAN` it adds `δ - δ z (⅓ - z (⅕ - z/7))`, `z = δ²`, every
product truncated to 62 bits. `atan_series_near`: for `δ ≤ 2^54` the result is
within `1.84` units of `(atan c + atan (δ / 2^62)) · 2^62`. The steps follow the
error budget of §3.13: `z` within `1`, `⅕ - z/7` within `15/7`, the bracket within
`2.21`, `δ z` within `1.004`, its product with the bracket within `1.335`, the
dropped term below `0.001`.

`arctan_split` is the exact remainder `δ = (t - c)/(1 + t c)` of the table point,
`arctan_sub_le` moves a quotient: `atan a - atan b ≤ (a - b)/(1 + a b)`. No code
here: the math of L4.
-/

@[expose] public section

open Finset

namespace Fulcrum

/-- `atan_unit` off the table points on naturals: the entry `T`, the remainder `δ`. -/
def atanN (T δ : ℕ) : ℕ :=
  let z := mul62 δ δ
  let p := 2 ^ 62 / 3 - mul62 z (2 ^ 62 / 5 - z / 7)
  T + δ - mul62 (mul62 δ z) p

/-- `arctan t = arctan c + arctan ((t - c)/(1 + t c))` for `0 ≤ c ≤ t`. -/
theorem arctan_split (t c : ℝ) (hc : 0 ≤ c) (hct : c ≤ t) :
    Real.arctan t = Real.arctan c + Real.arctan ((t - c) / (1 + t * c)) := by
  have p : 0 < 1 + t * c := by nlinarith
  have hD : 1 + t * c ≠ 0 := p.ne'
  have lt : c * ((t - c) / (1 + t * c)) < 1 := by
    rw [mul_div_assoc', div_lt_one p]; nlinarith
  have hw : (t - c) / (1 + t * c) * (1 + t * c) = t - c := div_mul_cancel₀ _ hD
  generalize (t - c) / (1 + t * c) = w at lt hw ⊢
  rw [Real.arctan_add lt]
  congr 1
  rw [eq_div_iff (by linarith)]
  linear_combination -hw

/-- `arctan a - arctan b ≤ (a - b)/(1 + a b)` for `0 ≤ b ≤ a`. -/
theorem arctan_sub_le (a b : ℝ) (hb : 0 ≤ b) (hab : b ≤ a) :
    0 ≤ Real.arctan a - Real.arctan b ∧ Real.arctan a - Real.arctan b ≤ (a - b) / (1 + a * b) := by
  have s := arctan_split a b hb hab
  have q : 0 ≤ (a - b) / (1 + a * b) := div_nonneg (by linarith) (by nlinarith)
  rw [s, add_sub_cancel_left]
  exact ⟨Real.arctan_nonneg.mpr q, Real.arctan_le_self q⟩

/-- A natural difference `a - b` of values within `ea`, `eb` of `A`, `B`, with `b ≤ a`. -/
theorem nat_sub_near (a b : ℕ) (A B ea eb : ℝ) (ha : |(a : ℝ) - A| ≤ ea) (hb : |(b : ℝ) - B| ≤ eb)
    (hab : b ≤ a) : |((a - b : ℕ) : ℝ) - (A - B)| ≤ ea + eb := by
  rw [Nat.cast_sub hab, show (a : ℝ) - b - (A - B) = (a - A) - (b - B) by ring]
  exact (abs_sub _ _).trans (add_le_add ha hb)

set_option maxRecDepth 10000 in
/-- `atan_unit` off the table points: from the entry `T` within `½` of
`atan c · 2^62` and the remainder `δ ≤ 2^54`, `atanN T δ` is within `1.84` units of
`(atan c + atan (δ / 2^62)) · 2^62`; nothing is truncated below zero, and the
result is at most `T + δ`. -/
theorem atan_series_near (T δ : ℕ) (c : ℝ) (hT : |(T : ℝ) - Real.arctan c * 2 ^ 62| ≤ 1 / 2)
    (hδ : δ ≤ 2 ^ 54) :
    |(atanN T δ : ℝ) - (Real.arctan c + Real.arctan (δ / 2 ^ 62)) * 2 ^ 62| ≤ 184 / 100 ∧
      mul62 (mul62 δ (mul62 δ δ)) (2 ^ 62 / 3 - mul62 (mul62 δ δ) (2 ^ 62 / 5 - mul62 δ δ / 7)) ≤ δ := by
  have U0 : (0 : ℝ) < 2 ^ 62 := by positivity
  have hδ' : (δ : ℝ) ≤ 2 ^ 54 := by exact_mod_cast hδ
  have δ0 : (0 : ℝ) ≤ δ := Nat.cast_nonneg δ
  set Z : ℝ := (δ : ℝ) * δ / 2 ^ 62 with hZ
  have Z0 : 0 ≤ Z := by positivity
  have ZM : Z ≤ 2 ^ 46 := by
    rw [hZ, div_le_iff₀ U0]; exact (mul_le_mul hδ' hδ' δ0 (by positivity)).trans (by norm_num)
  have zl : mul62 δ δ ≤ 2 ^ 46 := by
    have : δ * δ ≤ 2 ^ 54 * 2 ^ 54 := Nat.mul_le_mul hδ hδ
    unfold mul62; exact Nat.div_le_of_le_mul (this.trans (by norm_num))
  generalize hz : mul62 δ δ = z at zl ⊢
  have zM : (z : ℝ) ≤ 2 ^ 46 := by exact_mod_cast zl
  have ez : |(z : ℝ) - Z| ≤ 1 := by
    have h := mul62_near δ δ δ δ 0 0 (2 ^ 54) (2 ^ 54) (by simp) (by simp) δ0 hδ' hδ'
    rw [hz] at h; exact h.trans (by norm_num)
  have e9 : |((2 ^ 62 / 5 : ℕ) : ℝ) - 2 ^ 62 / 5| ≤ 1 := by
    have h := div_near (2 ^ 62) 5 (2 ^ 62) 0 (by norm_num) (by norm_num)
    push_cast at h; exact h.trans (by norm_num)
  have e8 : |((2 ^ 62 / 3 : ℕ) : ℝ) - 2 ^ 62 / 3| ≤ 1 := by
    have h := div_near (2 ^ 62) 3 (2 ^ 62) 0 (by norm_num) (by norm_num)
    push_cast at h; exact h.trans (by norm_num)
  have e10 := div_near z 7 Z 1 (by norm_num) ez
  push_cast at e10
  have l10 : z / 7 ≤ 2 ^ 62 / 5 := (Nat.div_le_self z 7).trans (zl.trans (by norm_num))
  have e11 := nat_sub_near _ _ _ _ _ _ e9 e10 l10
  have i11M : ((2 ^ 62 / 5 - z / 7 : ℕ) : ℝ) ≤ 2 ^ 62 / 5 := by
    have : 2 ^ 62 / 5 - z / 7 ≤ 2 ^ 62 / 5 := Nat.sub_le _ _
    exact (Nat.cast_le.mpr this).trans (by norm_num)
  have e12 := mul62_near z (2 ^ 62 / 5 - z / 7) Z (2 ^ 62 / 5 - Z / 7) 1 _ (2 ^ 46) _ ez e11 Z0 ZM i11M
  have l12 : mul62 z (2 ^ 62 / 5 - z / 7) ≤ 2 ^ 62 / 3 :=
    (mul62_le_left _ _ ((Nat.sub_le _ _).trans (by norm_num))).trans (zl.trans (by norm_num))
  have e12' := e12.trans (show _ ≤ (121 / 100 : ℝ) by norm_num)
  have ep := nat_sub_near _ _ _ _ _ _ e8 e12' l12
  have pM : ((2 ^ 62 / 3 - mul62 z (2 ^ 62 / 5 - z / 7) : ℕ) : ℝ) ≤ 2 ^ 62 / 3 := by
    have : 2 ^ 62 / 3 - mul62 z (2 ^ 62 / 5 - z / 7) ≤ 2 ^ 62 / 3 := Nat.sub_le _ _
    exact (Nat.cast_le.mpr this).trans (by norm_num)
  have pU : 2 ^ 62 / 3 - mul62 z (2 ^ 62 / 5 - z / 7) ≤ 2 ^ 62 := (Nat.sub_le _ _).trans (by norm_num)
  set I16 : ℝ := (δ : ℝ) * Z / 2 ^ 62 with hI
  have I0 : 0 ≤ I16 := by positivity
  have IM : I16 ≤ 2 ^ 38 := by
    rw [hI, div_le_iff₀ U0]; exact (mul_le_mul hδ' ZM Z0 (by positivity)).trans (by norm_num)
  have e16 := mul62_near δ z δ Z 0 1 (2 ^ 54) (2 ^ 46) (by simp) ez δ0 hδ' zM
  have e16' := e16.trans (show _ ≤ (1004 / 1000 : ℝ) by norm_num)
  set P : ℝ := 2 ^ 62 / 3 - Z * (2 ^ 62 / 5 - Z / 7) / 2 ^ 62 with hP
  have e17 := mul62_near (mul62 δ z) _ I16 P _ _ (2 ^ 38) _ e16' ep I0 IM pM
  have e17' := e17.trans (show _ ≤ (1335 / 1000 : ℝ) by norm_num)
  have sub : mul62 (mul62 δ z) (2 ^ 62 / 3 - mul62 z (2 ^ 62 / 5 - z / 7)) ≤ δ :=
    (mul62_le_left _ _ pU).trans (mul62_le_left _ _ (zl.trans (by norm_num)))
  refine ⟨?_, sub⟩
  unfold atanN
  dsimp only
  rw [hz]
  have x0 : 0 ≤ (δ : ℝ) / 2 ^ 62 := by positivity
  have xM : (δ : ℝ) / 2 ^ 62 ≤ 1 / 256 := by
    rw [div_le_iff₀ U0]; exact hδ'.trans (by norm_num)
  generalize hx : (δ : ℝ) / 2 ^ 62 = x at x0 xM
  have hδx : (δ : ℝ) = x * 2 ^ 62 := by rw [← hx]; field_simp
  have rs : |Real.arctan x * 2 ^ 62 - ((δ : ℝ) - I16 * P / 2 ^ 62)| ≤ 1 / 1000 := by
    have h := arctan_sub_sum_le x 4 (by rw [abs_of_nonneg x0]; exact xM.trans_lt (by norm_num))
    norm_num [sum_range_succ, abs_of_nonneg x0] at h
    have poly : (δ : ℝ) - I16 * P / 2 ^ 62 = 2 ^ 62 * (x + -x ^ 3 / 3 + x ^ 5 / 5 + -x ^ 7 / 7) := by
      rw [hI, hP, hZ, hδx]; field_simp; ring
    rw [poly, show Real.arctan x * 2 ^ 62 - 2 ^ 62 * (x + -x ^ 3 / 3 + x ^ 5 / 5 + -x ^ 7 / 7) =
      2 ^ 62 * (Real.arctan x - (x + -x ^ 3 / 3 + x ^ 5 / 5 + -x ^ 7 / 7)) by ring,
      abs_mul, abs_of_pos U0]
    refine (mul_le_mul_of_nonneg_left h U0.le).trans ?_
    have x2 : x ^ 2 ≤ (1 / 256) ^ 2 := pow_le_pow_left₀ x0 xM 2
    have x9 : x ^ 9 ≤ (1 / 256) ^ 9 := pow_le_pow_left₀ x0 xM 9
    have d : (99 / 100 : ℝ) ≤ 1 - x ^ 2 := by nlinarith
    calc (2 : ℝ) ^ 62 * (x ^ 9 / 9 / (1 - x ^ 2)) ≤ 2 ^ 62 * ((1 / 256) ^ 9 / 9 / (99 / 100)) :=
          mul_le_mul_of_nonneg_left (div_le_div₀ (by positivity)
            (div_le_div_of_nonneg_right x9 (by norm_num)) (by norm_num) d) U0.le
      _ ≤ 1 / 1000 := by norm_num
  have T1 : mul62 (mul62 δ z) (2 ^ 62 / 3 - mul62 z (2 ^ 62 / 5 - z / 7)) ≤ T + δ := sub.trans (Nat.le_add_left _ _)
  rw [Nat.cast_sub T1, Nat.cast_add]
  have key : (T : ℝ) + δ - mul62 (mul62 δ z) (2 ^ 62 / 3 - mul62 z (2 ^ 62 / 5 - z / 7)) -
      (Real.arctan c + Real.arctan x) * 2 ^ 62 =
      ((T : ℝ) - Real.arctan c * 2 ^ 62) - (Real.arctan x * 2 ^ 62 - ((δ : ℝ) - I16 * P / 2 ^ 62)) -
        ((mul62 (mul62 δ z) (2 ^ 62 / 3 - mul62 z (2 ^ 62 / 5 - z / 7)) : ℝ) - I16 * P / 2 ^ 62) := by ring
  rw [key]
  calc _ ≤ |(T : ℝ) - Real.arctan c * 2 ^ 62| + |Real.arctan x * 2 ^ 62 - ((δ : ℝ) - I16 * P / 2 ^ 62)| +
        |(mul62 (mul62 δ z) (2 ^ 62 / 3 - mul62 z (2 ^ 62 / 5 - z / 7)) : ℝ) - I16 * P / 2 ^ 62| :=
        (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ 1 / 2 + 1 / 1000 + 1335 / 1000 := add_le_add (add_le_add hT rs) e17'
    _ ≤ 184 / 100 := by norm_num

/-- The remainder of `atan_unit`: `k = ⌊256 n / d⌋`, `rest = 256 n mod d` and
`D = 256 d + k n`, so that `atan (n/d) = atan (k/256) + atan (rest / D)`, `rest < d`,
`⌊rest · 2^62 / D⌋ < 2^54`. -/
theorem atan_rest (n d : ℕ) (hd : 0 < d) (hnd : n ≤ d) :
    256 * n / d ≤ 256 ∧ 256 * n % d < d ∧ 256 * n % d * 2 ^ 62 / (256 * d + 256 * n / d * n) ≤ 2 ^ 54 ∧
    Real.arctan ((n : ℝ) / d) = Real.arctan (((256 * n / d : ℕ) : ℝ) / 256) +
      Real.arctan (((256 * n % d : ℕ) : ℝ) / ((256 * d + 256 * n / d * n : ℕ) : ℝ)) := by
  have k256 : 256 * n / d ≤ 256 := Nat.div_le_of_le_mul (by rw [mul_comm d]; exact Nat.mul_le_mul_left _ hnd)
  have rl : 256 * n % d < d := Nat.mod_lt _ hd
  refine ⟨k256, rl, Nat.div_le_of_le_mul ?_, ?_⟩
  · calc 256 * n % d * 2 ^ 62 ≤ d * 2 ^ 62 := Nat.mul_le_mul_right _ rl.le
      _ ≤ 2 ^ 54 * (256 * d + 256 * n / d * n) := by
          have : d * 2 ^ 62 = 2 ^ 54 * (256 * d) := by ring
          rw [this]; exact Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
      _ = (256 * d + 256 * n / d * n) * 2 ^ 54 := Nat.mul_comm _ _
  · have dp : (0 : ℝ) < d := by exact_mod_cast hd
    have k0 : (0 : ℝ) ≤ ((256 * n / d : ℕ) : ℝ) := Nat.cast_nonneg _
    have r0 : (0 : ℝ) ≤ ((256 * n % d : ℕ) : ℝ) := Nat.cast_nonneg _
    have e : (256 * n % d : ℕ) + d * (256 * n / d) = 256 * n := Nat.mod_add_div _ _
    have e' : ((256 * n % d : ℕ) : ℝ) = 256 * n - d * ((256 * n / d : ℕ) : ℝ) := by
      have : (((256 * n % d : ℕ) + d * (256 * n / d) : ℕ) : ℝ) = ((256 * n : ℕ) : ℝ) := by rw [e]
      push_cast at this ⊢; linarith
    push_cast
    rw [e'] at r0 ⊢
    generalize ((256 * n / d : ℕ) : ℝ) = k at r0 k0 ⊢
    have cle : k / 256 ≤ (n : ℝ) / d := by
      rw [div_le_div_iff₀ (by norm_num) dp]; linarith
    rw [arctan_split _ _ (by positivity) cle]
    congr 2
    have : (256 : ℝ) * d + k * n ≠ 0 := by positivity
    field_simp

/-- `atanN T 0 = T`: without a remainder `atan_unit` is the table entry. -/
theorem atanN_zero (T : ℕ) : atanN T 0 = T := by
  simp [atanN, mul62]

/-- `atan_unit` on naturals: for `n ≤ d`, `0 < d`, the entry `T` of
`k = ⌊256 n / d⌋` within `½` of `atan (k/256) · 2^62` and the remainder
`⌊(256 n mod d) · 2^62 / (256 d + k n)⌋`, `atanN` is within `2.9` units of
`atan (n/d) · 2^62`: `1.84` of the series and `1` of the floor of the remainder. -/
theorem atan_unit_near (n d T : ℕ) (hd : 0 < d) (hnd : n ≤ d)
    (hT : |(T : ℝ) - Real.arctan (((256 * n / d : ℕ) : ℝ) / 256) * 2 ^ 62| ≤ 1 / 2) :
    |(atanN T (256 * n % d * 2 ^ 62 / (256 * d + 256 * n / d * n)) : ℝ) -
      Real.arctan ((n : ℝ) / d) * 2 ^ 62| ≤ 29 / 10 := by
  obtain ⟨_, _, hδ, split⟩ := atan_rest n d hd hnd
  have a := (atan_series_near T _ _ hT hδ).1
  have Dp : 0 < 256 * d + 256 * n / d * n := by positivity
  have ⟨l, u⟩ := floor_div_near (256 * n % d * 2 ^ 62) _ Dp
  rw [split]
  generalize (256 * n % d * 2 ^ 62 / (256 * d + 256 * n / d * n) : ℕ) = δ at a l u
  set x : ℝ := ((256 * n % d : ℕ) : ℝ) / ((256 * d + 256 * n / d * n : ℕ) : ℝ) with hx
  have U0 : (0 : ℝ) < 2 ^ 62 := by positivity
  have ex : ((256 * n % d * 2 ^ 62 : ℕ) : ℝ) / ((256 * d + 256 * n / d * n : ℕ) : ℝ) = x * 2 ^ 62 := by
    rw [hx]; push_cast; ring
  rw [ex] at l u
  have b : (δ : ℝ) / 2 ^ 62 ≤ x := by rw [div_le_iff₀ U0]; exact l
  have ⟨s0, s1⟩ := arctan_sub_le x (δ / 2 ^ 62) (by positivity) b
  have s2 : (x - δ / 2 ^ 62) / (1 + x * (δ / 2 ^ 62)) ≤ x - δ / 2 ^ 62 :=
    div_le_self (sub_nonneg.mpr b) (le_add_of_nonneg_right (mul_nonneg ((by positivity : (0 : ℝ) ≤ δ / 2 ^ 62).trans b) (by positivity)))
  have s3 : (x - δ / 2 ^ 62) * 2 ^ 62 ≤ 1 := by
    rw [sub_mul, div_mul_cancel₀ _ U0.ne']; linarith
  have d1 : |(Real.arctan x - Real.arctan (δ / 2 ^ 62)) * 2 ^ 62| ≤ 1 := by
    rw [abs_of_nonneg (mul_nonneg s0 U0.le)]
    exact (mul_le_mul_of_nonneg_right (s1.trans s2) U0.le).trans s3
  have key : (atanN T δ : ℝ) - (Real.arctan (((256 * n / d : ℕ) : ℝ) / 256) + Real.arctan x) * 2 ^ 62 =
      ((atanN T δ : ℝ) - (Real.arctan (((256 * n / d : ℕ) : ℝ) / 256) + Real.arctan (δ / 2 ^ 62)) * 2 ^ 62) -
        (Real.arctan x - Real.arctan (δ / 2 ^ 62)) * 2 ^ 62 := by ring
  rw [key]
  exact (abs_sub _ _).trans ((add_le_add a d1).trans (by norm_num))

/-- `arg (d + n i) = atan (n/d)` for `0 < d`. -/
theorem arg_of_pos (d n : ℝ) (hd : 0 < d) : Complex.arg ⟨d, n⟩ = Real.arctan (n / d) := by
  rw [Complex.arg_of_re_nonneg hd.le, Complex.norm_eq_sqrt_sq_add_sq, Real.arctan_eq_arcsin]
  congr 1
  have e : √(1 + (n / d) ^ 2) = √(d ^ 2 + n ^ 2) / d := by
    rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity), div_mul_div_comm,
      Real.mul_self_sqrt (by positivity)]
    field_simp
  rw [e, div_div_div_cancel_right₀ hd.ne']

/-- `arg (d + n i) = π/2 - atan (d/n)` for `0 ≤ d`, `0 < n`. -/
theorem arg_compl (d n : ℝ) (hd : 0 ≤ d) (hn : 0 < n) :
    Complex.arg ⟨d, n⟩ = Real.pi / 2 - Real.arctan (d / n) := by
  rcases hd.lt_or_eq with hd | hd
  · rw [arg_of_pos d n hd, ← Real.arctan_inv_of_pos (by positivity), inv_div]
  · subst hd
    rw [zero_div, Real.arctan_zero, sub_zero]
    exact Complex.arg_eq_pi_div_two_iff.mpr ⟨rfl, hn⟩

/-- `arg (x + y i)` from the angle of `|x| + |y| i` in the first quadrant: `π`
minus it for `x < 0`, negated for `y < 0`. -/
theorem arg_signs (x y : ℝ) : Complex.arg ⟨x, y⟩ =
    (if y < 0 then -1 else 1) * (if x < 0 then Real.pi - Complex.arg ⟨|x|, |y|⟩ else Complex.arg ⟨|x|, |y|⟩) := by
  have N : ‖(⟨|x|, |y|⟩ : ℂ)‖ = ‖(⟨x, y⟩ : ℂ)‖ := by
    rw [Complex.norm_eq_sqrt_sq_add_sq, Complex.norm_eq_sqrt_sq_add_sq]; simp only [sq_abs]
  rw [Complex.arg_of_re_nonneg (show (0 : ℝ) ≤ (⟨|x|, |y|⟩ : ℂ).re from abs_nonneg x), N]
  dsimp only
  by_cases hx : x < 0
  · by_cases hy : y < 0
    · rw [Complex.arg_of_re_neg_of_im_neg hx hy, Complex.neg_im, ite_eq_left hy, ite_eq_left hx, abs_of_neg hy, neg_div]; ring
    · rw [Complex.arg_of_re_neg_of_im_nonneg hx (not_lt.mp hy), Complex.neg_im, ite_eq_right hy, ite_eq_left hx,
        abs_of_nonneg (not_lt.mp hy), neg_div, Real.arcsin_neg]; ring
  · rw [Complex.arg_of_re_nonneg (not_lt.mp hx), ite_eq_right hx]
    by_cases hy : y < 0
    · rw [ite_eq_left hy, abs_of_neg hy, neg_div, Real.arcsin_neg]; ring
    · rw [ite_eq_right hy, abs_of_nonneg (not_lt.mp hy), one_mul]

/-- `arg (s + X i) = asin (X / U)` on the circle `X² + s² = U²`, `0 ≤ s`, `0 < U`. -/
theorem arg_circle (s X U : ℝ) (hs : 0 ≤ s) (hU : 0 < U) (h : X ^ 2 + s ^ 2 = U ^ 2) :
    Complex.arg ⟨s, X⟩ = Real.arcsin (X / U) := by
  rw [Complex.arg_of_re_nonneg hs, Complex.norm_eq_sqrt_sq_add_sq]
  dsimp only
  rw [add_comm, h, Real.sqrt_sq hU.le]

/-- The root below the exact one moves the angle little: for `X² + s² = U²`,
`0 < X`, `0 ≤ ŝ ≤ s < ŝ + 1`, `atan (s/X)` and `atan (ŝ/X)` differ by at most
`1 / (U - 1)`. -/
theorem arctan_root_near (X s ŝ U : ℝ) (hX : 0 < X) (hŝ : 0 ≤ ŝ) (hs : ŝ ≤ s) (hs1 : s < ŝ + 1)
    (hU : 2 ≤ U) (h : X ^ 2 + s ^ 2 = U ^ 2) :
    |Real.arctan (s / X) - Real.arctan (ŝ / X)| ≤ 1 / (U - 1) := by
  have ⟨d0, d1⟩ := arctan_sub_le (s / X) (ŝ / X) (by positivity) (div_le_div_of_nonneg_right hs hX.le)
  rw [abs_of_nonneg d0]
  refine d1.trans ?_
  have sU : s ≤ U := by nlinarith
  have XU : X ≤ U := by nlinarith
  have e : (s / X - ŝ / X) / (1 + s / X * (ŝ / X)) = (s - ŝ) * X / (X ^ 2 + s * ŝ) := by
    field_simp
  have sp : 0 ≤ s * ŝ := mul_nonneg (hŝ.trans hs) hŝ
  rw [e, div_le_div_iff₀ (by nlinarith) (by linarith)]
  have XU1 : 0 ≤ X * (U - 1) := mul_nonneg hX.le (by linarith)
  have h1 : (s - ŝ) * (X * (U - 1)) ≤ X * (U - 1) :=
    (mul_le_mul_of_nonneg_right (by linarith) XU1).trans_eq (one_mul _)
  have h2 : s ^ 2 - s ≤ s * ŝ := by nlinarith [hŝ.trans hs]
  have h3 : X * (U - 1) ≤ U * (U - 1) := mul_le_mul_of_nonneg_right XU (by linarith)
  nlinarith

/-- The integer root of `asin` and `acos`: for `X ≤ 2^62` and `ŝ = ⌊√(2^124 - X²)⌋`,
`arg (ŝ + X i)` is within `1 / (2^62 - 1)` of `asin (X / 2^62)` and `arg (X + ŝ i)`
of `acos (X / 2^62)`. -/
theorem root_angles_near (X : ℕ) (hX : X ≤ 2 ^ 62) :
    |Complex.arg ⟨(Nat.sqrt (2 ^ 124 - X ^ 2) : ℝ), (X : ℝ)⟩ - Real.arcsin (X / 2 ^ 62)| ≤ 1 / (2 ^ 62 - 1) ∧
    |Complex.arg ⟨(X : ℝ), (Nat.sqrt (2 ^ 124 - X ^ 2) : ℝ)⟩ - Real.arccos (X / 2 ^ 62)| ≤ 1 / (2 ^ 62 - 1) := by
  have U0 : (0 : ℝ) < 2 ^ 62 := by positivity
  have X2 : X ^ 2 ≤ 2 ^ 124 := by
    calc X ^ 2 ≤ (2 ^ 62) ^ 2 := Nat.pow_le_pow_left hX 2
      _ = 2 ^ 124 := by norm_num
  have cast : ((2 ^ 124 - X ^ 2 : ℕ) : ℝ) = (2 ^ 62) ^ 2 - (X : ℝ) ^ 2 := by
    rw [Nat.cast_sub X2]; push_cast; norm_num
  have l := Real.nat_sqrt_le_real_sqrt (a := 2 ^ 124 - X ^ 2)
  have u := Real.real_sqrt_lt_nat_sqrt_succ (a := 2 ^ 124 - X ^ 2)
  rw [cast] at l u
  set s := √((2 ^ 62) ^ 2 - (X : ℝ) ^ 2) with hs
  have ŝ0 : (0 : ℝ) ≤ (Nat.sqrt (2 ^ 124 - X ^ 2) : ℕ) := Nat.cast_nonneg _
  generalize ((Nat.sqrt (2 ^ 124 - X ^ 2) : ℕ) : ℝ) = ŝ at l u ŝ0 ⊢
  have XU : (X : ℝ) ≤ 2 ^ 62 := by exact_mod_cast hX
  have X0 : (0 : ℝ) ≤ X := Nat.cast_nonneg _
  have s0 : 0 ≤ s := Real.sqrt_nonneg _
  have ss : (X : ℝ) ^ 2 + s ^ 2 = (2 ^ 62) ^ 2 := by
    rw [hs, Real.sq_sqrt (by nlinarith)]; ring
  have asin_e : Real.arcsin (X / 2 ^ 62) = Complex.arg ⟨s, (X : ℝ)⟩ := (arg_circle s X _ s0 U0 ss).symm
  have acos_e : Real.arccos (X / 2 ^ 62) = Complex.arg ⟨(X : ℝ), s⟩ := by
    rw [Real.arccos_eq_arcsin (by positivity), arg_circle (X : ℝ) s _ X0 U0 (by linarith)]
    congr 1
    rw [hs, Real.sqrt_eq_iff_mul_self_eq (by nlinarith [div_le_one_of_le₀ XU U0.le, div_nonneg X0 U0.le])
      (by positivity), div_mul_div_comm, Real.mul_self_sqrt (by nlinarith)]
    field_simp
  rw [asin_e, acos_e]
  have pos : (0 : ℝ) ≤ 1 / (2 ^ 62 - 1) := by norm_num
  rcases X0.lt_or_eq with Xp | Xz
  · have r := arctan_root_near X s ŝ (2 ^ 62) Xp ŝ0 l u (by norm_num) ss
    refine ⟨?_, ?_⟩
    · rw [arg_compl _ _ ŝ0 Xp, arg_compl _ _ s0 Xp, show Real.pi / 2 - Real.arctan (ŝ / X) -
        (Real.pi / 2 - Real.arctan (s / X)) = Real.arctan (s / X) - Real.arctan (ŝ / X) by ring]
      exact r
    · rw [arg_of_pos _ _ Xp, arg_of_pos _ _ Xp, abs_sub_comm]
      exact r
  · rw [← Xz] at ss ⊢
    have sU : s = 2 ^ 62 := by nlinarith
    have ŝp : 0 < ŝ := by rw [sU] at u; linarith
    refine ⟨?_, ?_⟩
    · rw [arg_of_pos _ _ ŝp, arg_of_pos _ _ (by rw [sU]; positivity)]
      simpa using pos
    · rw [arg_compl _ _ le_rfl ŝp, arg_compl _ _ le_rfl (by rw [sU]; positivity)]
      simpa using pos

end Fulcrum

end
