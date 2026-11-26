module

public import Fulcrum.Math.Fixed
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Fulcrum.Math.Quarter
import Fulcrum.Math.Series
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Pi.Bounds

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
`arctan_sub_le` moves a quotient: `atan a - atan b ≤ (a - b)/(1 + a b)`. `arg_scale`,
`arg_two_truncations` and `sqrt3_eq_zero` are the math of `angle_between3`: the angle survives a
positive scale, two truncations to 63 bits lose at most `7.18` units, and a zero cross product
has zero components. No code here: the math of L4.
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
  have p : 0 < 1 + t * c := by nlinarith only [hc, hct]
  have hD : 1 + t * c ≠ 0 := p.ne'
  have lt : c * ((t - c) / (1 + t * c)) < 1 := by
    rw [mul_div_assoc', div_lt_one p]; nlinarith only [hc]
  have hw : (t - c) / (1 + t * c) * (1 + t * c) = t - c := div_mul_cancel₀ _ hD
  generalize (t - c) / (1 + t * c) = w at lt hw ⊢
  rw [Real.arctan_add lt]
  congr 1
  rw [eq_div_iff (by linarith only [lt])]
  linear_combination -hw

/-- `arctan a - arctan b ≤ (a - b)/(1 + a b)` for `0 ≤ b ≤ a`. -/
theorem arctan_sub_le (a b : ℝ) (hb : 0 ≤ b) (hab : b ≤ a) :
    0 ≤ Real.arctan a - Real.arctan b ∧ Real.arctan a - Real.arctan b ≤ (a - b) / (1 + a * b) := by
  have s := arctan_split a b hb hab
  have q : 0 ≤ (a - b) / (1 + a * b) := div_nonneg (by linarith only [hab]) (by nlinarith only [hb, hab])
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
  set! Z : ℝ := (δ : ℝ) * δ / 2 ^ 62 with hZ
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
  set! I16 : ℝ := (δ : ℝ) * Z / 2 ^ 62 with hI
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
    have d : (99 / 100 : ℝ) ≤ 1 - x ^ 2 := by nlinarith only [x2]
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
      push_cast at this ⊢; linarith only [this]
    push_cast
    rw [e'] at r0 ⊢
    generalize ((256 * n / d : ℕ) : ℝ) = k at r0 k0 ⊢
    have cle : k / 256 ≤ (n : ℝ) / d := by
      rw [div_le_div_iff₀ (by norm_num) dp]; linarith only [r0]
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
    rw [sub_mul, div_mul_cancel₀ _ U0.ne']; linarith only [u]
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
  have sU : s ≤ U := by nlinarith only [hX, hŝ, hs, hU, h]
  have XU : X ≤ U := by nlinarith only [hX, hU, h]
  have e : (s / X - ŝ / X) / (1 + s / X * (ŝ / X)) = (s - ŝ) * X / (X ^ 2 + s * ŝ) := by
    field_simp
  have sp : 0 ≤ s * ŝ := mul_nonneg (hŝ.trans hs) hŝ
  rw [e, div_le_div_iff₀ (by nlinarith only [hX, sp]) (by linarith only [hU])]
  have XU1 : 0 ≤ X * (U - 1) := mul_nonneg hX.le (by linarith only [hU])
  have h1 : (s - ŝ) * (X * (U - 1)) ≤ X * (U - 1) :=
    (mul_le_mul_of_nonneg_right (by linarith only [hs1]) XU1).trans_eq (one_mul _)
  have h2 : s ^ 2 - s ≤ s * ŝ := by nlinarith only [hŝ.trans hs, hs1]
  have h3 : X * (U - 1) ≤ U * (U - 1) := mul_le_mul_of_nonneg_right XU (by linarith only [hU])
  nlinarith only [h, sU, h1, h2, h3]

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
    rw [hs, Real.sq_sqrt (by nlinarith only [cast])]; ring
  have asin_e : Real.arcsin (X / 2 ^ 62) = Complex.arg ⟨s, (X : ℝ)⟩ := (arg_circle s X _ s0 U0 ss).symm
  have acos_e : Real.arccos (X / 2 ^ 62) = Complex.arg ⟨(X : ℝ), s⟩ := by
    rw [Real.arccos_eq_arcsin (by positivity), arg_circle (X : ℝ) s _ X0 U0 (by linarith only [ss])]
    congr 1
    rw [hs, Real.sqrt_eq_iff_mul_self_eq (by nlinarith only [div_le_one_of_le₀ XU U0.le, div_nonneg X0 U0.le, cast])
      (by positivity), div_mul_div_comm, Real.mul_self_sqrt (by nlinarith only [cast])]
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
    have sU : s = 2 ^ 62 := by nlinarith only [l, ŝ0, ss]
    have ŝp : 0 < ŝ := by rw [sU] at u; linarith only [u]
    refine ⟨?_, ?_⟩
    · rw [arg_of_pos _ _ ŝp, arg_of_pos _ _ (by rw [sU]; positivity)]
      simpa using pos
    · rw [arg_compl _ _ le_rfl ŝp, arg_compl _ _ le_rfl (by rw [sU]; positivity)]
      simpa using pos

/-- Jordan's inequality both ways: `|δ| ≤ π/2 · |sin δ|` for `|δ| ≤ π/2`. -/
theorem abs_le_sin_mul (δ : ℝ) (h : |δ| ≤ Real.pi / 2) : |δ| ≤ Real.pi / 2 * |Real.sin δ| := by
  have pi0 := Real.pi_pos
  have key : ∀ x : ℝ, 0 ≤ x → x ≤ Real.pi / 2 → x ≤ Real.pi / 2 * Real.sin x := fun x h0 h1 => by
    have := Real.mul_le_sin h0 h1
    have e : Real.pi / 2 * (2 / Real.pi * x) = x := by field_simp
    calc x = Real.pi / 2 * (2 / Real.pi * x) := e.symm
      _ ≤ Real.pi / 2 * Real.sin x := mul_le_mul_of_nonneg_left this (by positivity)
  rcases le_total 0 δ with h0 | h0
  · rw [abs_of_nonneg h0] at h ⊢
    exact (key δ h0 h).trans (mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity))
  · rw [abs_of_nonpos h0] at h ⊢
    have := key (-δ) (by linarith only [h0]) h
    rw [Real.sin_neg] at this
    exact this.trans (mul_le_mul_of_nonneg_left (neg_le_abs _) (by positivity))

/-- Truncating both coordinates of a point of the first quadrant by at most `e` moves its
angle by at most `1.01 · e / M`, `M ≤ max(n, d)` the larger truncated coordinate and
`e ≤ M / 100`: `sin δ = (n D - d N) / (|z| |w|)` with `|n D - d N| ≤ e · max(n, d) ≤ e |z|`,
Jordan's inequality makes `δ` small, and `δ - δ³/6 < sin δ` brings it to `sin δ`. -/
theorem arg_truncate (n d N D M e : ℝ) (hn : 0 ≤ n) (hd : 0 ≤ d) (hN : n ≤ N) (hN1 : N ≤ n + e)
    (hD : d ≤ D) (hD1 : D ≤ d + e) (hM : 0 < M) (hMn : M ≤ max n d) (he : e ≤ M / 100) :
    |Complex.arg ⟨d, n⟩ - Complex.arg ⟨D, N⟩| ≤ 101 / 100 * (e / M) := by
  set z : ℂ := ⟨d, n⟩
  set w : ℂ := ⟨D, N⟩
  have hn' : n ≤ ‖z‖ := by have := Complex.abs_im_le_norm z; rwa [show z.im = n from rfl, abs_of_nonneg hn] at this
  have hd' : d ≤ ‖z‖ := by have := Complex.abs_re_le_norm z; rwa [show z.re = d from rfl, abs_of_nonneg hd] at this
  have zM : M ≤ ‖z‖ := hMn.trans (max_le hn' hd')
  have wM : M ≤ ‖w‖ := hMn.trans (max_le
    (by have := Complex.abs_im_le_norm w; rw [show w.im = N from rfl, abs_of_nonneg (hn.trans hN)] at this; linarith only [hN, this])
    (by have := Complex.abs_re_le_norm w; rw [show w.re = D from rfl, abs_of_nonneg (hd.trans hD)] at this; linarith only [hD, this]))
  have z0 : z ≠ 0 := fun e => by rw [e, norm_zero] at zM; linarith only [hM, zM]
  have w0 : w ≠ 0 := fun e => by rw [e, norm_zero] at wM; linarith only [hM, wM]
  have zp : 0 < ‖z‖ := hM.trans_le zM
  have wp : 0 < ‖w‖ := hM.trans_le wM
  have a0 : 0 ≤ Complex.arg z := Complex.arg_nonneg_iff.mpr hn
  have a1 : Complex.arg z ≤ Real.pi / 2 := Complex.arg_le_pi_div_two_iff.mpr (Or.inl hd)
  have b0 : 0 ≤ Complex.arg w := Complex.arg_nonneg_iff.mpr (hn.trans hN)
  have b1 : Complex.arg w ≤ Real.pi / 2 := Complex.arg_le_pi_div_two_iff.mpr (Or.inl (hd.trans hD))
  set δ := Complex.arg z - Complex.arg w
  have hδ : |δ| ≤ Real.pi / 2 := abs_le.mpr ⟨by linarith only [a0, b1], by linarith only [a1, b0]⟩
  have j := abs_le_sin_mul δ hδ
  have sd : Real.sin δ = (n * D - d * N) / (‖z‖ * ‖w‖) := by
    rw [Real.sin_sub, Complex.sin_arg, Complex.sin_arg, Complex.cos_arg z0, Complex.cos_arg w0]
    show n / ‖z‖ * (D / ‖w‖) - d / ‖z‖ * (N / ‖w‖) = _
    field_simp
  have e0 : 0 ≤ e := (sub_nonneg.mpr hN).trans (by linarith only [hN1])
  have num : |n * D - d * N| ≤ e * ‖z‖ := by
    have q : n * D - d * N = n * (D - d) - d * (N - n) := by ring
    have h1 : 0 ≤ n * (D - d) := mul_nonneg hn (by linarith only [hD])
    have h2 : n * (D - d) ≤ n * e := mul_le_mul_of_nonneg_left (by linarith only [hD1]) hn
    have h3 : 0 ≤ d * (N - n) := mul_nonneg hd (by linarith only [hN])
    have h4 : d * (N - n) ≤ d * e := mul_le_mul_of_nonneg_left (by linarith only [hN1]) hd
    have h5 : n * e ≤ ‖z‖ * e := mul_le_mul_of_nonneg_right hn' e0
    have h6 : d * e ≤ ‖z‖ * e := mul_le_mul_of_nonneg_right hd' e0
    rw [q]; exact abs_le.mpr ⟨by nlinarith only [h1, h4, h6], by nlinarith only [h2, h3, h5]⟩
  have s1 : |Real.sin δ| ≤ e / M := by
    rw [sd, abs_div, abs_of_pos (mul_pos zp wp), div_le_div_iff₀ (mul_pos zp wp) hM]
    nlinarith only [mul_le_mul_of_nonneg_left wM (mul_nonneg e0 zp.le), hM, num]
  have eM : e / M ≤ 1 / 100 := by rw [div_le_iff₀ hM]; linarith only [he]
  have small : |δ| ≤ 16 / 1000 := by
    calc |δ| ≤ Real.pi / 2 * |Real.sin δ| := j
      _ ≤ 16 / 10 * (1 / 100) := mul_le_mul (by linarith only [Real.pi_lt_d2]) (s1.trans eM) (abs_nonneg _) (by norm_num)
      _ = 16 / 1000 := by norm_num
  have sx : Real.sin |δ| ≤ |Real.sin δ| := by
    rcases le_total 0 δ with h | h
    · rw [abs_of_nonneg h]; exact le_abs_self _
    · rw [abs_of_nonpos h, Real.sin_neg]; exact neg_le_abs _
  rcases (abs_nonneg δ).lt_or_eq with hp | h0
  · have c := Real.sin_gt_sub_cube hp
    have cube : |δ| ^ 3 / 6 ≤ |δ| / 1000 := by
      have : |δ| ^ 2 ≤ (16 / 1000) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) small 2
      nlinarith [abs_nonneg δ]
    nlinarith only [s1, sx, hp, c, cube]
  · rw [← h0]; positivity

/-- The integer root of the sum of squares of three truncated coordinates, `c_i ≤ X_i < c_i + 1`,
is within `2.74` below the length `√(X₀² + X₁² + X₂²)`: the root of the integers is below
the length by at most `√3`, since `ℓ² - s² = Σ (X_i - c_i)(X_i + c_i) ≤ √3 (ℓ + s)`, and
the floor adds `1`. -/
theorem root_length_near (X0 X1 X2 : ℝ) (c0 c1 c2 : ℕ) (h0 : (c0 : ℝ) ≤ X0) (h0' : X0 < c0 + 1)
    (h1 : (c1 : ℝ) ≤ X1) (h1' : X1 < c1 + 1) (h2 : (c2 : ℝ) ≤ X2) (h2' : X2 < c2 + 1) :
    (Nat.sqrt (c0 * c0 + c1 * c1 + c2 * c2) : ℝ) ≤ √(X0 ^ 2 + X1 ^ 2 + X2 ^ 2) ∧
      √(X0 ^ 2 + X1 ^ 2 + X2 ^ 2) ≤ Nat.sqrt (c0 * c0 + c1 * c1 + c2 * c2) + 274 / 100 := by
  set S := c0 * c0 + c1 * c1 + c2 * c2
  have l := Real.nat_sqrt_le_real_sqrt (a := S)
  have u := Real.real_sqrt_lt_nat_sqrt_succ (a := S)
  have SR : ((S : ℕ) : ℝ) = (c0 : ℝ) ^ 2 + (c1 : ℝ) ^ 2 + (c2 : ℝ) ^ 2 := by simp only [S]; push_cast; ring
  rw [SR] at l u
  set s := √((c0 : ℝ) ^ 2 + (c1 : ℝ) ^ 2 + (c2 : ℝ) ^ 2)
  set ℓ := √(X0 ^ 2 + X1 ^ 2 + X2 ^ 2)
  have c0p := Nat.cast_nonneg (α := ℝ) c0
  have c1p := Nat.cast_nonneg (α := ℝ) c1
  have c2p := Nat.cast_nonneg (α := ℝ) c2
  have s0 : 0 ≤ s := Real.sqrt_nonneg _
  have l0 : 0 ≤ ℓ := Real.sqrt_nonneg _
  have ss : s ^ 2 = (c0 : ℝ) ^ 2 + (c1 : ℝ) ^ 2 + (c2 : ℝ) ^ 2 := Real.sq_sqrt (by positivity)
  have ll : ℓ ^ 2 = X0 ^ 2 + X1 ^ 2 + X2 ^ 2 := Real.sq_sqrt (by positivity)
  have sl : s ≤ ℓ := Real.sqrt_le_sqrt (by nlinarith only [h0, h1, h2])
  have k : (3 : ℝ) ≤ (17321 / 10000) ^ 2 := by norm_num
  have sX : X0 + X1 + X2 ≤ 17321 / 10000 * ℓ :=
    (abs_le_of_sq_le_sq' (by nlinarith only [sq_nonneg (X0 - X1), sq_nonneg (X1 - X2), sq_nonneg (X0 - X2), ll])
      (by positivity)).2
  have sc : (c0 : ℝ) + c1 + c2 ≤ 17321 / 10000 * s :=
    (abs_le_of_sq_le_sq' (by nlinarith only [sq_nonneg ((c0 : ℝ) - c1), sq_nonneg ((c1 : ℝ) - c2), sq_nonneg ((c0 : ℝ) - c2), ss])
      (by positivity)).2
  have diff : (ℓ - s) * (ℓ + s) ≤ 17321 / 10000 * (ℓ + s) := by
    have : (ℓ - s) * (ℓ + s) = (X0 - c0) * (X0 + c0) + (X1 - c1) * (X1 + c1) + (X2 - c2) * (X2 + c2) := by
      rw [show (ℓ - s) * (ℓ + s) = ℓ ^ 2 - s ^ 2 by ring, ll, ss]; ring
    rw [this]
    nlinarith only [mul_le_mul_of_nonneg_right (show X0 - c0 ≤ 1 by linarith only [h0']) (show 0 ≤ X0 + c0 by linarith only [h0]),
      mul_le_mul_of_nonneg_right (show X1 - c1 ≤ 1 by linarith only [h1']) (show 0 ≤ X1 + c1 by linarith only [h1]),
      mul_le_mul_of_nonneg_right (show X2 - c2 ≤ 1 by linarith only [h2']) (show 0 ≤ X2 + c2 by linarith only [h2]), sX, sc]
  have ls : ℓ - s ≤ 17321 / 10000 := by
    rcases (add_nonneg l0 s0).lt_or_eq with hp | hz
    · exact le_of_mul_le_mul_right diff hp
    · have : ℓ = 0 := by linarith only [l, l0, hz]
      linarith only [l, hz]
  exact ⟨l.trans sl, by linarith only [u, ls]⟩

/-- `arg (κ x + κ y i) = arg (x + y i)` for `κ > 0`. -/
theorem arg_scale (x y κ : ℝ) (hκ : 0 < κ) : Complex.arg ⟨x * κ, y * κ⟩ = Complex.arg ⟨x, y⟩ := by
  have e : (⟨x * κ, y * κ⟩ : ℂ) = (κ : ℂ) * ⟨x, y⟩ := by
    apply Complex.ext <;> simp [mul_comm]
  rw [e, Complex.arg_real_mul _ hκ]

/-- `angle_between3` after its two truncations: `a` within `3.4` of the angle of `(d1, n1)`,
which are within `1` of `(d, n) · κ2`, which are within `2.74` of `(dot, len) · κ`, with both
maxima at least `2^62`, is within `7.18` of `arg (dot + len i) · 2^62`. -/
theorem arg_two_truncations (a n1 d1 n d : ℕ) (dot len κ κ2 : ℝ) (dot0 : 0 ≤ dot) (len0 : 0 ≤ len)
    (hκ : 0 < κ) (hκ2 : 0 < κ2) (n1l : (n1 : ℝ) ≤ n * κ2) (n1u : (n : ℝ) * κ2 < n1 + 1)
    (d1l : (d1 : ℝ) ≤ d * κ2) (d1u : (d : ℝ) * κ2 < d1 + 1) (M2 : (2 : ℝ) ^ 62 ≤ max (n1 : ℝ) (d1 : ℝ))
    (nl : (n : ℝ) ≤ len * κ) (nu : len * κ ≤ n + 274 / 100) (dl : (d : ℝ) ≤ dot * κ)
    (du : dot * κ ≤ d + 274 / 100) (M1 : (2 : ℝ) ^ 62 ≤ max (n : ℝ) (d : ℝ))
    (ha : |(a : ℝ) - Complex.arg ⟨(d1 : ℝ), (n1 : ℝ)⟩ * 2 ^ 62| ≤ 34 / 10) :
    |(a : ℝ) - Complex.arg ⟨dot, len⟩ * 2 ^ 62| ≤ 718 / 100 := by
  have E1 := arg_truncate n1 d1 (n * κ2) (d * κ2) (2 ^ 62) 1 (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) n1l n1u.le d1l d1u.le (by positivity) M2 (by norm_num)
  rw [arg_scale _ _ _ hκ2] at E1
  have E2 := arg_truncate n d (len * κ) (dot * κ) (2 ^ 62) (274 / 100) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) nl nu dl du (by positivity) M1 (by norm_num)
  rw [arg_scale _ _ _ hκ] at E2
  have U0 : (0 : ℝ) < 2 ^ 62 := by positivity
  have t1 : |(Complex.arg ⟨(d1 : ℝ), (n1 : ℝ)⟩ - Complex.arg ⟨(d : ℝ), (n : ℝ)⟩) * 2 ^ 62| ≤ 101 / 100 := by
    rw [abs_mul, abs_of_pos U0]
    calc _ ≤ 101 / 100 * (1 / 2 ^ 62) * 2 ^ 62 := mul_le_mul_of_nonneg_right E1 U0.le
      _ = 101 / 100 := by field_simp
  have t2 : |(Complex.arg ⟨(d : ℝ), (n : ℝ)⟩ - Complex.arg ⟨dot, len⟩) * 2 ^ 62| ≤ 27674 / 10000 := by
    rw [abs_mul, abs_of_pos U0]
    calc _ ≤ 101 / 100 * (274 / 100 / 2 ^ 62) * 2 ^ 62 := mul_le_mul_of_nonneg_right E2 U0.le
      _ = 27674 / 10000 := by field_simp; norm_num
  have k1 : |(a : ℝ) - Complex.arg ⟨(d : ℝ), (n : ℝ)⟩ * 2 ^ 62| ≤ 34 / 10 + 101 / 100 :=
    ((abs_sub_le _ (Complex.arg ⟨(d1 : ℝ), (n1 : ℝ)⟩ * 2 ^ 62) _).trans_eq (by rw [sub_mul])).trans
      (add_le_add ha t1)
  calc _ ≤ |(a : ℝ) - Complex.arg ⟨(d : ℝ), (n : ℝ)⟩ * 2 ^ 62| +
        |(Complex.arg ⟨(d : ℝ), (n : ℝ)⟩ - Complex.arg ⟨dot, len⟩) * 2 ^ 62| :=
        (abs_sub_le _ _ _).trans_eq (by rw [sub_mul])
    _ ≤ (34 / 10 + 101 / 100) + 27674 / 10000 := add_le_add k1 t2
    _ ≤ 718 / 100 := by norm_num

/-- `√(C0² + C1² + C2²) = 0` for integers: all three are `0`. -/
theorem sqrt3_eq_zero (C0 C1 C2 : ℤ) (h : √((C0 : ℝ) ^ 2 + (C1 : ℝ) ^ 2 + (C2 : ℝ) ^ 2) = 0) :
    C0 = 0 ∧ C1 = 0 ∧ C2 = 0 := by
  have z := (Real.sqrt_eq_zero (by positivity)).mp h
  have p0 := sq_nonneg (C0 : ℝ)
  have p1 := sq_nonneg (C1 : ℝ)
  have p2 := sq_nonneg (C2 : ℝ)
  have e0 : (C0 : ℝ) ^ 2 = 0 := by linarith only [z, p1, p2, p0]
  have e1 : (C1 : ℝ) ^ 2 = 0 := by linarith only [z, p0, p2, p1]
  have e2 : (C2 : ℝ) ^ 2 = 0 := by linarith only [z, p0, p1, p2]
  exact ⟨by exact_mod_cast pow_eq_zero_iff two_ne_zero |>.mp e0, by exact_mod_cast pow_eq_zero_iff two_ne_zero |>.mp e1,
    by exact_mod_cast pow_eq_zero_iff two_ne_zero |>.mp e2⟩

end Fulcrum

end
