module

public import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring.RingNF

/-!
# The reciprocal-root start of `isqrt` of `k32`

`W = a · Y²` of the table entry `Y` is within `2^94 / 128` of `2^94`
(`w_bounds`). One Newton step for the reciprocal root never overshoots in
square, because `4K³ - W(3K - W)² = (K - W)²(4K - W)` (`newton_rsqrt_identity`);
with the floors of the code, `s = ⌊a · y₁ / 2^31⌋` is within `2^42` above and
`2^52` below `m` in square (`rsqrt_core`). The Karp–Markstein step keeps every
value in its signed type and `s₁² ≤ m + 2^57` (`km_core`). No code here.

Steps that add up several bounds are `linear_combination` with the
coefficients written out; every other step is an explicit term.
-/

@[expose] public section

namespace Fulcrum

/-- `4K³ - W(3K - W)² = (K - W)²(4K - W)`. -/
theorem newton_rsqrt_identity (K W : ℤ) :
    4 * K ^ 3 - W * (3 * K - W) ^ 2 = (K - W) ^ 2 * (4 * K - W) := by ring

/-- The table start against `a`: `W = a·Y²` is within `K/128` of `K = 2^94`,
as `127K < 128W < 129K`. -/
theorem w_bounds (A t Y : ℤ) (ht0 : 64 ≤ t) (ht1 : t < 256) (hA1 : t * 2 ^ 24 ≤ A)
    (hA2 : A < (t + 1) * 2 ^ 24) (hY1 : Y < 2 ^ 33) (hY2 : Y ^ 2 * (2 * t + 1) ≤ 2 ^ 71)
    (hY3 : 2 ^ 71 < (Y + 1) ^ 2 * (2 * t + 1)) :
    128 * (A * Y ^ 2) < 129 * 2 ^ 94 ∧ 127 * 2 ^ 94 < 128 * (A * Y ^ 2) := by
  have t0 : (0 : ℤ) < 2 * t + 1 :=
    Int.lt_add_one_of_le (mul_nonneg zero_le_two (le_trans (by decide) ht0))
  have hApos : 0 < A := lt_of_lt_of_le (mul_pos (lt_of_lt_of_le (by decide) ht0) (pow_pos two_pos 24)) hA1
  have hA0 : 0 ≤ A := hApos.le
  constructor
  · have h1 : A * (Y ^ 2 * (2 * t + 1)) ≤ A * 2 ^ 71 := mul_le_mul_of_nonneg_left hY2 hA0
    have h2 : A * 2 ^ 71 < (t + 1) * 2 ^ 24 * 2 ^ 71 := mul_lt_mul_of_pos_right hA2 (pow_pos two_pos 71)
    refine lt_of_mul_lt_mul_right (?_ : _ * (2 * t + 1) < _ * (2 * t + 1)) t0.le
    linear_combination 128 * h1 + 128 * h2 + 2 ^ 95 * ht0
  · have h1 : t * 2 ^ 24 * 2 ^ 71 < A * ((Y + 1) ^ 2 * (2 * t + 1)) :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_right hA1 (pow_nonneg zero_le_two 71))
        (mul_lt_mul_of_pos_left hY3 hApos)
    have hAa : A < 2 ^ 32 :=
      lt_of_lt_of_le hA2 ((mul_le_mul_of_nonneg_right (ht1 : t + 1 ≤ 256) (pow_nonneg zero_le_two 24)).trans_eq rfl)
    have h2 : A * (2 * Y + 1) < 2 ^ 32 * 2 ^ 34 :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_left (by linear_combination 2 * Int.add_one_le_of_lt hY1) hA0)
        (mul_lt_mul_of_pos_right hAa (pow_pos two_pos 34))
    have h3 := mul_lt_mul_of_pos_right h2 t0
    refine lt_of_mul_lt_mul_right (?_ : _ * (2 * t + 1) < _ * (2 * t + 1)) t0.le
    linear_combination 128 * h1 + 128 * h3 + (2 ^ 95 - 2 ^ 74) * ht0

/-- The subtraction of the reciprocal-root step stays non-negative. -/
theorem rsqrt_r1 (A t Y c : ℤ) (ht0 : 64 ≤ t) (ht1 : t < 256) (hA1 : t * 2 ^ 24 ≤ A)
    (hA2 : A < (t + 1) * 2 ^ 24) (hY1 : Y < 2 ^ 33)
    (hY2 : Y ^ 2 * (2 * t + 1) ≤ 2 ^ 71) (hY3 : 2 ^ 71 < (Y + 1) ^ 2 * (2 * t + 1))
    (hc1 : c * 2 ^ 32 ≤ Y ^ 2) : A * c ≤ 3 * 2 ^ 62 := by
  have Whi := (w_bounds A t Y ht0 ht1 hA1 hA2 hY1 hY2 hY3).1
  have hA0 : 0 ≤ A := (mul_nonneg (le_trans (by decide) ht0) (pow_nonneg zero_le_two 24)).trans hA1
  have h : A * (c * 2 ^ 32) ≤ A * Y ^ 2 := mul_le_mul_of_nonneg_left hc1 hA0
  refine le_of_mul_le_mul_right (?_ : A * c * (2 ^ 32 * 128) ≤ 3 * 2 ^ 62 * (2 ^ 32 * 128)) (by decide)
  linear_combination 128 * h + Whi

set_option exponentiation.threshold 512 in
/-- The reciprocal-root step `y₁ = ⌊Y · ⌊(3·2^62 - a·⌊Y²/2^32⌋) / 2^32⌋ / 2^31⌋` and the
root `s = ⌊a · y₁ / 2^31⌋`: the subtraction stays non-negative, `a · y₁` fits `u64`,
`a · y₁² ≤ 2^94 + 2^72`, and `s² ` is within `2^42` above and `2^52` below `m`. -/
theorem rsqrt_core (m A t Y c d i y1 s : ℤ) (ht0 : 64 ≤ t) (ht1 : t < 256)
    (hm1 : A * 2 ^ 32 ≤ m) (hm2 : m < (A + 1) * 2 ^ 32)
    (hA1 : t * 2 ^ 24 ≤ A) (hA2 : A < (t + 1) * 2 ^ 24)
    (hY0 : 0 ≤ Y) (hY1 : Y < 2 ^ 33) (hY2 : Y ^ 2 * (2 * t + 1) ≤ 2 ^ 71)
    (hY3 : 2 ^ 71 < (Y + 1) ^ 2 * (2 * t + 1))
    (hc1 : c * 2 ^ 32 ≤ Y ^ 2) (hc2 : Y ^ 2 < (c + 1) * 2 ^ 32)
    (hd : d = 3 * 2 ^ 62 - A * c)
    (hi1 : i * 2 ^ 32 ≤ d) (hi2 : d < (i + 1) * 2 ^ 32)
    (hy1 : y1 * 2 ^ 31 ≤ Y * i) (hy2 : Y * i < (y1 + 1) * 2 ^ 31) (hy0 : 0 ≤ y1)
    (hs1 : s * 2 ^ 31 ≤ A * y1) (hs2 : A * y1 < (s + 1) * 2 ^ 31) (hs0 : 0 ≤ s) :
    A * c ≤ 3 * 2 ^ 62 ∧ A * y1 < 2 ^ 64 ∧ A * y1 ^ 2 ≤ 2 ^ 94 + 2 ^ 72 ∧
      s ^ 2 ≤ m + 2 ^ 42 ∧ m ≤ s ^ 2 + 2 ^ 52 := by
  obtain ⟨Whi, Wlo⟩ := w_bounds A t Y ht0 ht1 hA1 hA2 hY1 hY2 hY3
  have t0 : (0 : ℤ) ≤ 2 * t + 1 :=
    add_nonneg (mul_nonneg zero_le_two (le_trans (by decide) ht0)) zero_le_one
  have hApos : 0 < A := lt_of_lt_of_le (mul_pos (lt_of_lt_of_le (by decide) ht0) (pow_pos two_pos 24)) hA1
  have hA0 : 0 ≤ A := hApos.le
  have hAa : A < 2 ^ 32 :=
    lt_of_lt_of_le hA2 ((mul_le_mul_of_nonneg_right (ht1 : t + 1 ≤ 256) (pow_nonneg zero_le_two 24)).trans_eq rfl)
  obtain ⟨W, hW⟩ : ∃ W, W = A * Y ^ 2 := ⟨_, rfl⟩
  rw [← hW] at Whi Wlo
  have Ac : A * c * 2 ^ 32 ≤ W := by rw [hW, mul_assoc]; exact mul_le_mul_of_nonneg_left hc1 hA0
  have Ac2 : W < A * c * 2 ^ 32 + A * 2 ^ 32 :=
    calc W = A * Y ^ 2 := hW
      _ < A * ((c + 1) * 2 ^ 32) := mul_lt_mul_of_pos_left hc2 hApos
      _ = A * c * 2 ^ 32 + A * 2 ^ 32 := by ring
  have G1 := rsqrt_r1 A t Y c ht0 ht1 hA1 hA2 hY1 hY2 hY3 hc1
  have hW0 : 0 ≤ W := hW ▸ mul_nonneg hA0 (sq_nonneg Y)
  have W2 : W < 2 * 2 ^ 94 :=
    lt_of_mul_lt_mul_left (Whi.trans (by decide : (129 : ℤ) * 2 ^ 94 < 128 * (2 * 2 ^ 94))) (by decide)
  have W94 : (2 : ℤ) ^ 94 ≤ 3 * 2 ^ 94 - W := by linear_combination W2
  obtain ⟨P, hP⟩ : ∃ P, P = Y * (3 * 2 ^ 94 - W) := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := hP ▸ mul_nonneg hY0 ((pow_nonneg zero_le_two 94).trans W94)
  have AP2 : A * P ^ 2 = W * (3 * 2 ^ 94 - W) ^ 2 := by rw [hP, hW]; ring
  have err0 : 0 ≤ ((2 : ℤ) ^ 94 - W) ^ 2 * (4 * 2 ^ 94 - W) :=
    mul_nonneg (sq_nonneg _) (by linear_combination W2)
  have AP_up : A * P ^ 2 ≤ 4 * (2 ^ 94) ^ 3 := by
    rw [AP2, ← sub_nonneg, newton_rsqrt_identity]; exact err0
  have sqb : ((2 : ℤ) ^ 94 - W) ^ 2 * 2 ^ 14 ≤ (2 ^ 94) ^ 2 :=
    calc ((2 : ℤ) ^ 94 - W) ^ 2 * 2 ^ 14 = (128 * (2 ^ 94 - W)) ^ 2 := by ring
      _ ≤ (2 ^ 94) ^ 2 := sq_le_sq' (by linear_combination Whi) (by linear_combination Wlo)
  have err1 : ((2 : ℤ) ^ 94 - W) ^ 2 * (4 * 2 ^ 94 - W) ≤ 2 ^ 270 := by
    refine le_of_mul_le_mul_right (?_ : _ * (2 : ℤ) ^ 14 ≤ _ * 2 ^ 14) (pow_pos two_pos 14)
    calc ((2 : ℤ) ^ 94 - W) ^ 2 * (4 * 2 ^ 94 - W) * 2 ^ 14
        = (((2 : ℤ) ^ 94 - W) ^ 2 * 2 ^ 14) * (4 * 2 ^ 94 - W) := by ring
      _ ≤ (2 ^ 94) ^ 2 * (4 * 2 ^ 94) :=
          mul_le_mul sqb (sub_le_self _ hW0) (by linear_combination W2) (sq_nonneg _)
      _ = 2 ^ 270 * 2 ^ 14 := rfl
  have AP_lo : 4 * (2 : ℤ) ^ 282 ≤ A * P ^ 2 + 2 ^ 270 := by
    rw [AP2]; linear_combination newton_rsqrt_identity (2 ^ 94) W + err1
  have yup : y1 * 2 ^ 95 ≤ P + Y * A * 2 ^ 32 :=
    calc y1 * 2 ^ 95 = y1 * 2 ^ 31 * 2 ^ 64 := by ring
      _ ≤ Y * i * 2 ^ 64 := mul_le_mul_of_nonneg_right hy1 (pow_nonneg zero_le_two 64)
      _ = Y * (i * 2 ^ 32) * 2 ^ 32 := by ring
      _ ≤ Y * d * 2 ^ 32 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hi1 hY0) (pow_nonneg zero_le_two 32)
      _ = Y * (3 * 2 ^ 94 - A * c * 2 ^ 32) := by rw [hd]; ring
      _ ≤ Y * (3 * 2 ^ 94 - W + A * 2 ^ 32) := mul_le_mul_of_nonneg_left (by linear_combination Ac2) hY0
      _ = P + Y * A * 2 ^ 32 := by rw [hP]; ring
  have ylo : P - Y * 2 ^ 64 - 2 ^ 95 < y1 * 2 ^ 95 :=
    calc P - Y * 2 ^ 64 - 2 ^ 95 = Y * (3 * 2 ^ 94 - W - 2 ^ 64) - 2 ^ 95 := by rw [hP]; ring
      _ ≤ Y * (i * 2 ^ 64) - 2 ^ 95 := sub_le_sub_right (mul_le_mul_of_nonneg_left
          (by linear_combination Ac + 2 ^ 32 * hi2 - 2 ^ 32 * hd) hY0) _
      _ = Y * i * 2 ^ 64 - 2 ^ 95 := by ring
      _ < (y1 + 1) * 2 ^ 31 * 2 ^ 64 - 2 ^ 95 :=
          sub_lt_sub_right (mul_lt_mul_of_pos_right hy2 (pow_pos two_pos 64)) _
      _ = y1 * 2 ^ 95 := by ring
  have Y31 : 2 ^ 31 ≤ Y := by
    refine le_of_not_gt fun hc => absurd hY3 (not_lt.mpr ?_)
    calc (Y + 1) ^ 2 * (2 * t + 1) ≤ (2 ^ 31) ^ 2 * 511 :=
          mul_le_mul (pow_le_pow_left₀ (add_nonneg hY0 zero_le_one) (hc : Y + 1 ≤ 2 ^ 31) 2)
            (by linear_combination 2 * Int.add_one_le_of_lt ht1) t0 (sq_nonneg _)
      _ ≤ 2 ^ 71 := by decide
  have Pbig : 2 ^ 98 ≤ P :=
    calc (2 : ℤ) ^ 98 ≤ 2 ^ 31 * 2 ^ 94 := by decide
      _ ≤ Y * (3 * 2 ^ 94 - W) := mul_le_mul Y31 W94 (pow_nonneg zero_le_two 94) hY0
      _ = P := hP.symm
  have Psmall : P < 2 ^ 129 :=
    calc P = Y * (3 * 2 ^ 94 - W) := hP
      _ ≤ Y * (3 * 2 ^ 94) := mul_le_mul_of_nonneg_left (sub_le_self _ hW0) hY0
      _ < 2 ^ 33 * (3 * 2 ^ 94) := mul_lt_mul_of_pos_right hY1 (by decide)
      _ ≤ 2 ^ 129 := by decide
  have AP : A * P ≤ 2 ^ 32 * 2 ^ 129 := mul_le_mul hAa.le Psmall.le hP0 (pow_nonneg zero_le_two 32)
  obtain ⟨E, hE⟩ : ∃ E, E = Y * A * 2 ^ 32 := ⟨_, rfl⟩
  have E0 : 0 ≤ E := hE ▸ mul_nonneg (mul_nonneg hY0 hA0) (pow_nonneg zero_le_two 32)
  have Esmall : E < 2 ^ 97 :=
    calc E = Y * A * 2 ^ 32 := hE
      _ ≤ Y * 2 ^ 32 * 2 ^ 32 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAa.le hY0) (pow_nonneg zero_le_two 32)
      _ < 2 ^ 33 * 2 ^ 32 * 2 ^ 32 :=
          mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hY1 (pow_pos two_pos 32)) (pow_pos two_pos 32)
      _ = 2 ^ 97 := rfl
  have G3 : A * y1 ^ 2 ≤ 2 ^ 94 + 2 ^ 72 := by
    have h1 : (y1 * 2 ^ 95) ^ 2 ≤ (P + E) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hy0 (pow_nonneg zero_le_two 95)) (hE ▸ yup) 2
    have b1 : A * P * E ≤ 2 ^ 32 * 2 ^ 129 * 2 ^ 97 :=
      mul_le_mul AP Esmall.le E0 (mul_nonneg (pow_nonneg zero_le_two 32) (pow_nonneg zero_le_two 129))
    have b2 : A * E ^ 2 ≤ 2 ^ 32 * (2 ^ 97) ^ 2 :=
      mul_le_mul hAa.le (pow_le_pow_left₀ E0 Esmall.le 2) (sq_nonneg _) (pow_nonneg zero_le_two 32)
    have h2 : A * (P + E) ^ 2 ≤ 4 * (2 ^ 94) ^ 3 + 2 ^ 260 := by
      linear_combination AP_up + 2 * b1 + b2
    refine le_of_mul_le_mul_right (?_ : _ * (2 : ℤ) ^ 190 ≤ _ * 2 ^ 190) (pow_pos two_pos 190)
    calc A * y1 ^ 2 * 2 ^ 190 = A * (y1 * 2 ^ 95) ^ 2 := by ring
      _ ≤ A * (P + E) ^ 2 := mul_le_mul_of_nonneg_left h1 hA0
      _ ≤ 4 * (2 ^ 94) ^ 3 + 2 ^ 260 := h2
      _ ≤ (2 ^ 94 + 2 ^ 72) * 2 ^ 190 := by decide
  have Ay2 : (A * y1) ^ 2 ≤ A * (2 ^ 94 + 2 ^ 72) :=
    calc (A * y1) ^ 2 = A * (A * y1 ^ 2) := by ring
      _ ≤ A * (2 ^ 94 + 2 ^ 72) := mul_le_mul_of_nonneg_left G3 hA0
  have G2 : A * y1 < 2 ^ 64 := by
    refine lt_of_pow_lt_pow_left₀ 2 (pow_nonneg zero_le_two 64) (Ay2.trans_lt ?_)
    calc A * (2 ^ 94 + 2 ^ 72) ≤ 2 ^ 32 * (2 ^ 94 + 2 ^ 72) :=
          mul_le_mul_of_nonneg_right hAa.le (by decide)
      _ < (2 ^ 64) ^ 2 := by decide
  have G4 : s ^ 2 ≤ m + 2 ^ 42 := by
    have h4 : s ^ 2 ≤ A * 2 ^ 32 + A * 2 ^ 10 := by
      refine le_of_mul_le_mul_right (?_ : _ * (2 : ℤ) ^ 62 ≤ _ * 2 ^ 62) (pow_pos two_pos 62)
      calc s ^ 2 * 2 ^ 62 = (s * 2 ^ 31) ^ 2 := by ring
        _ ≤ (A * y1) ^ 2 := pow_le_pow_left₀ (mul_nonneg hs0 (pow_nonneg zero_le_two 31)) hs1 2
        _ ≤ A * (2 ^ 94 + 2 ^ 72) := Ay2
        _ = (A * 2 ^ 32 + A * 2 ^ 10) * 2 ^ 62 := by ring
    linear_combination h4 + hm1 + 2 ^ 10 * hAa
  have G5 : m ≤ s ^ 2 + 2 ^ 52 := by
    have h1 : A * (P - 2 ^ 98) ≤ A * y1 * 2 ^ 95 :=
      (mul_le_mul_of_nonneg_left (by linear_combination ylo + 2 ^ 64 * hY1) hA0).trans_eq
        (mul_assoc _ _ _).symm
    have h2 : A * y1 * 2 ^ 95 < (s + 1) * 2 ^ 126 :=
      calc A * y1 * 2 ^ 95 < (s + 1) * 2 ^ 31 * 2 ^ 95 := mul_lt_mul_of_pos_right hs2 (pow_pos two_pos 95)
        _ = (s + 1) * 2 ^ 126 := by ring
    have h3 : (A * (P - 2 ^ 98)) ^ 2 ≤ ((s + 1) * 2 ^ 126) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hA0 (sub_nonneg.mpr Pbig)) (h1.trans h2.le) 2
    have A196 : 0 ≤ A * 2 ^ 196 := mul_nonneg hA0 (pow_nonneg zero_le_two 196)
    have h6 : A * 2 ^ 32 - A * 2 ^ 19 ≤ (s + 1) ^ 2 := by
      refine le_of_mul_le_mul_right (?_ : _ * (2 : ℤ) ^ 252 ≤ _ * 2 ^ 252) (pow_pos two_pos 252)
      calc (A * 2 ^ 32 - A * 2 ^ 19) * 2 ^ 252 = A * (2 ^ 284 - 2 ^ 271) := by ring
        _ ≤ A * (A * P ^ 2 - 2 ^ 260) := mul_le_mul_of_nonneg_left (by linear_combination AP_lo) hA0
        _ ≤ A * (A * P ^ 2 - 2 * (A * P) * 2 ^ 98 + A * 2 ^ 196) :=
            mul_le_mul_of_nonneg_left (by linear_combination 2 ^ 99 * AP + A196) hA0
        _ = (A * (P - 2 ^ 98)) ^ 2 := by ring
        _ ≤ ((s + 1) * 2 ^ 126) ^ 2 := h3
        _ = (s + 1) ^ 2 * 2 ^ 252 := by ring
    have s33 : s < 2 ^ 33 := by
      refine lt_of_pow_lt_pow_left₀ 2 (pow_nonneg zero_le_two 33) ?_
      calc s ^ 2 ≤ m + 2 ^ 42 := G4
        _ < (A + 1) * 2 ^ 32 + 2 ^ 42 := add_lt_add_left hm2 _
        _ ≤ 2 ^ 32 * 2 ^ 32 + 2 ^ 42 :=
            add_le_add_left (mul_le_mul_of_nonneg_right (hAa : A + 1 ≤ 2 ^ 32) (pow_nonneg zero_le_two 32)) _
        _ < (2 ^ 33) ^ 2 := by decide
    have h7 : A * 2 ^ 19 ≤ 2 ^ 32 * 2 ^ 19 := mul_le_mul_of_nonneg_right hAa.le (pow_nonneg zero_le_two 19)
    linear_combination hm2 + h6 + h7 + 2 * s33
  exact ⟨G1, G2, G3, G4, G5⟩

/-- The Karp–Markstein step `s₁ = s + ⌊y₁ · (m - s²) / 2^64⌋`: every value fits its
signed type, `s₁ ≥ 0` and `s₁² ≤ m + 2^57`. -/
theorem km_core (m s y1 A e corr : ℤ) (hm0 : 2 ^ 62 ≤ m) (hm : m < 2 ^ 64)
    (hA0 : 2 ^ 30 ≤ A) (hAy : A * y1 < 2 ^ 64) (hy0 : 0 ≤ y1)
    (hs0 : 0 ≤ s) (G4 : s ^ 2 ≤ m + 2 ^ 42) (G5 : m ≤ s ^ 2 + 2 ^ 52) (he : e = m - s ^ 2)
    (hc1 : corr * 2 ^ 64 ≤ y1 * e) (hc2 : y1 * e < (corr + 1) * 2 ^ 64) :
    -2 ^ 63 ≤ e ∧ e < 2 ^ 63 ∧ -2 ^ 127 ≤ y1 * e ∧ y1 * e < 2 ^ 127 ∧
      -2 ^ 63 ≤ corr ∧ corr < 2 ^ 63 ∧ 0 ≤ s + corr ∧ s + corr < 2 ^ 63 ∧
      (s + corr) ^ 2 ≤ m + 2 ^ 57 := by
  have y34 : y1 < 2 ^ 34 := lt_of_not_ge fun hc => absurd hAy (not_lt.mpr
    (calc (2 : ℤ) ^ 64 = 2 ^ 30 * 2 ^ 34 := rfl
      _ ≤ A * y1 := mul_le_mul hA0 hc (pow_nonneg zero_le_two 34) ((pow_nonneg zero_le_two 30).trans hA0)))
  have s33 : s < 2 ^ 33 := by
    refine lt_of_pow_lt_pow_left₀ 2 (pow_nonneg zero_le_two 33) (G4.trans_lt ?_)
    calc m + 2 ^ 42 < 2 ^ 64 + 2 ^ 42 := add_lt_add_left hm _
      _ < (2 ^ 33) ^ 2 := by decide
  have s30 : 2 ^ 30 ≤ s := by
    refine le_of_not_gt fun hc => absurd G5 (not_le.mpr ?_)
    calc s ^ 2 + 2 ^ 52 < (2 ^ 30) ^ 2 + 2 ^ 52 := add_lt_add_left (pow_lt_pow_left₀ hc hs0 two_ne_zero) _
      _ < 2 ^ 62 := by decide
      _ ≤ m := hm0
  have e1 : -2 ^ 42 ≤ e := by rw [he]; linear_combination G4
  have e2 : e ≤ 2 ^ 52 := by rw [he]; linear_combination G5
  have p1 : y1 * e ≤ 2 ^ 34 * 2 ^ 52 := by
    rcases le_total 0 e with h | h
    · exact mul_le_mul y34.le e2 h (pow_nonneg zero_le_two 34)
    · exact (mul_nonpos_of_nonneg_of_nonpos hy0 h).trans (by decide)
  have p2 : -(2 ^ 34 * 2 ^ 42) ≤ y1 * e := by
    rcases le_total 0 e with h | h
    · exact (by decide : -((2 : ℤ) ^ 34 * 2 ^ 42) ≤ 0).trans (mul_nonneg hy0 h)
    · have : y1 * -e ≤ 2 ^ 34 * 2 ^ 42 :=
        mul_le_mul y34.le (neg_le.mp e1) (neg_nonneg.mpr h) (pow_nonneg zero_le_two 34)
      rw [mul_neg] at this
      exact neg_le.mp this
  have c1 : corr ≤ 2 ^ 22 :=
    le_of_mul_le_mul_right (hc1.trans (p1.trans_eq rfl)) (pow_pos two_pos 64)
  have c2 : -2 ^ 12 ≤ corr := Int.lt_add_one_iff.mp (lt_of_mul_lt_mul_right
    (lt_of_le_of_lt ((by decide : (-2 ^ 12 : ℤ) * 2 ^ 64 ≤ -(2 ^ 34 * 2 ^ 42)).trans p2) hc2)
    (pow_nonneg zero_le_two 64))
  have s1 : 0 ≤ s + corr := by linear_combination s30 + c2
  have sq : (s + corr) ^ 2 ≤ (s + 2 ^ 22) ^ 2 := pow_le_pow_left₀ s1 (add_le_add_right c1 s) 2
  exact ⟨(by decide : (-2 ^ 63 : ℤ) ≤ -2 ^ 42).trans e1, e2.trans_lt (by decide),
    (by decide : (-2 ^ 127 : ℤ) ≤ -(2 ^ 34 * 2 ^ 42)).trans p2, p1.trans_lt (by decide),
    (by decide : (-2 ^ 63 : ℤ) ≤ -2 ^ 12).trans c2, c1.trans_lt (by decide), s1,
    (add_lt_add_of_lt_of_le s33 c1).trans (by decide),
    by linear_combination sq + G4 + 2 ^ 23 * s33⟩

end Fulcrum

end
