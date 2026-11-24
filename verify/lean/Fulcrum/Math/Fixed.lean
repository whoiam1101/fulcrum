module

public import Fulcrum.Math.Series
public import Fulcrum.Math.Round
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Errors of fixed-point arithmetic with 62 fractional bits

`trig.rs` and `exp.rs` compute on naturals that stand for reals times `2^62`:
a floor division, a truncated product `⌊a · b / 2^62⌋` and `2^62 - a`. Given
how far each operand is from its ideal real value, these lemmas bound how far
the result is from the ideal result; `two_term_le` is Cauchy–Schwarz for the
sum `x · sin a + y · cos a` of two such errors, and `round_shift_near` the one
rounding by `shr_round` at the end. No code here: the math of L4.
-/

@[expose] public section

namespace Fulcrum

/-- `⌊a · b / 2^62⌋`: `trig::mul` and `exp::mul` on naturals. -/
def mul62 (a b : ℕ) : ℕ := a * b / 2 ^ 62

/-- `⌊x / d⌋` is within `1` of `x / d`, and not above it. -/
theorem floor_div_near (x d : ℕ) (hd : 0 < d) :
    ((x / d : ℕ) : ℝ) ≤ x / d ∧ (x : ℝ) / d - 1 < ((x / d : ℕ) : ℝ) := by
  have dp : (0 : ℝ) < d := by exact_mod_cast hd
  refine ⟨Nat.cast_div_le, ?_⟩
  rw [sub_lt_iff_lt_add, div_lt_iff₀ dp]
  have := Nat.lt_div_mul_add (a := x) hd
  exact_mod_cast (show x < (x / d + 1) * d by rw [add_mul, one_mul]; exact this)

/-- A floor division of a value within `e` of `X` is within `e / d + 1` of `X / d`. -/
theorem div_near (x d : ℕ) (X e : ℝ) (hd : 0 < d) (h : |(x : ℝ) - X| ≤ e) :
    |((x / d : ℕ) : ℝ) - X / d| ≤ e / d + 1 := by
  have dp : (0 : ℝ) < d := by exact_mod_cast hd
  have ⟨l, u⟩ := floor_div_near x d hd
  have hx : |(x : ℝ) / d - X / d| ≤ e / d := by
    rw [← sub_div, abs_div, abs_of_pos dp]; exact div_le_div_of_nonneg_right h dp.le
  calc |((x / d : ℕ) : ℝ) - X / d| ≤ |((x / d : ℕ) : ℝ) - x / d| + |(x : ℝ) / d - X / d| :=
        abs_sub_le _ _ _
    _ ≤ 1 + e / d := by
        refine add_le_add ?_ hx
        exact abs_le.mpr ⟨neg_le_sub_iff_le_add.mpr (sub_lt_iff_lt_add.mp u).le,
          (sub_nonpos.mpr l).trans zero_le_one⟩
    _ = e / d + 1 := add_comm _ _

/-- The truncated product `⌊a · b / 2^62⌋` of values within `ea`, `eb` of `A ≥ 0`,
`B` is within `(ea · Mb + MA · eb) / 2^62 + 1` of `A · B / 2^62`, for `A ≤ MA`
and `b ≤ Mb`. -/
theorem mul_near (a b : ℕ) (A B ea eb MA Mb : ℝ) (ha : |(a : ℝ) - A| ≤ ea)
    (hb : |(b : ℝ) - B| ≤ eb) (hA0 : 0 ≤ A) (hA : A ≤ MA) (hbM : (b : ℝ) ≤ Mb) :
    |((a * b / 2 ^ 62 : ℕ) : ℝ) - A * B / 2 ^ 62| ≤ (ea * Mb + MA * eb) / 2 ^ 62 + 1 := by
  have h := div_near (a * b) (2 ^ 62) (A * B) (ea * Mb + MA * eb) (by positivity) (by
    rw [Nat.cast_mul, show (a : ℝ) * b - A * B = (a - A) * b + A * (b - B) by ring]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, Nat.abs_cast b]
      exact mul_le_mul ha hbM (Nat.cast_nonneg b) ((abs_nonneg _).trans ha)
    · rw [abs_mul, abs_of_nonneg hA0]
      exact mul_le_mul hA hb (abs_nonneg _) (hA0.trans hA))
  rw [Nat.cast_pow, Nat.cast_ofNat] at h
  exact h

/-- `2^62 - a` of a value `a ≤ 2^62` within `e` of `A` is within `e` of `2^62 - A`. -/
theorem sub_near (a : ℕ) (A e : ℝ) (h : |(a : ℝ) - A| ≤ e) (ha : a ≤ 2 ^ 62) :
    |((2 ^ 62 - a : ℕ) : ℝ) - (2 ^ 62 - A)| ≤ e := by
  rw [Nat.cast_sub ha, show ((2 ^ 62 : ℕ) : ℝ) - a - (2 ^ 62 - A) = -(a - A) by push_cast; ring,
    abs_neg]
  exact h

/-- `x · S + y · C ≤ K · W` for `S² + C² = W²`, `x² + y² ≤ K²` and non-negative
`x`, `y`, `K`, `W`: Cauchy–Schwarz on two terms. -/
theorem two_term_le (S C x y K W : ℝ) (hW : S ^ 2 + C ^ 2 = W ^ 2) (hK : x ^ 2 + y ^ 2 ≤ K ^ 2)
    (hK0 : 0 ≤ K) (hW0 : 0 ≤ W) : x * S + y * C ≤ K * W := by
  have sq : (x * S + y * C) ^ 2 ≤ (K * W) ^ 2 := by
    have e : (x ^ 2 + y ^ 2) * (S ^ 2 + C ^ 2) - (x * S + y * C) ^ 2 = (x * C - y * S) ^ 2 := by ring
    calc (x * S + y * C) ^ 2 ≤ (x ^ 2 + y ^ 2) * (S ^ 2 + C ^ 2) :=
          sub_nonneg.mp (e ▸ sq_nonneg _)
      _ ≤ K ^ 2 * W ^ 2 := by
          rw [hW]; exact mul_le_mul_of_nonneg_right hK (sq_nonneg W)
      _ = (K * W) ^ 2 := (mul_pow K W 2).symm
  exact abs_le_of_sq_le_sq' sq (mul_nonneg hK0 hW0) |>.2

/-- Rounding to nearest moves a rational by at most `½`. -/
theorem roundHalfUp_near (q : ℚ) : |((roundHalfUp q : ℤ) : ℚ) - q| ≤ 1 / 2 := by
  unfold roundHalfUp
  have l := Int.floor_le (q + 1 / 2)
  have u := Int.lt_floor_add_one (q + 1 / 2)
  rw [show ((⌊q + 1 / 2⌋ : ℤ) : ℚ) + 1 = ((⌊q + 1 / 2⌋ : ℤ) : ℚ) + 1 / 2 + 1 / 2 by ring] at u
  exact abs_le.mpr ⟨neg_le_sub_iff_le_add.mpr (lt_of_add_lt_add_right u).le, sub_le_iff_le_add'.mpr l⟩

/-- `m · 2^-s` rounded once, for `m` within `E` of `S · 2^62` and `s + f = 62`, is
within `½ + E / 2^s` of `S · 2^f`. -/
theorem round_shift_near (m : ℤ) (s f : ℕ) (hs : s + f = 62) (S E : ℝ)
    (h : |(m : ℝ) - S * 2 ^ 62| ≤ E) :
    |((roundHalfUp (exact s m) : ℤ) : ℝ) - S * 2 ^ f| ≤ 1 / 2 + E / 2 ^ s := by
  have r := roundHalfUp_near (exact s m)
  have r' : |((roundHalfUp (exact s m) : ℤ) : ℝ) - (m : ℝ) / 2 ^ s| ≤ 1 / 2 := by
    have := (Rat.cast_le (K := ℝ)).mpr r
    push_cast [exact] at this
    exact this
  have p : (0 : ℝ) < 2 ^ s := by positivity
  have e : (m : ℝ) / 2 ^ s - S * 2 ^ f = ((m : ℝ) - S * 2 ^ 62) / 2 ^ s := by
    rw [← hs, pow_add]; field_simp
  calc _ ≤ |((roundHalfUp (exact s m) : ℤ) : ℝ) - (m : ℝ) / 2 ^ s| + |(m : ℝ) / 2 ^ s - S * 2 ^ f| :=
        abs_sub_le _ _ _
    _ ≤ 1 / 2 + E / 2 ^ s := by
        refine add_le_add r' ?_
        rw [e, abs_div, abs_of_pos p]
        exact div_le_div_of_nonneg_right h p.le

end Fulcrum

end
