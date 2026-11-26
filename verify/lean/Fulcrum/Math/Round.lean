module

public import Fulcrum.Spec
import Fulcrum.Lemmas.Int

/-!
# Rounding by a shift

Shifting right by `k + 1` after adding `2^k` is rounding to nearest with ties
toward `+∞`, for every shift, and so is the floor plus the first dropped bit,
the model `shrRound` of `kernel::shr_round` on unbounded integers. Adding an
integer to the exact value adds it to the rounded value, and bounds of the
exact value bound the rounded one. A sign and a magnitude round by the first
dropped bit and the sticky bits (`roundHalfUp_sign_magnitude`). No code here:
the math of L1, `mul`, `mul_add` and `lerp`.
-/

@[expose] public section

namespace Fulcrum

/-- `kernel::shr_round` on unbounded integers: `⌊n / 2^s⌋` plus the first
dropped bit. -/
def shrRound (n : ℤ) (s : ℕ) : ℤ :=
  if s = 0 then n else (n >>> s) + (n >>> (s - 1)) % 2

/-- Adding `2^k` and shifting right by `k + 1` rounds `n / 2^(k+1)` to nearest,
ties toward `+∞`. -/
theorem add_half_shr (n : ℤ) (k : ℕ) :
    (n + 2 ^ k) >>> (k + 1) = roundHalfUp (exact (k + 1) n) := by
  have h : exact (k + 1) n + 1 / 2 = ((n + 2 ^ k : ℤ) : ℚ) / ((2 ^ (k + 1) : ℕ) : ℚ) := by
    rw [exact, Int.cast_add, Int.cast_pow, Int.cast_ofNat, Nat.cast_pow, Nat.cast_ofNat,
      add_div, pow_succ, div_mul_cancel_left₀ (pow_ne_zero k two_ne_zero), one_div]
  rw [roundHalfUp, h, Rat.floor_intCast_div_natCast, shr_eq_div, Nat.cast_pow, Nat.cast_ofNat]

/-- `kernel::shr_round` rounds `n / 2^s` to nearest, ties toward `+∞`, for
every `n` and every `s`. -/
theorem shrRound_eq (n : ℤ) (s : ℕ) : shrRound n s = roundHalfUp (exact s n) := by
  unfold shrRound
  rcases s with _ | k
  · rw [ite_eq_left rfl, roundHalfUp, exact, pow_zero, div_one, Int.floor_intCast_add,
      Int.floor_eq_zero_iff.2 ⟨one_half_pos.le, one_half_lt_one⟩, add_zero]
  · have hd : (0 : ℤ) < 2 ^ k := pow_pos zero_lt_two k
    rw [ite_eq_right (Nat.add_one_ne_zero k), ← add_half_shr, Nat.add_sub_cancel, shr_eq_div,
      shr_eq_div, shr_eq_div, pow_succ, ← Int.ediv_ediv_of_nonneg hd.le,
      ← Int.ediv_ediv_of_nonneg hd.le, add_ediv_self n hd.ne']
    omega

/-- Adding an integer `c` to the exact value adds it to the rounded value. -/
theorem roundHalfUp_add_int (x c : ℤ) (n : ℕ) :
    roundHalfUp (exact n (x + c * 2 ^ n)) = roundHalfUp (exact n x) + c := by
  have e : exact n (x + c * 2 ^ n) + 1 / 2 = (exact n x + 1 / 2) + c := by
    rw [exact, exact, Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, add_div,
      mul_div_cancel_right₀ _ (pow_ne_zero n two_ne_zero), add_right_comm]
  rw [roundHalfUp, roundHalfUp, e, Int.floor_add_intCast]

/-- Bounds of the rounded value from bounds of the exact one. -/
theorem roundHalfUp_bounds (x L U : ℤ) (k : ℕ) (hl : L * 2 ^ (k + 1) ≤ x + 2 ^ k)
    (hu : x + 2 ^ k < U * 2 ^ (k + 1)) :
    L ≤ roundHalfUp (exact (k + 1) x) ∧ roundHalfUp (exact (k + 1) x) < U := by
  have pos : (0 : ℤ) < 2 ^ (k + 1) := pow_pos zero_lt_two _
  rw [← add_half_shr, shr_eq_div]
  exact ⟨(Int.le_ediv_iff_mul_le pos).2 hl, (Int.ediv_lt_iff_lt_mul pos).2 hu⟩

/-- The rounded value is `c` when the exact value plus `½` is in `[c, c + 1)`. -/
theorem roundHalfUp_eq_of_bounds (x c : ℤ) (k : ℕ) (hl : c * 2 ^ (k + 1) ≤ x + 2 ^ k)
    (hu : x + 2 ^ k < (c + 1) * 2 ^ (k + 1)) : roundHalfUp (exact (k + 1) x) = c :=
  have b := roundHalfUp_bounds x c (c + 1) k hl hu
  le_antisymm (Int.lt_add_one_iff.mp b.2) b.1

/-- Dropped bits `r < 2^(k+1)` of a non-negative value round up exactly when
the first of them is set. -/
theorem roundHalfUp_dropped (r : ℤ) (k : ℕ) (h0 : 0 ≤ r) (h1 : r < 2 ^ (k + 1)) :
    roundHalfUp (exact (k + 1) r) = (decide (2 ^ k ≤ r)).toInt := by
  rw [pow_succ] at h1
  by_cases h : 2 ^ k ≤ r
  · rw [decide_eq_true h, Bool.toInt_true]
    exact roundHalfUp_eq_of_bounds r 1 k (by rw [pow_succ]; omega) (by rw [pow_succ]; omega)
  · rw [decide_eq_false h, Bool.toInt_false]
    exact roundHalfUp_eq_of_bounds r 0 k (by rw [pow_succ]; omega) (by rw [pow_succ]; omega)

/-- Dropped bits `r < 2^(k+1)` of a negative value round its magnitude up
exactly when the first of them and a later one are set: a tie goes toward
`+∞`, so toward zero. -/
theorem roundHalfUp_neg_dropped (r : ℤ) (k : ℕ) (h0 : 0 ≤ r) (h1 : r < 2 ^ (k + 1)) :
    roundHalfUp (exact (k + 1) (-r)) = -(decide (2 ^ k ≤ r) && decide (r % 2 ^ k ≠ 0)).toInt := by
  rw [pow_succ] at h1
  by_cases h : 2 ^ k ≤ r
  · have e : r % 2 ^ k = r - 2 ^ k := by
      rw [← Int.sub_emod_right]; exact Int.emod_eq_of_lt (sub_nonneg.mpr h) (by omega)
    rw [decide_eq_true h, Bool.true_and, e]
    by_cases h' : 2 ^ k < r
    · rw [decide_eq_true (sub_ne_zero.mpr (ne_of_gt h')), Bool.toInt_true]
      exact roundHalfUp_eq_of_bounds _ _ k (by rw [pow_succ]; omega) (by rw [pow_succ]; omega)
    · rw [decide_eq_false (not_not.mpr (sub_eq_zero.mpr (le_antisymm (not_lt.mp h') h))),
        Bool.toInt_false]
      exact roundHalfUp_eq_of_bounds _ _ k (by rw [pow_succ]; omega) (by rw [pow_succ]; omega)
  · rw [decide_eq_false h, Bool.false_and, Bool.toInt_false]
    exact roundHalfUp_eq_of_bounds _ _ k (by rw [pow_succ]; omega) (by rw [pow_succ]; omega)

/-- A value of sign `±` and magnitude `m · 2^(k+1) + r`, `r < 2^(k+1)`, rounds
to `±(m + up)`, where `up` is the first dropped bit, and for a negative value
also a later dropped bit. -/
theorem roundHalfUp_sign_magnitude (negative : Bool) (m r : ℤ) (k : ℕ) (h0 : 0 ≤ r)
    (h1 : r < 2 ^ (k + 1)) :
    roundHalfUp (exact (k + 1) ((if negative then -1 else 1) * (m * 2 ^ (k + 1) + r))) =
      (if negative then -1 else 1) *
        (m + (decide (2 ^ k ≤ r) && (!negative || decide (r % 2 ^ k ≠ 0))).toInt) := by
  cases negative
  · rw [ite_eq_right Bool.false_ne_true, one_mul, one_mul, add_comm (m * _), roundHalfUp_add_int,
      roundHalfUp_dropped r k h0 h1, add_comm, Bool.not_false, Bool.true_or, Bool.and_true]
  · rw [ite_eq_left rfl, neg_one_mul, neg_one_mul, neg_add, neg_add, add_comm (-_), ← neg_mul,
      roundHalfUp_add_int, roundHalfUp_neg_dropped r k h0 h1, add_comm, Bool.not_true,
      Bool.false_or]

end Fulcrum

end
