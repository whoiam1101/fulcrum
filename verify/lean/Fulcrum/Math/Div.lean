module

public import Fulcrum.Spec

/-!
# Rounding a quotient

On magnitudes, `⌊(2·n + d) / 2·d⌋` rounds `n / d` and `-⌊(2·n + d - 1) / 2·d⌋`
rounds `-n / d` to nearest with ties toward `+∞` (`roundHalfUp_div`,
`roundHalfUp_neg_div`); the sign of the quotient is the parity of the signs of
the operands (`signed_div_eq`, `decide_mul_neg`). The signed form divides
`2·n + bias` by `2·d` truncating, with the same result (`tdiv_round`). No code
here: the math of `mul_div`, `div` and `div_int`.
-/

@[expose] public section

namespace Fulcrum

/-- `⌊(2·n + d) / 2·d⌋` rounds `n / d` for `d > 0`. -/
theorem roundHalfUp_div (n d : ℤ) (hd : 0 < d) :
    roundHalfUp ((n : ℚ) / d) = (2 * n + d) / (2 * d) := by
  have hq : (d : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hd.ne'
  have h2 : (0 : ℤ) ≤ 2 * d := mul_nonneg zero_le_two hd.le
  have e : (n : ℚ) / d + 1 / 2 = ((2 * n + d : ℤ) : ℚ) / (((2 * d).toNat : ℕ) : ℚ) := by
    rw [← Int.cast_natCast (R := ℚ), Int.toNat_of_nonneg h2, Int.cast_add, Int.cast_mul,
      Int.cast_mul, Int.cast_ofNat, div_add_div _ _ hq two_ne_zero, mul_one, mul_comm (n : ℚ) 2,
      mul_comm (d : ℚ) 2]
  rw [roundHalfUp, e, Rat.floor_intCast_div_natCast, Int.toNat_of_nonneg h2]

/-- `⌊(-x + D - 1) / D⌋ = -⌊x / D⌋` for `D > 0`. -/
theorem neg_ediv_shape (x D : ℤ) (hD : 0 < D) : (-x + D - 1) / D = -(x / D) := by
  have h := Int.emod_add_mul_ediv x D
  have r0 := Int.emod_nonneg x hD.ne'
  have r1 := Int.emod_lt_of_pos x hD
  refine ((Int.ediv_emod_unique (r := D - 1 - x % D) hD).2 ⟨?_, sub_nonneg.mpr
    (Int.le_sub_one_of_lt r1), lt_of_le_of_lt (sub_le_self _ r0) (sub_one_lt D)⟩).1
  conv_rhs => rw [← h]
  ring

/-- `-⌊(2·n + d - 1) / 2·d⌋` rounds `-n / d` for `d > 0`. -/
theorem roundHalfUp_neg_div (n d : ℤ) (hd : 0 < d) :
    roundHalfUp ((-n : ℤ) / (d : ℚ)) = -((2 * n + d - 1) / (2 * d)) := by
  rw [roundHalfUp_div _ _ hd, ← neg_ediv_shape _ _ (mul_pos zero_lt_two hd)]
  congr 1
  ring

/-- `±|x| / |y|` with the sign of the parity of the signs is `x / y`. -/
theorem signed_div_eq (x y : ℤ) (hy : y ≠ 0) (s : Bool)
    (hs : x ≠ 0 → s = (decide (x < 0) != decide (y < 0))) :
    (((if s then -(x.natAbs : ℤ) else x.natAbs : ℤ) : ℚ) / (y.natAbs : ℚ)) = (x : ℚ) / y := by
  by_cases hx : x = 0
  · rw [hx, Int.natAbs_zero, Nat.cast_zero, neg_zero, ite_self, Int.cast_zero, zero_div, zero_div]
  rw [hs hx]
  rcases lt_or_gt_of_ne hx with hxn | hxp <;> rcases lt_or_gt_of_ne hy with hyn | hyp
  · rw [decide_eq_true hxn, decide_eq_true hyn,
      ite_eq_right (show (true != true) ≠ true from Bool.false_ne_true),
      Int.natCast_natAbs, abs_of_neg hxn, ← Int.cast_natCast, Int.natCast_natAbs, abs_of_neg hyn,
      Int.cast_neg, Int.cast_neg, neg_div_neg_eq]
  · rw [decide_eq_true hxn, decide_eq_false (not_lt.mpr hyp.le),
      ite_eq_left (show (true != false) = true from rfl),
      Int.natCast_natAbs, abs_of_neg hxn, neg_neg, ← Int.cast_natCast, Int.natCast_natAbs,
      abs_of_pos hyp]
  · rw [decide_eq_false (not_lt.mpr hxp.le), decide_eq_true hyn,
      ite_eq_left (show (false != true) = true from rfl),
      Int.natCast_natAbs, abs_of_pos hxp, ← Int.cast_natCast, Int.natCast_natAbs, abs_of_neg hyn,
      Int.cast_neg, Int.cast_neg, neg_div_neg_eq]
  · rw [decide_eq_false (not_lt.mpr hxp.le), decide_eq_false (not_lt.mpr hyp.le),
      ite_eq_right (show (false != false) ≠ true from Bool.false_ne_true), Int.natCast_natAbs,
      abs_of_pos hxp, ← Int.cast_natCast, Int.natCast_natAbs, abs_of_pos hyp]

/-- A non-zero product is negative exactly when one factor is. -/
theorem decide_mul_neg (a b : ℤ) (h : a * b ≠ 0) :
    decide (a * b < 0) = (decide (a < 0) != decide (b < 0)) := by
  have ha : a ≠ 0 := left_ne_zero_of_mul h
  have hb : b ≠ 0 := right_ne_zero_of_mul h
  rcases lt_or_gt_of_ne ha with an | ap <;> rcases lt_or_gt_of_ne hb with nn | bp
  · rw [decide_eq_false (not_lt.mpr (mul_pos_of_neg_of_neg an nn).le), decide_eq_true an,
      decide_eq_true nn]; rfl
  · rw [decide_eq_true (mul_neg_of_neg_of_pos an bp), decide_eq_true an,
      decide_eq_false (not_lt.mpr bp.le)]; rfl
  · rw [decide_eq_true (mul_neg_of_pos_of_neg ap nn), decide_eq_false (not_lt.mpr ap.le),
      decide_eq_true nn]; rfl
  · rw [decide_eq_false (not_lt.mpr (mul_pos ap bp).le), decide_eq_false (not_lt.mpr ap.le),
      decide_eq_false (not_lt.mpr bp.le)]; rfl

/-- The signed form of `div_kernel!`: `tdiv(2·n + bias, 2·d)` with the bias
`±(|d| - [d < 0])` of the sign of `n` rounds `n / d`. -/
theorem tdiv_round (n d : ℤ) (hd : d ≠ 0) :
    (2 * n + (if n < 0 then 1 - (decide (d < 0)).toInt - d.natAbs
      else d.natAbs - (decide (d < 0)).toInt)).tdiv (2 * d) = roundHalfUp ((n : ℚ) / d) := by
  rcases lt_or_gt_of_ne hd with dn | dp <;> rcases lt_or_ge n 0 with nn | np
  · rw [ite_eq_left nn, decide_eq_true dn, Bool.toInt_true, Int.ofNat_natAbs_of_nonpos dn.le,
      show 2 * n + (1 - 1 - -d) = -(2 * -n + -d) by ring, ← neg_neg (2 * d), ← mul_neg,
      Int.neg_tdiv_neg, Int.tdiv_eq_ediv_of_nonneg (add_nonneg (mul_nonneg zero_le_two
        (neg_nonneg.mpr nn.le)) (neg_nonneg.mpr dn.le)),
      ← roundHalfUp_div _ _ (neg_pos.mpr dn), Int.cast_neg, Int.cast_neg, neg_div_neg_eq]
  · rw [ite_eq_right (not_lt.mpr np), decide_eq_true dn, Bool.toInt_true,
      Int.ofNat_natAbs_of_nonpos dn.le, ← neg_neg (2 * d), ← mul_neg, Int.tdiv_neg,
      Int.tdiv_eq_ediv_of_nonneg (add_nonneg (mul_nonneg zero_le_two np)
        (Int.le_sub_one_of_lt (neg_pos.mpr dn))), ← add_sub_assoc,
      ← roundHalfUp_neg_div _ _ (neg_pos.mpr dn), Int.cast_neg, Int.cast_neg, neg_div_neg_eq]
  · rw [ite_eq_left nn, decide_eq_false (not_lt.mpr dp.le), Bool.toInt_false,
      Int.natAbs_of_nonneg dp.le, show 2 * n + (1 - 0 - d) = -(2 * -n + (d - 1)) by ring,
      Int.neg_tdiv, Int.tdiv_eq_ediv_of_nonneg (add_nonneg (mul_nonneg zero_le_two
        (neg_nonneg.mpr nn.le)) (Int.le_sub_one_of_lt dp)), ← add_sub_assoc,
      ← roundHalfUp_neg_div _ _ dp, neg_neg]
  · rw [ite_eq_right (not_lt.mpr np), decide_eq_false (not_lt.mpr dp.le), Bool.toInt_false,
      Int.natAbs_of_nonneg dp.le, sub_zero,
      Int.tdiv_eq_ediv_of_nonneg (add_nonneg (mul_nonneg zero_le_two np) dp.le),
      ← roundHalfUp_div _ _ dp]

end Fulcrum

end
