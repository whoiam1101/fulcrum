module

public import Mathlib.Algebra.Order.Floor.Ring

/-!
# Integer facts used by several modules

A right shift is the floor of the quotient by a power of two, adding the
divisor adds one to the quotient, balanced residues depend only on the residue,
a magnitude below `2^j` bounds both sides, and a boolean as an integer is `0` or
`1`.
-/

@[expose] public section

namespace Fulcrum

/-- A right shift of an integer is the floor of its quotient by `2^s`. -/
theorem shr_eq_div (n : ℤ) (s : ℕ) : n >>> s = n / 2 ^ s := by
  rw [Int.shiftRight_eq_div_pow, Nat.cast_pow, Nat.cast_ofNat]

/-- `(n + b) / b = n / b + 1` for `b ≠ 0`. -/
theorem add_ediv_self (n : ℤ) {b : ℤ} (hb : b ≠ 0) : (n + b) / b = n / b + 1 := by
  rw [← Int.add_mul_ediv_right n 1 hb, one_mul]

/-- Balanced residues agree for congruent integers. -/
theorem bmod_congr (x y : ℤ) (M : ℕ) (h : x % M = y % M) : x.bmod M = y.bmod M := by
  rw [Int.bmod_def, Int.bmod_def, h]

/-- `|x| < 2^j` bounds `x` on both sides. -/
theorem lt_of_natAbs_lt {x : ℤ} {j : ℕ} (h : x.natAbs < 2 ^ j) : -2 ^ j < x ∧ x < 2 ^ j := by
  rw [← abs_lt, ← Int.natCast_natAbs]
  exact_mod_cast h

/-- `b.toInt` of a boolean is `0` or `1`. -/
theorem toInt_bounds (b : Bool) : 0 ≤ b.toInt ∧ b.toInt ≤ 1 :=
  b.casesOn ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩

end Fulcrum

end
