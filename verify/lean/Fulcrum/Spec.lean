module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Rat.Floor

/-!
# Specification of fulcrum (docs/ARCHITECTURE.md §6.1.1)

A raw integer with `n` fractional bits has the exact value `raw / 2^n`. Every
kernel that drops bits rounds that value to nearest with ties toward `+∞`, and
a result of `b` bits is one of the integers of two's complement on `b` bits.
-/

@[expose] public section

namespace Fulcrum

/-- The exact value `raw / 2^n` of a raw integer with `n` fractional bits. -/
def exact (n : ℕ) (raw : ℤ) : ℚ := raw / 2 ^ n

/-- Rounding to nearest, ties toward `+∞`: `⌊q + ½⌋`. -/
def roundHalfUp (q : ℚ) : ℤ := ⌊q + 1 / 2⌋

/-- The smallest integer of two's complement on `k + 1` bits, `-2^k`. -/
def minOf (k : ℕ) : ℤ := -2 ^ k

/-- The largest integer of two's complement on `k + 1` bits, `2^k - 1`. -/
def maxOf (k : ℕ) : ℤ := 2 ^ k - 1

/-- `w` is an integer of two's complement on `k + 1` bits. -/
def InRange (k : ℕ) (w : ℤ) : Prop := minOf k ≤ w ∧ w ≤ maxOf k

instance (k : ℕ) (w : ℤ) : Decidable (InRange k w) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- `MIN ≤ MAX` for every width. -/
theorem minOf_le_maxOf (k : ℕ) : minOf k ≤ maxOf k := by
  have h : (1 : ℤ) ≤ 2 ^ k := one_le_pow₀ one_le_two
  exact (neg_nonpos.mpr (zero_le_one.trans h)).trans (sub_nonneg.mpr h)

/-- `w` clamped to `[minOf k, maxOf k]`. -/
def clamp (k : ℕ) (w : ℤ) : ℤ := max (minOf k) (min (maxOf k) w)

end Fulcrum

end
