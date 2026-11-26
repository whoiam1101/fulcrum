module

public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Tactic.Ring.RingNF

/-!
# The product of two 128-bit words from four `u64 × u64` products

The math of `wide::widening_mul_u128`, no code. With `a = a₁ 2^64 + a₀`, `b = b₁ 2^64 + b₀` and
`mid = ⌊a₀b₀ / 2^64⌋ + (a₀b₁ mod 2^64) + (a₁b₀ mod 2^64)`, the top word
`a₁b₁ + ⌊a₀b₁ / 2^64⌋ + ⌊a₁b₀ / 2^64⌋ + ⌊mid / 2^64⌋` is `⌊a · b / 2^128⌋` (`widening_hi`) and
the low word `(mid mod 2^64) · 2^64 + (a₀b₀ mod 2^64)` is `a · b mod 2^128` (`widening_lo`).
-/

@[expose] public section

namespace Fulcrum

/-- The top word of `a · b` from four `u64 × u64` products: `a = a₁ 2^64 + a₀`,
`b = b₁ 2^64 + b₀`, `mid = ⌊a₀b₀ / 2^64⌋ + (a₀b₁ mod 2^64) + (a₁b₀ mod 2^64)`. -/
theorem widening_hi (a b : ℕ) :
    a / 2 ^ 64 * (b / 2 ^ 64) + a % 2 ^ 64 * (b / 2 ^ 64) / 2 ^ 64 + a / 2 ^ 64 * (b % 2 ^ 64) / 2 ^ 64 +
      (a % 2 ^ 64 * (b % 2 ^ 64) / 2 ^ 64 + a % 2 ^ 64 * (b / 2 ^ 64) % 2 ^ 64 +
        a / 2 ^ 64 * (b % 2 ^ 64) % 2 ^ 64) / 2 ^ 64 = a * b / 2 ^ 128 := by
  have ea := Nat.div_add_mod a (2 ^ 64)
  have eb := Nat.div_add_mod b (2 ^ 64)
  generalize a / 2 ^ 64 = a1 at ea ⊢
  generalize a % 2 ^ 64 = a0 at ea ⊢
  generalize b / 2 ^ 64 = b1 at eb ⊢
  generalize b % 2 ^ 64 = b0 at eb ⊢
  have p : a * b = a1 * b1 * 2 ^ 128 + a0 * b1 * 2 ^ 64 + a1 * b0 * 2 ^ 64 + a0 * b0 := by
    rw [← ea, ← eb]; ring
  rw [p]
  generalize a1 * b1 = P11
  generalize a0 * b1 = P01
  generalize a1 * b0 = P10
  generalize a0 * b0 = P00
  omega

/-- The low word of `a · b` from the same products: `(mid mod 2^64) · 2^64 + (a₀b₀ mod 2^64)`. -/
theorem widening_lo (a b : ℕ) :
    (a % 2 ^ 64 * (b % 2 ^ 64) / 2 ^ 64 + a % 2 ^ 64 * (b / 2 ^ 64) % 2 ^ 64 +
        a / 2 ^ 64 * (b % 2 ^ 64) % 2 ^ 64) % 2 ^ 64 * 2 ^ 64 + a % 2 ^ 64 * (b % 2 ^ 64) % 2 ^ 64 =
      a * b % 2 ^ 128 := by
  have ea := Nat.div_add_mod a (2 ^ 64)
  have eb := Nat.div_add_mod b (2 ^ 64)
  generalize a / 2 ^ 64 = a1 at ea ⊢
  generalize a % 2 ^ 64 = a0 at ea ⊢
  generalize b / 2 ^ 64 = b1 at eb ⊢
  generalize b % 2 ^ 64 = b0 at eb ⊢
  have p : a * b = a1 * b1 * 2 ^ 128 + a0 * b1 * 2 ^ 64 + a1 * b0 * 2 ^ 64 + a0 * b0 := by
    rw [← ea, ← eb]; ring
  rw [p]
  generalize a1 * b1 = P11
  generalize a0 * b1 = P01
  generalize a1 * b0 = P10
  generalize a0 * b0 = P00
  omega

end Fulcrum

end
