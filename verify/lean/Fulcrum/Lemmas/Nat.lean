module

public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.Ring.RingNF

/-!
# Natural-number facts used by several modules

The floor of a quotient from both sides, widths and sums of magnitudes that
fit a wide type, and `⌊√n⌋`: of `n < 2`, of a candidate whose square is at most `n` and
which is at least the root, of a quotient by a square, and the gap from
`n < (x + 1)²` to `x² + D · x`.
-/

@[expose] public section

namespace Fulcrum

/-- `a < (⌊a / b⌋ + 1) · b` for `b > 0`: the floor of a quotient from above. -/
theorem lt_succ_div_mul (a b : ℕ) (hb : 0 < b) : a < (a / b + 1) * b := by
  rw [Nat.add_mul, Nat.one_mul]
  exact Nat.lt_div_mul_add hb

/-- `q = ⌊a / 2^k⌋` is the floor from both sides: `q · 2^k ≤ a < (q + 1) · 2^k`. -/
theorem div_pow_bounds {q a k : ℕ} (h : q = a / 2 ^ k) : q * 2 ^ k ≤ a ∧ a < (q + 1) * 2 ^ k :=
  h ▸ ⟨Nat.div_mul_le_self _ _, lt_succ_div_mul _ _ (Nat.two_pow_pos _)⟩

/-- `k + 1 ≤ 2k + 2`: a type of `k + 1` bits fits its wide type. -/
theorem succ_le_two_mul_add_two (k : ℕ) : k + 1 ≤ 2 * k + 2 :=
  Nat.add_le_add (Nat.le_mul_of_pos_left k two_pos) one_le_two

/-- `a < n` once `2·a + 2·b < n`. -/
theorem lt_of_two_mul_add_lt {a b n : ℕ} (h : 2 * a + 2 * b < n) : a < n :=
  lt_of_le_of_lt ((Nat.le_mul_of_pos_left a two_pos).trans (Nat.le_add_right _ _)) h

/-- Magnitudes `x`, `y`, `z ≤ 2^k` with `k > 0` fit `2·(x·y) + 2·z < 2^(2k + 2)`. -/
theorem fit_mul_add (k x y z : ℕ) (hk : 0 < k) (hx : x ≤ 2 ^ k) (hy : y ≤ 2 ^ k)
    (hz : z ≤ 2 ^ k) : 2 * (x * y) + 2 * z < 2 ^ (2 * k + 2) :=
  calc 2 * (x * y) + 2 * z ≤ 2 * (2 ^ k * 2 ^ k) + 2 * 2 ^ k :=
        Nat.add_le_add (Nat.mul_le_mul_left 2 (Nat.mul_le_mul hx hy)) (Nat.mul_le_mul_left 2 hz)
    _ < 2 * (2 ^ k * 2 ^ k) + 2 * (2 ^ k * 2 ^ k) := Nat.add_lt_add_left
        (Nat.mul_lt_mul_of_pos_left (lt_mul_self (Nat.one_lt_two_pow hk.ne')) two_pos) _
    _ = 2 ^ (2 * k + 2) := by ring

/-- `0` and `1` are their own roots. -/
theorem sqrt_eq_self_of_lt_two (n : ℕ) (h : n < 2) : n = Nat.sqrt n := by
  rcases Nat.lt_succ_iff_lt_or_eq.mp h with e | e
  · rw [Nat.lt_one_iff.mp e]; rfl
  · rw [e]; rfl

/-- `x` is `⌊√n⌋` when `x² ≤ n` and `⌊√n⌋ ≤ x`. -/
theorem eq_sqrt_of_le (n x : ℕ) (le : x * x ≤ n) (ge : Nat.sqrt n ≤ x) : x = Nat.sqrt n :=
  Nat.eq_sqrt.mpr ⟨le, Nat.lt_of_lt_of_le (Nat.lt_succ_sqrt n)
    (Nat.mul_le_mul (Nat.succ_le_succ ge) (Nat.succ_le_succ ge))⟩

/-- `⌊√m⌋ / k = ⌊√(m / k²)⌋`. -/
theorem sqrt_div_eq (m k : ℕ) (hk : 0 < k) : Nat.sqrt m / k = Nat.sqrt (m / (k * k)) := by
  refine Nat.eq_sqrt.mpr ⟨?_, ?_⟩
  · refine (Nat.le_div_iff_mul_le (Nat.mul_pos hk hk)).mpr ?_
    have h := Nat.div_mul_le_self (Nat.sqrt m) k
    calc Nat.sqrt m / k * (Nat.sqrt m / k) * (k * k)
        = (Nat.sqrt m / k * k) * (Nat.sqrt m / k * k) := Nat.mul_mul_mul_comm _ _ _ _
      _ ≤ Nat.sqrt m * Nat.sqrt m := Nat.mul_le_mul h h
      _ ≤ m := Nat.sqrt_le m
  · refine (Nat.div_lt_iff_lt_mul (Nat.mul_pos hk hk)).mpr ?_
    have h : Nat.sqrt m + 1 ≤ (Nat.sqrt m / k + 1) * k := lt_succ_div_mul _ _ hk
    calc m < (Nat.sqrt m + 1) * (Nat.sqrt m + 1) := Nat.lt_succ_sqrt m
      _ ≤ ((Nat.sqrt m / k + 1) * k) * ((Nat.sqrt m / k + 1) * k) := Nat.mul_le_mul h h
      _ = (Nat.sqrt m / k + 1) * (Nat.sqrt m / k + 1) * (k * k) := Nat.mul_mul_mul_comm _ _ _ _

/-- `n ≤ x² + D · x` from `n < (x + 1)²` when `2 ≤ D`. -/
theorem le_sq_add_of_lt_succ_sq (n x D : ℕ) (hD : 2 ≤ D) (h : n < (x + 1) * (x + 1)) :
    n ≤ x * x + D * x :=
  Nat.le_of_lt_succ (h.trans_le (calc (x + 1) * (x + 1) = x * x + 2 * x + 1 := by ring
    _ ≤ x * x + D * x + 1 := Nat.add_le_add_right (Nat.add_le_add_left
      (Nat.mul_le_mul_right x hD) _) 1))

end Fulcrum

end
