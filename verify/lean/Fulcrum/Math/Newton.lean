module

public import Mathlib.Data.Nat.Notation
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic.Ring.RingNF

/-!
# One Newton step for `⌊√n⌋`

One step `(x + ⌊n / x⌋) / 2` from any `x > 0` is at least `⌊√n⌋`
(`sqrt_le_newton`), and from a start whose square is within `D · x` of `n` the
sum and the square of the step are bounded by `n` and `D` (`newton_bound`). No
code here: shared by the `isqrt` of `k8`, `k16` and `k64`.
-/

@[expose] public section

namespace Fulcrum

/-- `2·⌊√n⌋ ≤ x + ⌊n / x⌋` for `x > 0`: the arithmetic mean bound. -/
theorem two_sqrt_le (n x : ℕ) (hx : 0 < x) : 2 * Nat.sqrt n ≤ x + n / x := by
  set s := Nat.sqrt n
  by_cases h : 2 * s ≤ x
  · exact h.trans (Nat.le_add_right _ _)
  have amgm : ((2 * s - x : ℕ) : ℤ) * x ≤ (s : ℤ) * s := by
    rw [Nat.cast_sub (Nat.lt_of_not_le h).le, Nat.cast_mul, Nat.cast_ofNat]
    have e : (s : ℤ) * s - (2 * s - x) * x = (s - x) * (s - x) := by ring
    exact sub_nonneg.mp (e ▸ mul_self_nonneg _)
  have : (2 * s - x) * x ≤ n := (Int.ofNat_le.mp (by exact_mod_cast amgm)).trans (Nat.sqrt_le n)
  have := (Nat.le_div_iff_mul_le hx).mpr this
  omega

/-- One Newton step from any `x > 0` stays at or above `⌊√n⌋`. -/
theorem sqrt_le_newton (n x : ℕ) (hx : 0 < x) : Nat.sqrt n ≤ (x + n / x) / 2 :=
  (Nat.le_div_iff_mul_le two_pos).mpr (by rw [mul_comm]; exact two_sqrt_le n x hx)

/-- One Newton step from `x₀` with `x₀² ≈ n` within `D · x₀`: the sum and the
square of the step are bounded by `n` and `D`. -/
theorem newton_bound (n x0 D : ℕ) (h1 : 1 ≤ x0) (hu : x0 * x0 ≤ n + D * x0)
    (hl : n ≤ x0 * x0 + D * x0) :
    x0 + n / x0 ≤ 2 * x0 + D ∧
      4 * ((x0 + n / x0) / 2 * ((x0 + n / x0) / 2)) ≤ D * D + 4 * n := by
  set q := n / x0
  have hq1 : q * x0 ≤ n := Nat.div_mul_le_self n x0
  have hq2 : n < q * x0 + x0 := Nat.lt_div_mul_add h1
  have hxq : x0 ≤ q + D := by
    by_contra hc
    have : (q + D + 1) * x0 ≤ x0 * x0 := Nat.mul_le_mul_right _ (by omega)
    have e : (q + D + 1) * x0 = q * x0 + D * x0 + x0 := by ring
    omega
  have hqx : q ≤ x0 + D := by
    by_contra hc
    have : (x0 + D + 1) * x0 ≤ q * x0 := Nat.mul_le_mul_right _ (by omega)
    have e : (x0 + D + 1) * x0 = x0 * x0 + D * x0 + x0 := by ring
    omega
  refine ⟨by omega, ?_⟩
  have h2 : 2 * ((x0 + q) / 2) ≤ x0 + q := Nat.mul_div_le _ _
  have sq : 4 * ((x0 + q) / 2 * ((x0 + q) / 2)) ≤ (x0 + q) * (x0 + q) := by
    calc 4 * ((x0 + q) / 2 * ((x0 + q) / 2))
        = (2 * ((x0 + q) / 2)) * (2 * ((x0 + q) / 2)) := by ring
      _ ≤ (x0 + q) * (x0 + q) := Nat.mul_le_mul h2 h2
  rcases le_total x0 q with hle | hle
  · obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hle
    rw [he] at sq hq1 hqx ⊢
    have ee : e * e ≤ D * D := Nat.mul_le_mul (by omega) (by omega)
    have id : (x0 + (x0 + e)) * (x0 + (x0 + e)) = e * e + 4 * ((x0 + e) * x0) := by ring
    omega
  · obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hle
    rw [he] at sq hq1 ⊢
    have ee : e * e ≤ D * D := Nat.mul_le_mul (by omega) (by omega)
    have id : (q + e + q) * (q + e + q) = e * e + 4 * (q * (q + e)) := by ring
    omega

end Fulcrum

end
