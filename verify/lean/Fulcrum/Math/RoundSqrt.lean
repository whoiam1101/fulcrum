module

public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Prime.Basic

/-!
# Rounding a square root

`round √X` is `s = ⌊√X⌋` plus one exactly when `(s + ½)² < X`, when `X` is not
the tie `(s + ½)²`. For a natural `n` there is no tie, and the test is
`n - s² > s`, the one of `kernel::kN::sqrt_round`; for `X = 2^e / a` with
`a < 2^e` there is none either, since an odd square divides no power of two
but `1`, which `rsqrt` uses. No code here: the math of `sqrt`, `rsqrt`, `hypot`
and `hypot3` of L5.
-/

@[expose] public section

namespace Fulcrum

/-- `round √X = s + [(s + ½)² < X]` for `s = ⌊√X⌋` and `X` not a tie. -/
theorem round_sqrt_of_bounds (X : ℝ) (s : ℕ) (h1 : (s : ℝ) ^ 2 ≤ X) (h2 : X < ((s : ℝ) + 1) ^ 2)
    (hne : X ≠ ((s : ℝ) + 1 / 2) ^ 2) :
    round (Real.sqrt X) = (s : ℤ) + if ((s : ℝ) + 1 / 2) ^ 2 < X then 1 else 0 := by
  have s0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  rw [round_eq, Int.floor_eq_iff]
  split
  · next h =>
    have l : (s : ℝ) + 1 / 2 ≤ Real.sqrt X := (Real.le_sqrt (by linarith only [h2, h]) (by nlinarith only [h2, h])).2 h.le
    have u : Real.sqrt X < s + 1 := (Real.sqrt_lt' (by linarith only [h2, h])).2 h2
    push_cast
    constructor <;> linarith only [l, u]
  · next h =>
    have l : (s : ℝ) ≤ Real.sqrt X := (Real.le_sqrt s0 (by nlinarith only [h1])).2 h1
    have u : Real.sqrt X < s + 1 / 2 :=
      (Real.sqrt_lt' (by linarith only [])).2 (lt_of_le_of_ne (not_lt.mp h) hne)
    push_cast
    constructor <;> linarith only [l, u]

/-- `kernel::kN::sqrt_round` on naturals: `s = ⌊√n⌋`, plus one when
`n - s² > s`. -/
def sqrtRound (n : ℕ) : ℕ := Nat.sqrt n + if Nat.sqrt n * Nat.sqrt n + Nat.sqrt n < n then 1 else 0

/-- `round √n = s + [n - s² > s]` for a natural `n` and `s = ⌊√n⌋`. -/
theorem round_sqrt_nat (n : ℕ) : round (Real.sqrt n) = (sqrtRound n : ℤ) := by
  rw [sqrtRound, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  have h1 : ((Nat.sqrt n : ℕ) : ℝ) ^ 2 ≤ n := by
    have := Nat.sqrt_le n; rw [sq]; exact_mod_cast this
  have h2 : (n : ℝ) < ((Nat.sqrt n : ℕ) + 1) ^ 2 := by
    have := Nat.lt_succ_sqrt n; rw [sq]; exact_mod_cast this
  have t : ∀ s : ℕ, (n : ℝ) ≠ ((s : ℝ) + 1 / 2) ^ 2 := fun s e => by
    have : ((4 * n : ℕ) : ℝ) = (((2 * s + 1) * (2 * s + 1) : ℕ) : ℝ) := by push_cast; rw [e]; ring
    have h : 4 * n = (2 * s + 1) * (2 * s + 1) := by exact_mod_cast this
    have o : Odd ((2 * s + 1) * (2 * s + 1)) := (odd_two_mul_add_one s).mul (odd_two_mul_add_one s)
    rw [← h] at o
    exact (Nat.not_even_iff_odd.mpr o) ⟨2 * n, by ring⟩
  rw [round_sqrt_of_bounds n (Nat.sqrt n) h1 h2 (t _)]
  congr 1
  have e : (((Nat.sqrt n : ℝ) + 1 / 2) ^ 2 < n) ↔ Nat.sqrt n * Nat.sqrt n + Nat.sqrt n < n := by
    constructor
    · intro h
      have : (4 * (Nat.sqrt n * Nat.sqrt n + Nat.sqrt n) + 1 : ℝ) < 4 * n := by nlinarith only [h]
      have : 4 * (Nat.sqrt n * Nat.sqrt n + Nat.sqrt n) + 1 < 4 * n := by exact_mod_cast this
      omega
    · intro h
      have : Nat.sqrt n * Nat.sqrt n + Nat.sqrt n + 1 ≤ n := h
      have : (Nat.sqrt n * Nat.sqrt n + Nat.sqrt n + 1 : ℝ) ≤ n := by exact_mod_cast this
      nlinarith only [this]
  simp only [e]

/-- `round √(N / a) = s + [(2s + 1)² · a < 4N]` for `s = ⌊√⌊N / a⌋⌋`, with
`N = 2^e` and `0 < a < 4N`: no tie, since `(2s + 1)² · a = 4N` would make the
odd `(2s + 1)²` a divisor of a power of two, so `1`, and `a = 4N`. -/
theorem round_sqrt_pow_div (e a : ℕ) (ha : 0 < a) (hlt : a < 4 * 2 ^ e) :
    round (Real.sqrt ((2 ^ e : ℕ) / a : ℝ)) = (Nat.sqrt (2 ^ e / a) : ℤ) +
      if (2 * Nat.sqrt (2 ^ e / a) + 1) * (2 * Nat.sqrt (2 ^ e / a) + 1) * a < 4 * 2 ^ e then 1
      else 0 := by
  set N := 2 ^ e with hN
  set s := Nat.sqrt (N / a)
  have aR : (0 : ℝ) < a := by exact_mod_cast ha
  have h1 : s * s ≤ N / a := Nat.sqrt_le _
  have h2 : N / a < (s + 1) * (s + 1) := Nat.lt_succ_sqrt _
  have d1 : (N / a) * a ≤ N := Nat.div_mul_le_self N a
  have d2 : N < (N / a + 1) * a := by
    have := Nat.lt_div_mul_add (a := N) ha; nlinarith only [this]
  have b1 : (s : ℝ) ^ 2 ≤ (N : ℝ) / a := by
    rw [le_div_iff₀ aR]
    have : s * s * a ≤ N := (Nat.mul_le_mul_right a h1).trans d1
    have : ((s * s * a : ℕ) : ℝ) ≤ N := by exact_mod_cast this
    push_cast at this; nlinarith only [this]
  have b2 : (N : ℝ) / a < ((s : ℝ) + 1) ^ 2 := by
    rw [div_lt_iff₀ aR]
    have : N < (s + 1) * (s + 1) * a :=
      d2.trans_le (Nat.mul_le_mul_right a (Nat.succ_le_of_lt h2))
    have : (N : ℝ) < (((s + 1) * (s + 1) * a : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this; nlinarith only [this]
  have iff : ((s : ℝ) + 1 / 2) ^ 2 < (N : ℝ) / a ↔ (2 * s + 1) * (2 * s + 1) * a < 4 * N := by
    rw [lt_div_iff₀ aR]
    constructor
    · intro h
      have : (((2 * s + 1) * (2 * s + 1) * a : ℕ) : ℝ) < ((4 * N : ℕ) : ℝ) := by
        push_cast; nlinarith only [h]
      exact_mod_cast this
    · intro h
      have : (((2 * s + 1) * (2 * s + 1) * a : ℕ) : ℝ) < ((4 * N : ℕ) : ℝ) := by exact_mod_cast h
      push_cast at this; nlinarith only [this]
  have tie : (N : ℝ) / a ≠ ((s : ℝ) + 1 / 2) ^ 2 := by
    intro t
    rw [div_eq_iff aR.ne'] at t
    have : ((4 * N : ℕ) : ℝ) = (((2 * s + 1) * (2 * s + 1) * a : ℕ) : ℝ) := by
      push_cast; rw [t]; ring
    have t' : 4 * N = (2 * s + 1) * (2 * s + 1) * a := by exact_mod_cast this
    have dv : (2 * s + 1) * (2 * s + 1) ∣ 2 ^ (e + 2) := ⟨a, by rw [pow_add, ← hN, ← t']; ring⟩
    have cop : Nat.Coprime ((2 * s + 1) * (2 * s + 1)) (2 ^ (e + 2)) :=
      Nat.Coprime.pow_right _ (by
        rw [Nat.coprime_two_right]
        exact Odd.mul (odd_two_mul_add_one s) (odd_two_mul_add_one s))
    have one : (2 * s + 1) * (2 * s + 1) = 1 := Nat.Coprime.eq_one_of_dvd cop dv
    rw [one, one_mul] at t'
    omega
  rw [round_sqrt_of_bounds _ s b1 b2 tie]
  simp only [iff]

/-- `round √n ≤ m` for `n < m²`. -/
theorem sqrtRound_le (n m : ℕ) (h : n < m * m) : sqrtRound n ≤ m := by
  have := Nat.sqrt_lt.mpr h
  unfold sqrtRound
  split <;> omega

end Fulcrum

end
