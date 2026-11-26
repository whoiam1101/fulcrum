module

public import Mathlib.Data.Nat.Notation
import Mathlib.Tactic.Ring.RingNF

/-!
# The rounding of `scale_to` on 64 bits

The math of `kernel::k64::scale_to`, no code. For `p² = Q · s + R` with `R < s` and
`t = ⌊√Q⌋`, the magnitude `p / √s` rounds to `t + 1` when `Q > t² + t`, or `Q = t² + t` and
`4R > s`, and to `t` otherwise. The lemmas give the weak sides of `ScaleRound` for that
magnitude: `4p² ≤ (2m + 1)² s` (`up_hup`, `down_hup_neg`, `down_hup_mid`) and
`(2m - 1)² s ≤ 4p²` (`up_hlo_pos`, `up_hlo_mid`, `down_hlo`); with no tie they are strict
(`scaleRound_of_walk` of `L5/Scale.lean`). A magnitude with the weak lower side stays at most
`k` when `p² ≤ k² s` (`round_le`).
-/

@[expose] public section

namespace Fulcrum

/-- `p² < (t + 1)² s`, so `4p² ≤ (2(t + 1) + 1)² s`. -/
theorem up_hup (p s Q R t : ℕ) (hP : p * p = Q * s + R) (hR : R < s) (ht : Q < (t + 1) * (t + 1)) :
    4 * p * p ≤ (2 * (t + 1) + 1) * (2 * (t + 1) + 1) * s := by
  have h : Q + 1 ≤ t * t + 2 * t + 1 := by
    have : (t + 1) * (t + 1) = t * t + 2 * t + 1 := by ring
    omega
  have m := Nat.mul_le_mul_right s h
  have e1 : (Q + 1) * s = Q * s + s := by ring
  have e2 : (t * t + 2 * t + 1) * s = t * t * s + 2 * (t * s) + s := by ring
  have e3 : (2 * (t + 1) + 1) * (2 * (t + 1) + 1) * s = 4 * (t * t * s) + 12 * (t * s) + 9 * s := by ring
  have e4 : 4 * p * p = 4 * (p * p) := by ring
  omega

/-- `Q ≥ t² + t + 1` gives `(2t + 1)² s ≤ 4p²`. -/
theorem up_hlo_pos (p s Q R t : ℕ) (hP : p * p = Q * s + R) (hQ : t * t + t < Q) :
    (2 * (t + 1) - 1) * (2 * (t + 1) - 1) * s ≤ 4 * p * p := by
  have m := Nat.mul_le_mul_right s (Nat.succ_le_of_lt hQ)
  have e1 : (t * t + t).succ * s = t * t * s + t * s + s := by rw [Nat.succ_eq_add_one]; ring
  have e2 : (2 * (t + 1) - 1) * (2 * (t + 1) - 1) * s = 4 * (t * t * s) + 4 * (t * s) + s := by
    rw [show 2 * (t + 1) - 1 = 2 * t + 1 by omega]; ring
  have e4 : 4 * p * p = 4 * (p * p) := by ring
  omega

/-- `Q = t² + t` and `4R > s` give `(2t + 1)² s ≤ 4p²`. -/
theorem up_hlo_mid (p s Q R t : ℕ) (hP : p * p = Q * s + R) (hQ : Q = t * t + t) (hR : s < 4 * R) :
    (2 * (t + 1) - 1) * (2 * (t + 1) - 1) * s ≤ 4 * p * p := by
  subst hQ
  have e1 : (t * t + t) * s = t * t * s + t * s := by ring
  have e2 : (2 * (t + 1) - 1) * (2 * (t + 1) - 1) * s = 4 * (t * t * s) + 4 * (t * s) + s := by
    rw [show 2 * (t + 1) - 1 = 2 * t + 1 by omega]; ring
  have e4 : 4 * p * p = 4 * (p * p) := by ring
  omega

/-- `Q < t² + t` gives `4p² ≤ (2t + 1)² s`. -/
theorem down_hup_neg (p s Q R t : ℕ) (hP : p * p = Q * s + R) (hR : R < s) (hQ : Q < t * t + t) :
    4 * p * p ≤ (2 * t + 1) * (2 * t + 1) * s := by
  have m := Nat.mul_le_mul_right s (Nat.succ_le_of_lt hQ)
  have e1 : Q.succ * s = Q * s + s := by rw [Nat.succ_eq_add_one]; ring
  have e2 : (t * t + t) * s = t * t * s + t * s := by ring
  have e3 : (2 * t + 1) * (2 * t + 1) * s = 4 * (t * t * s) + 4 * (t * s) + s := by ring
  have e4 : 4 * p * p = 4 * (p * p) := by ring
  omega

/-- `Q = t² + t` and `4R ≤ s` give `4p² ≤ (2t + 1)² s`. -/
theorem down_hup_mid (p s Q R t : ℕ) (hP : p * p = Q * s + R) (hQ : Q = t * t + t) (hR : 4 * R ≤ s) :
    4 * p * p ≤ (2 * t + 1) * (2 * t + 1) * s := by
  subst hQ
  have e1 : (t * t + t) * s = t * t * s + t * s := by ring
  have e3 : (2 * t + 1) * (2 * t + 1) * s = 4 * (t * t * s) + 4 * (t * s) + s := by ring
  have e4 : 4 * p * p = 4 * (p * p) := by ring
  omega

/-- `t² ≤ Q` gives `(2t - 1)² s ≤ 4p²`. -/
theorem down_hlo (p s Q R t : ℕ) (hP : p * p = Q * s + R) (ht : t * t ≤ Q) :
    (2 * t - 1) * (2 * t - 1) * s ≤ 4 * p * p := by
  have o : (2 * t - 1) * (2 * t - 1) ≤ 4 * (t * t) := by
    have := Nat.mul_le_mul (Nat.sub_le (2 * t) 1) (Nat.sub_le (2 * t) 1)
    exact this.trans_eq (by ring)
  have m := Nat.mul_le_mul_right s (o.trans (Nat.mul_le_mul_left 4 ht))
  have e1 : 4 * Q * s = 4 * (Q * s) := by ring
  have e4 : 4 * p * p = 4 * (p * p) := by ring
  omega

/-- A magnitude with `(2m - 1)² s ≤ 4p²` and `p² ≤ k² s` is at most `k`. -/
theorem round_le (p s k m : ℕ) (hs : 0 < s) (hpk : p * p ≤ k * k * s)
    (hlo : m = 0 ∨ (2 * m - 1) * (2 * m - 1) * s ≤ 4 * p * p) : m ≤ k := by
  rcases hlo with h | hlo
  · omega
  have le : (2 * m - 1) * (2 * m - 1) * s ≤ 2 * k * (2 * k) * s := by
    have e : 2 * k * (2 * k) * s = 4 * (k * k * s) := by ring
    have e4 : 4 * p * p = 4 * (p * p) := by ring
    omega
  have sq := Nat.mul_self_le_mul_self_iff.mp (Nat.le_of_mul_le_mul_right le hs)
  omega

end Fulcrum

end
