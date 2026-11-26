module

public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Prime.Basic

/-!
# A component of a vector scaled to a length

A component `x` of a vector with squared length `s = a² + b² + c² > 0`, scaled to
the length `k`, has magnitude `p / √s` for `p = |x| · k`. Its rounded value is the
`m` with `(2m - 1)² s < 4p² < (2m + 1)² s` (`m = 0` needs only the right side,
`ScaleRound`), and it is `round (p / √s)` (`scaleRound_eq`). There are no ties:
`o² (a² + b² + c²) = 4 a² k²` has no solution with an odd `o` (`no_tie`), since
it makes `a² + b² + c²` a multiple of `4`, so `a`, `b`, `c` even, and halving them
gives a smaller solution. No code here: the math of `scale_vec` of L5.
-/

@[expose] public section

namespace Fulcrum

/-- `m` is the magnitude `p / √s` rounded: `4p²` lies strictly between
`(2m - 1)² s` and `(2m + 1)² s`, the left side dropped for `m = 0`. -/
def ScaleRound (p s m : ℕ) : Prop :=
  4 * p * p < (2 * m + 1) * (2 * m + 1) * s ∧ (m = 0 ∨ (2 * m - 1) * (2 * m - 1) * s < 4 * p * p)

/-- `x²` is `0` or `1` modulo `4`, by the parity of `x`. -/
theorem sq_halves (x : ℕ) : ∃ t e, x = 2 * t + e ∧ e ≤ 1 ∧ x * x = 4 * (t * t + t * e) + e := by
  obtain ⟨t, ht | ht⟩ := Nat.even_or_odd' x
  · exact ⟨t, 0, by omega, by omega, by subst ht; ring⟩
  · exact ⟨t, 1, ht, le_refl 1, by subst ht; ring⟩

/-- No tie: `o² (a² + b² + c²) ≠ 4 (a k)²` for an odd `o` and `a² + b² + c² > 0`. -/
theorem no_tie (o k : ℕ) (ho : Odd o) :
    ∀ a b c : ℕ, 0 < a * a + b * b + c * c →
      o * o * (a * a + b * b + c * c) ≠ 4 * (a * k) * (a * k) := by
  suffices H : ∀ n, ∀ a b c : ℕ, a * a + b * b + c * c = n → 0 < n →
      o * o * n ≠ 4 * (a * k) * (a * k) from
    fun a b c hpos => H _ a b c rfl hpos
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b c h hpos e
    have cop : Nat.Coprime (o * o) 4 := by
      have : Nat.Coprime (o * o) 2 := Nat.coprime_two_right.mpr (ho.mul ho)
      simpa using Nat.Coprime.pow_right 2 this
    have d4 : 4 ∣ n := cop.symm.dvd_of_dvd_mul_left ⟨(a * k) * (a * k), by rw [e]; ring⟩
    obtain ⟨ta, ea, ha, ea1, sa⟩ := sq_halves a
    obtain ⟨tb, eb, hb, eb1, sb⟩ := sq_halves b
    obtain ⟨tc, ec, hc, ec1, sc⟩ := sq_halves c
    rw [← h, sa, sb, sc] at d4
    have e0 : ea = 0 ∧ eb = 0 ∧ ec = 0 := by omega
    obtain ⟨rfl, rfl, rfl⟩ := e0
    have hs : a * a + b * b + c * c = 4 * (ta * ta + tb * tb + tc * tc) := by
      rw [sa, sb, sc]; ring
    have pos : 0 < ta * ta + tb * tb + tc * tc := by omega
    refine ih (ta * ta + tb * tb + tc * tc) (by omega) ta tb tc rfl pos ?_
    simp only [add_zero] at ha
    rw [← h, hs, ha] at e
    have : 4 * (o * o * (ta * ta + tb * tb + tc * tc)) = 4 * (4 * (ta * k) * (ta * k)) := by
      rw [← mul_assoc 4 (o * o), mul_comm 4 (o * o), mul_assoc, e]; ring
    omega

/-- The rounded magnitude is `round (p / √s)`. -/
theorem scaleRound_eq (p s m : ℕ) (hs : 0 < s) (h : ScaleRound p s m) :
    round ((p : ℝ) / Real.sqrt s) = m := by
  obtain ⟨hu, hl⟩ := h
  have sR : (0 : ℝ) < s := by exact_mod_cast hs
  set t := Real.sqrt s with ht
  have t0 : 0 < t := Real.sqrt_pos.mpr sR
  have tt : t * t = s := Real.mul_self_sqrt sR.le
  have p0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have m0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hu' : (4 * p * p : ℝ) < (2 * m + 1) * (2 * m + 1) * s := by exact_mod_cast hu
  have up : 2 * (p : ℝ) < (2 * m + 1) * t := by
    by_contra c
    have c := not_lt.mp c
    have := mul_self_le_mul_self (by positivity) c
    nlinarith only [tt, hu', this]
  rw [round_eq, Int.floor_eq_iff]
  have pt : 0 ≤ (p : ℝ) / t := by positivity
  constructor
  · have key : (m : ℝ) - 1 / 2 ≤ p / t := by
      rcases Nat.eq_zero_or_pos m with h0 | m1
      · subst h0; push_cast; linarith only [pt]
      rcases hl with h0 | hl
      · omega
      have c : ((2 * m - 1 : ℕ) : ℝ) = 2 * m - 1 := by
        push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * m)]; ring
      have hl' : ((2 * m - 1 : ℕ) : ℝ) * ((2 * m - 1 : ℕ) : ℝ) * s < 4 * p * p := by
        exact_mod_cast hl
      rw [c] at hl'
      have m1' : (1 : ℝ) ≤ m := by exact_mod_cast m1
      have lo : (2 * m - 1) * t ≤ 2 * (p : ℝ) := by
        by_contra c
        have c := (not_le.mp c).le
        have := mul_self_le_mul_self (by positivity) c
        nlinarith only [tt, hl', this]
      rw [le_div_iff₀ t0]; linarith only [lo]
    push_cast; linarith only [key]
  · push_cast
    have : (p : ℝ) / t < m + 1 / 2 := by rw [div_lt_iff₀ t0]; linarith only [up]
    linarith only [this]

/-- The component `x` of a vector with squared length `s`, scaled to the length
`k`: `round (|x| · k / √s)` with the sign of `x`. -/
noncomputable def scaled (x : ℤ) (k s : ℕ) : ℤ :=
  if x < 0 then -round (((x.natAbs * k : ℕ) : ℝ) / Real.sqrt s)
  else round (((x.natAbs * k : ℕ) : ℝ) / Real.sqrt s)

/-- The zero component stays zero. -/
theorem scaled_zero (k s : ℕ) : scaled 0 k s = 0 := by
  simp [scaled]

end Fulcrum

end
