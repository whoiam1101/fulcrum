module

public import Fulcrum.Spec

/-!
# L1: the rounding rule of `kernel::shr_round`

Shifting right by `k + 1` after adding `2^k` is rounding to nearest with ties
toward `+∞`, for every shift. `kernel::shr_round` takes the same value as the
floor plus the first dropped bit, and returns `0` for shifts of `128` and
more, which is the rounded value for every `i128`.
-/

@[expose] public section

namespace Fulcrum

/-- `kernel::shr_round` on unbounded integers: `⌊n / 2^s⌋` plus the first
dropped bit. -/
def shrRound (n : ℤ) (s : ℕ) : ℤ :=
  if s = 0 then n else (n >>> s) + (n >>> (s - 1)) % 2

/-- `kernel::shr_round` with the branch for shifts of `128` and more. -/
def shrRound128 (n : ℤ) (s : ℕ) : ℤ :=
  if s = 0 then n else if 128 ≤ s then 0 else (n >>> s) + (n >>> (s - 1)) % 2

/-- A right shift of an integer is the floor of its quotient by `2^s`. -/
theorem shr_eq_div (n : ℤ) (s : ℕ) : n >>> s = n / 2 ^ s := by
  rw [Int.shiftRight_eq_div_pow, Nat.cast_pow, Nat.cast_ofNat]

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
  · simp only [↓reduceIte, roundHalfUp, exact, pow_zero, div_one]
    rw [eq_comm, Int.floor_eq_iff]
    exact ⟨le_add_of_nonneg_right one_half_pos.le, add_lt_add_right one_half_lt_one _⟩
  · simp only [Nat.add_one_ne_zero, ↓reduceIte]
    rw [← add_half_shr, Nat.add_sub_cancel,
      shr_eq_div, shr_eq_div, shr_eq_div]
    have hd : (0 : ℤ) < 2 ^ k := pow_pos zero_lt_two k
    rw [pow_succ, ← Int.ediv_ediv_of_nonneg hd.le, ← Int.ediv_ediv_of_nonneg hd.le]
    have e := Int.add_mul_ediv_right n 1 hd.ne'
    rw [one_mul] at e
    rw [e]
    omega

/-- The rounded value of an `i128` shifted by `128` or more is `0`, so
`shrRound128` equals the rounding on the whole range of `i128`. -/
theorem shrRound128_eq (n : ℤ) (s : ℕ) (lo : -2 ^ 127 ≤ n) (hi : n < 2 ^ 127) :
    shrRound128 n s = roundHalfUp (exact s n) := by
  rw [← shrRound_eq]
  unfold shrRound128
  split
  · next h0 => simp only [shrRound, h0, ite_true]
  split
  · next h0 hs =>
    obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, (Nat.succ_pred_eq_of_ne_zero h0).symm⟩
    rw [shrRound_eq, ← add_half_shr, shr_eq_div]
    have hk : (2 : ℤ) ^ 127 ≤ 2 ^ k := pow_le_pow_right₀ one_le_two' (Nat.le_of_succ_le_succ hs)
    rw [pow_succ]
    exact (Int.ediv_eq_zero_of_lt (neg_le_iff_add_nonneg.mp ((neg_le_neg hk).trans lo))
      (mul_two ((2 : ℤ) ^ k) ▸ add_lt_add_left (hi.trans_le hk) _)).symm
  · next h0 hs => simp only [shrRound, h0, ite_false]

end Fulcrum

end
