module

public import Fulcrum.Math.Round
public import Fulcrum.Lemmas.Scalar

/-!
# L1: the rounding rule of `kernel::shr_round`

`kernel::shr_round` takes the floor plus the first dropped bit (`shrRound_eq`
of `Math/Round.lean`), and returns `0` for shifts of `128` and more, which is
the rounded value for every `i128`. `shr_round_spec` states it on
`kernel::shr_round` itself, as Aeneas extracts it to `Fulcrum.Kernel`.
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace Fulcrum

/-- An `i128` shifted right by a non-zero `s` is in `[-2^126, 2^126)`. -/
theorem shr_bounds (n : ℤ) (s : ℕ) (hs : s ≠ 0) (lo : -2 ^ 127 ≤ n) (hi : n < 2 ^ 127) :
    -2 ^ 126 ≤ n >>> s ∧ n >>> s < 2 ^ 126 := by
  have two : (2 : ℤ) ≤ 2 ^ s := le_self_pow₀ one_le_two hs
  have pos : (0 : ℤ) < 2 ^ s := pow_pos zero_lt_two _
  have p126 : (0 : ℤ) ≤ 2 ^ 126 := (pow_pos zero_lt_two 126).le
  rw [shr_eq_div, Int.le_ediv_iff_mul_le pos, Int.ediv_lt_iff_lt_mul pos]
  exact ⟨(mul_le_mul_of_nonpos_left two (neg_nonpos.mpr p126)).trans lo,
    hi.trans_le (mul_le_mul_of_nonneg_left two p126)⟩

/-- The last step of `shr_round`: the floor `i = n >> s` plus the last bit of
`i2 = n >> (s - 1)` is the rounded value, for every `i128` and `s ≠ 0`. -/
theorem add_bit_spec (n : ℤ) (s : ℕ) (hs : s ≠ 0) (lo : -2 ^ 127 ≤ n) (hi : n < 2 ^ 127)
    (i i2 : Std.I128) (hi1 : i.val = n >>> s) (hi2 : i2.val = n >>> (s - 1)) :
    (do let i3 ← lift (i2 &&& 1#i128); i + i3) ⦃ r => r.val = roundHalfUp (exact s n) ⦄ := by
  rw [lift, bind_ok]
  have ⟨l, u⟩ := shr_bounds n s hs lo hi
  have bit := and_one_val i2
  have b0 : 0 ≤ i2.val % 2 := Int.emod_nonneg _ two_ne_zero
  have b1 : i2.val % 2 < 2 := Int.emod_lt_of_pos _ zero_lt_two
  have p : (2 : ℤ) ^ 126 ≤ 2 ^ 127 := pow_le_pow_right₀ one_le_two (Nat.le_succ 126)
  have two : (2 : ℤ) ≤ 2 ^ 126 := le_self_pow₀ one_le_two (Nat.succ_ne_zero 125)
  have top : (2 : ℤ) ^ 126 + 2 ≤ 2 ^ 127 :=
    (add_le_add_left two _).trans_eq ((mul_two _).symm.trans (pow_succ 2 126).symm)
  have ⟨fl, fu⟩ := in_bounds_of_pow (W := .I128) (m := 127) rfl
    ((neg_le_neg p).trans (le_add_of_le_of_nonneg (hi1 ▸ l) b0))
    ((add_lt_add (hi1 ▸ u) b1).trans_le top)
  refine WP.spec_mono (IScalar.add_spec (bit ▸ fl) (bit ▸ fu)) fun r hr => ?_
  rw [hr, bit, hi1, hi2, ← shrRound_eq, shrRound, ite_eq_right hs]

/-- The rounded value of an `i128` shifted by `128` or more is `0`. -/
theorem round_eq_zero_of_ge (n : ℤ) (s : ℕ) (hs : 128 ≤ s) (lo : -2 ^ 127 ≤ n)
    (hi : n < 2 ^ 127) : roundHalfUp (exact s n) = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, (Nat.succ_pred_eq_of_ne_zero
    (Nat.pos_iff_ne_zero.mp (Nat.lt_of_lt_of_le (Nat.succ_pos 127) hs))).symm⟩
  rw [← add_half_shr, shr_eq_div]
  have hk : (2 : ℤ) ^ 127 ≤ 2 ^ k := pow_le_pow_right₀ one_le_two (Nat.le_of_succ_le_succ hs)
  rw [pow_succ]
  exact Int.ediv_eq_zero_of_lt (neg_le_iff_add_nonneg.mp ((neg_le_neg hk).trans lo))
    (mul_two ((2 : ℤ) ^ k) ▸ add_lt_add_left (hi.trans_le hk) _)

/-- L1 on the code: `kernel::shr_round`, extracted by Aeneas, never fails and
rounds `n / 2^s` to nearest, ties toward `+∞`, for every `i128` and `u32`. -/
theorem shr_round_spec (n : Std.I128) (s : Std.U32) :
    fulcrum.kernel.shr_round n s ⦃ r => r.val = roundHalfUp (exact s.val n.val) ⦄ := by
  unfold fulcrum.kernel.shr_round
  by_cases h0 : s = 0#u32
  · rw [ite_eq_left h0, WP.spec_ok, ← shrRound_eq, shrRound,
      ite_eq_left (c := s.val = 0) (congrArg UScalar.val h0)]
  have v0 : s.val ≠ 0 := fun e => h0 (UScalar.eq_of_val_eq e)
  rw [ite_eq_right h0]
  by_cases hs : s ≥ 128#u32
  · rw [ite_eq_left hs, WP.spec_ok, round_eq_zero_of_ge n.val s.val hs n.hmin n.hmax]
    rfl
  have lt : s.val < 128 := Nat.lt_of_not_le hs
  rw [ite_eq_right hs]
  refine WP.spec_bind (IScalar.ShiftRight_spec n s lt) fun i ⟨hi, _⟩ => ?_
  refine WP.spec_bind (U32.sub_spec (x := s) (y := 1#u32) (Nat.one_le_iff_ne_zero.mpr v0))
    fun i1 ⟨hi1, _⟩ => ?_
  refine WP.spec_bind (IScalar.ShiftRight_spec n i1 (hi1 ▸ Nat.sub_lt_of_lt lt))
    fun i2 ⟨hi2, _⟩ => ?_
  exact add_bit_spec n.val s.val v0 n.hmin n.hmax i i2 hi (hi1 ▸ hi2)

end Fulcrum

end
