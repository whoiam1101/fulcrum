module

public import Fulcrum.Spec
public import Fulcrum.Lemmas.Int

/-!
# Ranges of two's complement on `k + 1` bits

The high bits `w >>> k` are all zeros or all ones exactly when `w` is in
`[MIN, MAX]`, and the cast to `k + 1` bits, two's complement wrapping
`Int.bmod w (2^(k+1))`, keeps `w` exactly then; `saturate` of the kernel is
the clamp. No code here: the models of L2, used by L2, `rescale` and `div`.
-/

@[expose] public section

namespace Fulcrum

/-- The cast `w as $Bits` of a wide value to `k + 1` bits: two's complement
wrapping. -/
def wrap (k : ℕ) (w : ℤ) : ℤ := w.bmod (2 ^ (k + 1))

/-- `kernel::saturate`: `MAX` above it, `MIN` below it, the cast otherwise. -/
def saturate (k : ℕ) (w : ℤ) : ℤ :=
  if maxOf k < w then maxOf k else if w < minOf k then minOf k else wrap k w

/-- The high bits of `w` from bit `k` up are all zeros or all ones exactly
when `w` fits `k + 1` bits. -/
theorem inRange_iff_high_bits (k : ℕ) (w : ℤ) :
    InRange k w ↔ w >>> k = 0 ∨ w >>> k = -1 := by
  have hd : (0 : ℤ) < 2 ^ k := pow_pos zero_lt_two k
  have lo := Int.le_ediv_iff_mul_le (a := -1) (b := w) hd
  have hi := Int.ediv_lt_iff_lt_mul (a := w) (b := 1) hd
  rw [InRange, minOf, maxOf, shr_eq_div]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := lo.2 (by rw [neg_mul, one_mul]; exact h.1)
    have := hi.2 (by rw [one_mul]; exact Int.le_sub_one_iff.mp h.2)
    omega
  · have l := lo.1 (h.elim (fun hl => hl ▸ neg_one_lt_zero.le) (fun hr => hr.ge))
    have u := hi.1 (h.elim
      (fun hl => hl.trans_lt zero_lt_one)
      (fun hr => hr.trans_lt (neg_one_lt_zero.trans zero_lt_one)))
    exact ⟨neg_one_mul ((2 : ℤ) ^ k) ▸ l, Int.le_sub_one_of_lt (one_mul ((2 : ℤ) ^ k) ▸ u)⟩

/-- The cast to `k + 1` bits keeps `w` exactly when `w` fits them. -/
theorem wrap_eq_self_iff (k : ℕ) (w : ℤ) : wrap k w = w ↔ InRange k w := by
  have hm : 0 < 2 ^ (k + 1) := pow_pos zero_lt_two (k + 1)
  have half : ((2 ^ (k + 1) : ℕ) : ℤ) / 2 = 2 ^ k := by
    rw [Nat.cast_pow, Nat.cast_ofNat, pow_succ]
    exact mul_div_cancel_right₀ _ two_ne_zero
  have half' : (((2 ^ (k + 1) : ℕ) : ℤ) + 1) / 2 = 2 ^ k := by
    rw [Nat.cast_pow, Nat.cast_ofNat, pow_succ, add_comm, Int.add_mul_ediv_right _ _ two_ne_zero]
    exact zero_add _
  rw [wrap, InRange, minOf, maxOf]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have l := Int.le_bmod (x := w) hm
    have u := Int.bmod_lt (x := w) hm
    rw [h, half] at l
    rw [h, half'] at u
    exact ⟨l, Int.le_sub_one_of_lt u⟩
  · exact Int.bmod_eq_of_le (half ▸ h.1) (half' ▸ Int.lt_of_le_sub_one h.2)

/-- `saturate` is the clamp to `[MIN, MAX]`. -/
theorem saturate_eq_clamp (k : ℕ) (w : ℤ) : saturate k w = clamp k w := by
  unfold saturate clamp
  split
  · next h => rw [min_eq_left h.le, max_eq_right (minOf_le_maxOf k)]
  · split
    · next h₁ h₂ =>
      rw [min_eq_right (h₂.le.trans (minOf_le_maxOf k)), max_eq_left h₂.le]
    · next h₁ h₂ =>
      rw [(wrap_eq_self_iff k w).2 ⟨le_of_not_gt h₂, le_of_not_gt h₁⟩,
        min_eq_right (le_of_not_gt h₁), max_eq_right (le_of_not_gt h₂)]

end Fulcrum

end
