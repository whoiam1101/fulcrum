module

public import Fulcrum.Round
public import Fulcrum.Kernel.Funs

/-!
# L2: range checks of `kernel::fits`, `narrow` and `saturate`

For every width `k + 1`: the high bits `w >>> k` are all zeros or all ones
exactly when `w` is in `[MIN, MAX]`, and the cast to the storage type, two's
complement wrapping `Int.bmod w (2^(k+1))`, keeps `w` exactly then. On the
code extracted by Aeneas, for `k8`..`k64`: `fits` is the comparison with
`[MIN, MAX]`, `narrow` returns `w` exactly when it fits, `saturate` is the
clamp.
-/

@[expose] public section

open Aeneas Aeneas.Std Result

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

/-- The body of `kernel::kN::fits` once its first `lift` is taken: `true`
exactly when `w` is in `[lo, hi]`. -/
theorem fits_shape {W} (w lo hi : IScalar W) (k : ℕ) (hlo : lo.val = minOf k)
    (hhi : hi.val = maxOf k) :
    (if w ≥ lo then do let i1 ← lift hi; ok (decide (w ≤ i1)) else ok false)
      ⦃ b => b = decide (InRange k w.val) ⦄ := by
  by_cases h : w ≥ lo
  · rw [ite_eq_left h, lift, bind_ok, WP.spec_ok]
    exact decide_eq_decide.mpr
      ⟨fun u => ⟨hlo ▸ h, hhi ▸ u⟩, fun u => show w.val ≤ hi.val from hhi ▸ u.2⟩
  · rw [ite_eq_right h, WP.spec_ok]
    exact (decide_eq_false fun u => h (show lo.val ≤ w.val from hlo ▸ u.1)).symm

/-- The body of `kernel::kN::saturate` once its first `lift` is taken: the
clamp, given the cast to the storage type is `wrap`. -/
theorem saturate_shape {B W} (w lo hi : IScalar W) (mn mx : IScalar B) (k : ℕ)
    (hlo : lo.val = minOf k) (hhi : hi.val = maxOf k) (hmn : mn.val = minOf k)
    (hmx : mx.val = maxOf k) (hc : (IScalar.cast B w).val = wrap k w.val) :
    (if w > hi then ok mx else do
        let i1 ← lift lo
        if w < i1 then ok mn else ok (IScalar.cast B w))
      ⦃ r => r.val = clamp k w.val ⦄ := by
  rw [← saturate_eq_clamp]
  unfold saturate
  by_cases h₁ : w > hi
  · rw [ite_eq_left h₁, WP.spec_ok, hmx, ite_eq_left (hhi ▸ h₁)]
  rw [ite_eq_right h₁, ite_eq_right (hhi ▸ h₁), lift, bind_ok]
  by_cases h₂ : w < lo
  · rw [ite_eq_left h₂, WP.spec_ok, hmn, ite_eq_left (hlo ▸ h₂)]
  · rw [ite_eq_right h₂, WP.spec_ok, hc, ite_eq_right (hlo ▸ h₂)]

/-- The body of `kernel::kN::narrow`: the value when `fits` says it is in range,
`none` otherwise. -/
theorem narrow_shape {B W} (f : Result Bool) (w : IScalar W) (k : ℕ)
    (hf : f ⦃ b => b = decide (InRange k w.val) ⦄)
    (hc : (IScalar.cast B w).val = wrap k w.val) :
    (do let b ← f; if b then do let i ← lift (IScalar.cast B w); ok (some i) else ok none)
      ⦃ r => r.map IScalar.val = if InRange k w.val then some w.val else none ⦄ :=
  WP.spec_bind hf fun b hb => by
    by_cases h : InRange k w.val
    · rw [hb, decide_eq_true h, ite_eq_left rfl, lift, bind_ok, WP.spec_ok, ite_eq_left h,
        Option.map_some, hc, (wrap_eq_self_iff k w.val).2 h]
    · rw [hb, decide_eq_false h, ite_eq_right Bool.false_ne_true, WP.spec_ok, ite_eq_right h,
        Option.map_none]

/-- L2 on the code: `kernel::k8::fits` is the range check of 8 bits. -/
theorem k8_fits_spec (w : Std.I16) :
    fulcrum.kernel.k8.fits w ⦃ b => b = decide (InRange 7 w.val) ⦄ := by
  unfold fulcrum.kernel.k8.fits
  rw [lift, bind_ok]
  exact fits_shape w _ _ 7 rfl rfl

/-- L2 on the code: `kernel::k8::narrow` returns `w` exactly when it fits 8 bits. -/
theorem k8_narrow_spec (w : Std.I16) :
    fulcrum.kernel.k8.narrow w
      ⦃ r => r.map IScalar.val = if InRange 7 w.val then some w.val else none ⦄ :=
  narrow_shape _ w 7 (k8_fits_spec w) (IScalar.cast_val_eq _ _)

/-- L2 on the code: `kernel::k8::saturate` is the clamp to 8 bits. -/
theorem k8_saturate_spec (w : Std.I16) :
    fulcrum.kernel.k8.saturate w ⦃ r => r.val = clamp 7 w.val ⦄ := by
  unfold fulcrum.kernel.k8.saturate
  rw [lift, bind_ok]
  exact saturate_shape w _ _ _ _ 7 rfl rfl rfl rfl (IScalar.cast_val_eq _ _)

/-- L2 on the code: `kernel::k16::fits` is the range check of 16 bits. -/
theorem k16_fits_spec (w : Std.I32) :
    fulcrum.kernel.k16.fits w ⦃ b => b = decide (InRange 15 w.val) ⦄ := by
  unfold fulcrum.kernel.k16.fits
  rw [lift, bind_ok]
  exact fits_shape w _ _ 15 rfl rfl

/-- L2 on the code: `kernel::k16::narrow` returns `w` exactly when it fits 16 bits. -/
theorem k16_narrow_spec (w : Std.I32) :
    fulcrum.kernel.k16.narrow w
      ⦃ r => r.map IScalar.val = if InRange 15 w.val then some w.val else none ⦄ :=
  narrow_shape _ w 15 (k16_fits_spec w) (IScalar.cast_val_eq _ _)

/-- L2 on the code: `kernel::k16::saturate` is the clamp to 16 bits. -/
theorem k16_saturate_spec (w : Std.I32) :
    fulcrum.kernel.k16.saturate w ⦃ r => r.val = clamp 15 w.val ⦄ := by
  unfold fulcrum.kernel.k16.saturate
  rw [lift, bind_ok]
  exact saturate_shape w _ _ _ _ 15 rfl rfl rfl rfl (IScalar.cast_val_eq _ _)

/-- L2 on the code: `kernel::k32::fits` is the range check of 32 bits. -/
theorem k32_fits_spec (w : Std.I64) :
    fulcrum.kernel.k32.fits w ⦃ b => b = decide (InRange 31 w.val) ⦄ := by
  unfold fulcrum.kernel.k32.fits
  rw [lift, bind_ok]
  exact fits_shape w _ _ 31 rfl rfl

/-- L2 on the code: `kernel::k32::narrow` returns `w` exactly when it fits 32 bits. -/
theorem k32_narrow_spec (w : Std.I64) :
    fulcrum.kernel.k32.narrow w
      ⦃ r => r.map IScalar.val = if InRange 31 w.val then some w.val else none ⦄ :=
  narrow_shape _ w 31 (k32_fits_spec w) (IScalar.cast_val_eq _ _)

/-- L2 on the code: `kernel::k32::saturate` is the clamp to 32 bits. -/
theorem k32_saturate_spec (w : Std.I64) :
    fulcrum.kernel.k32.saturate w ⦃ r => r.val = clamp 31 w.val ⦄ := by
  unfold fulcrum.kernel.k32.saturate
  rw [lift, bind_ok]
  exact saturate_shape w _ _ _ _ 31 rfl rfl rfl rfl (IScalar.cast_val_eq _ _)

/-- L2 on the code: `kernel::k64::fits` is the range check of 64 bits. -/
theorem k64_fits_spec (w : Std.I128) :
    fulcrum.kernel.k64.fits w ⦃ b => b = decide (InRange 63 w.val) ⦄ := by
  unfold fulcrum.kernel.k64.fits
  rw [lift, bind_ok]
  exact fits_shape w _ _ 63 rfl rfl

/-- L2 on the code: `kernel::k64::narrow` returns `w` exactly when it fits 64 bits. -/
theorem k64_narrow_spec (w : Std.I128) :
    fulcrum.kernel.k64.narrow w
      ⦃ r => r.map IScalar.val = if InRange 63 w.val then some w.val else none ⦄ :=
  narrow_shape _ w 63 (k64_fits_spec w) (IScalar.cast_val_eq _ _)

/-- L2 on the code: `kernel::k64::saturate` is the clamp to 64 bits. -/
theorem k64_saturate_spec (w : Std.I128) :
    fulcrum.kernel.k64.saturate w ⦃ r => r.val = clamp 63 w.val ⦄ := by
  unfold fulcrum.kernel.k64.saturate
  rw [lift, bind_ok]
  exact saturate_shape w _ _ _ _ 63 rfl rfl rfl rfl (IScalar.cast_val_eq _ _)

end Fulcrum

end
