module

public import Fulcrum.Math.Range
public import Fulcrum.Lemmas.Scalar

/-!
# L2: `kernel::to_int` and `from_parts`

On the code extracted by Aeneas, for `k8`..`k64`: `to_int` is the floor of
`w / 2^F` wrapped to the storage type, so the integer itself whenever it fits;
`from_parts` never fails and is `int · 2^F + frac`. Every width goes through
`to_int_shape` and `from_parts_shape`.
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace Fulcrum

/-- The body of `kernel::kN::to_int`: a right shift by `F`, then the cast to
the storage type of `k + 1` bits. -/
theorem to_int_shape {B W} (w : IScalar W) (sh : Std.I32) (k f : ℕ) (hs : sh.val = f)
    (hf : f < W.numBits) (hc : ∀ x : IScalar W, (IScalar.cast B x).val = wrap k x.val) :
    (do let i ← w >>> sh; ok (IScalar.cast B i)) ⦃ r => r.val = wrap k (w.val / 2 ^ f) ⦄ :=
  WP.spec_bind (IScalar.ShiftRight_IScalar_spec w sh (hs ▸ Int.natCast_nonneg f)
    (hs ▸ Int.ofNat_lt.mpr hf)) fun i ⟨hi, _⟩ => by
    rw [WP.spec_ok, hc, hi, IScalar.toNat, hs, Int.toNat_natCast, shr_eq_div]

/-- The body of `kernel::kN::from_parts`: an integer part of `s + 1` bits
shifted left by `F` plus a fractional part of `u` bits, on a wide type of
`m + 2` bits with `s + F ≤ m` and `u ≤ m`, never overflows. -/
theorem from_parts_shape {S U W} (int : IScalar S) (frac : UScalar U) (sh : Std.I32)
    (s f u m : ℕ) (hS : S.numBits = s + 1) (hU : U.numBits = u) (hW : W.numBits = m + 1 + 1)
    (hs : sh.val = f) (hsf : s + f ≤ m) (hu : u ≤ m) :
    (do
        let i ← lift (IScalar.cast W int)
        let i1 ← i <<< sh
        let i2 ← lift (UScalar.hcast W frac)
        i1 + i2)
      ⦃ r => r.val = int.val * 2 ^ f + frac.val ⦄ := by
  have sm : s ≤ m := (Nat.le_add_right s f).trans hsf
  have fm : f ≤ m := (Nat.le_add_left f s).trans hsf
  have ci := IScalar.val_mod_pow_greater_numBits W int
    (hS ▸ hW ▸ Nat.succ_le_succ (Nat.le_succ_of_le sm))
  have ⟨il, iu⟩ := val_bounds int hS
  have pf : (0 : ℤ) < 2 ^ f := pow_pos zero_lt_two f
  have hp : |int.val * 2 ^ f| ≤ 2 ^ m := by
    rw [abs_mul, abs_of_pos pf]
    exact (mul_le_mul_of_nonneg_right (abs_le.mpr ⟨il, iu.le⟩) pf.le).trans
      ((pow_add (2 : ℤ) s f).symm.trans_le (pow_le_pow_right₀ one_le_two hsf))
  have ⟨pl, pu⟩ := abs_le.mp hp
  have fu : (frac.val : ℤ) < 2 ^ m := (Int.ofNat_lt.mpr frac.bv.isLt).trans_le (by
    rw [hU]; exact_mod_cast Nat.pow_le_pow_right two_pos hu)
  have f0 : (0 : ℤ) ≤ frac.val := Int.natCast_nonneg _
  have e : (2 : ℕ) ^ W.numBits = 2 ^ (m + 1 + 1) := by rw [hW]
  have pm1 : (2 : ℤ) ^ (m + 1) = 2 ^ m * 2 := pow_succ 2 m
  rw [lift, bind_ok]
  refine WP.spec_bind (IScalar.ShiftLeft_IScalar_spec _ sh (hs ▸ Int.natCast_nonneg f)
    (hs ▸ Int.ofNat_lt.mpr (hW ▸ Nat.lt_succ_of_lt (Nat.lt_succ_of_le fm))))
    fun i1 ⟨hi1, _⟩ => ?_
  rw [IScalar.toNat, hs, Int.toNat_natCast, Int.shiftLeft_eq, ci, e] at hi1
  have e1 : int.val * 2 ^ f = i1.val := by
    rw [hi1]
    exact ((wrap_eq_self_iff (m + 1) _).2 ⟨by unfold minOf; omega, by unfold maxOf; omega⟩).symm
  have e2 : (UScalar.hcast W frac).val = frac.val := by
    rw [UScalar.hcast_val_eq, e]
    exact (wrap_eq_self_iff (m + 1) _).2 ⟨by unfold minOf; omega, by unfold maxOf; omega⟩
  rw [lift, bind_ok]
  refine WP.spec_mono (IScalar.add_spec (x := i1) (y := UScalar.hcast W frac)
    (by rw [min_eq_neg_pow hW, e2, ← e1]; omega) (by rw [max_eq_pow_sub_one hW, e2, ← e1]; omega))
    fun r hr => ?_
  rw [hr, e2, e1]

/-- L2 on the code: `kernel::k8::to_int` is `⌊w / 2^4⌋` wrapped to 8 bits. -/
theorem k8_to_int_spec (w : Std.I16) :
    fulcrum.kernel.k8.to_int w ⦃ r => r.val = wrap 7 (w.val / 2 ^ 4) ⦄ :=
  to_int_shape w 4#i32 7 4 rfl (Nat.le_of_ble_eq_true rfl) fun x => IScalar.cast_val_eq _ x

/-- L2 on the code: `kernel::k8::from_parts` is `int · 2^4 + frac`. -/
theorem k8_from_parts_spec (int : Std.I8) (frac : Std.U8) :
    fulcrum.kernel.k8.from_parts int frac ⦃ r => r.val = int.val * 2 ^ 4 + frac.val ⦄ := by
  unfold fulcrum.kernel.k8.from_parts
  exact from_parts_shape int frac 4#i32 7 4 8 14 rfl rfl rfl rfl
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)

/-- L2 on the code: `kernel::k16::to_int` is `⌊w / 2^8⌋` wrapped to 16 bits. -/
theorem k16_to_int_spec (w : Std.I32) :
    fulcrum.kernel.k16.to_int w ⦃ r => r.val = wrap 15 (w.val / 2 ^ 8) ⦄ :=
  to_int_shape w 8#i32 15 8 rfl (Nat.le_of_ble_eq_true rfl) fun x => IScalar.cast_val_eq _ x

/-- L2 on the code: `kernel::k16::from_parts` is `int · 2^8 + frac`. -/
theorem k16_from_parts_spec (int : Std.I8) (frac : Std.U8) :
    fulcrum.kernel.k16.from_parts int frac ⦃ r => r.val = int.val * 2 ^ 8 + frac.val ⦄ := by
  unfold fulcrum.kernel.k16.from_parts
  exact from_parts_shape int frac 8#i32 7 8 8 30 rfl rfl rfl rfl
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)

/-- L2 on the code: `kernel::k32::to_int` is `⌊w / 2^16⌋` wrapped to 32 bits. -/
theorem k32_to_int_spec (w : Std.I64) :
    fulcrum.kernel.k32.to_int w ⦃ r => r.val = wrap 31 (w.val / 2 ^ 16) ⦄ :=
  to_int_shape w 16#i32 31 16 rfl (Nat.le_of_ble_eq_true rfl) fun x => IScalar.cast_val_eq _ x

/-- L2 on the code: `kernel::k32::from_parts` is `int · 2^16 + frac`. -/
theorem k32_from_parts_spec (int : Std.I16) (frac : Std.U16) :
    fulcrum.kernel.k32.from_parts int frac ⦃ r => r.val = int.val * 2 ^ 16 + frac.val ⦄ := by
  unfold fulcrum.kernel.k32.from_parts
  exact from_parts_shape int frac 16#i32 15 16 16 62 rfl rfl rfl rfl
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)

/-- L2 on the code: `kernel::k64::to_int` is `⌊w / 2^32⌋` wrapped to 64 bits. -/
theorem k64_to_int_spec (w : Std.I128) :
    fulcrum.kernel.k64.to_int w ⦃ r => r.val = wrap 63 (w.val / 2 ^ 32) ⦄ :=
  to_int_shape w 32#i32 63 32 rfl (Nat.le_of_ble_eq_true rfl) fun x => IScalar.cast_val_eq _ x

/-- L2 on the code: `kernel::k64::from_parts` is `int · 2^32 + frac`. -/
theorem k64_from_parts_spec (int : Std.I32) (frac : Std.U32) :
    fulcrum.kernel.k64.from_parts int frac ⦃ r => r.val = int.val * 2 ^ 32 + frac.val ⦄ := by
  unfold fulcrum.kernel.k64.from_parts
  exact from_parts_shape int frac 32#i32 31 32 32 126 rfl rfl rfl rfl
    (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)

end Fulcrum

end
