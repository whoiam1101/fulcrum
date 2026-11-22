module

public import Fulcrum.Round

/-!
# L3: `kernel::kN::mul`

`mul(a, b)` of the kernel of every width, as Aeneas extracts it, never fails
and is `round(a · b / 2^F)`, to nearest with ties toward `+∞`, of the exact
product of the raw operands. `k8`..`k32` add `HALF = 2^(F-1)` and shift
(`add_half_shape`); `k64` takes the floor and the first dropped bit, the form
of `shr_round`.
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace Fulcrum

/-- The product of two raw values of `B` is at most `2^(BITS-1) · 2^(BITS-1)`
in magnitude. -/
theorem prod_abs_le {B} (a b : IScalar B) :
    |a.val * b.val| ≤ 2 ^ (B.numBits - 1) * 2 ^ (B.numBits - 1) := by
  rw [abs_mul]
  exact mul_le_mul (abs_le.mpr ⟨a.hmin, a.hmax.le⟩) (abs_le.mpr ⟨b.hmin, b.hmax.le⟩)
    (abs_nonneg _) (pow_pos zero_lt_two _).le

/-- `(p + h) >> sh` with `h = 2^k` and `sh = k + 1` rounds `p / 2^(k+1)` to
nearest, ties toward `+∞`, when the sum fits. -/
theorem add_half_shape {W} (p h : IScalar W) (sh : IScalar .I32) (k : ℕ) (hh : h.val = 2 ^ k)
    (hs : sh.val = ((k + 1 : ℕ) : ℤ)) (hk : k + 1 < W.numBits) (hfit : p.val + 2 ^ k ≤ IScalar.max W) :
    (do let i1 ← p + h; i1 >>> sh) ⦃ r => r.val = roundHalfUp (exact (k + 1) p.val) ⦄ := by
  have lo : IScalar.min W ≤ p.val + h.val :=
    hh ▸ (IScalar.min_def W ▸ p.hmin).trans (le_add_of_nonneg_right (pow_pos zero_lt_two k).le)
  refine WP.spec_bind (IScalar.add_spec lo (hh ▸ hfit)) fun i1 hi1 => ?_
  refine WP.spec_mono (IScalar.ShiftRight_IScalar_spec i1 sh (hs ▸ Int.natCast_nonneg _)
    (hs ▸ Int.ofNat_lt.mpr hk)) fun r ⟨hr, _⟩ => ?_
  rw [hr, IScalar.toNat, hs, hi1, hh, Int.toNat_natCast, add_half_shr]

/-- `kernel::k8::HALF` is `2^3`. -/
theorem k8_half_spec : fulcrum.kernel.k8.HALF ⦃ h => h.val = 2 ^ 3 ⦄ := by
  unfold fulcrum.kernel.k8.HALF
  refine WP.spec_bind (IScalar.sub_spec (x := 4#i32) (y := 1#i32)
    (by rw [IScalar.min_IScalarTy_I32_eq, I32.min_eq]; decide)
    (by rw [IScalar.max_IScalarTy_I32_eq, I32.max_eq]; decide)) fun i hi => ?_
  have hk : i.val = 3 := hi
  refine WP.spec_mono (IScalar.ShiftLeft_IScalar_spec 1#i16 i (by rw [hk]; decide)
    (by rw [hk]; decide)) fun h ⟨hv, _⟩ => ?_
  rw [hv, IScalar.toNat, hk]
  rfl

/-- `kernel::k8::round_frac` rounds `p / 2^4` when `p + 2^3` fits. -/
theorem k8_round_frac_spec (p : Std.I16) (hfit : p.val + 2 ^ 3 ≤ IScalar.max .I16) :
    fulcrum.kernel.k8.round_frac p ⦃ r => r.val = roundHalfUp (exact 4 p.val) ⦄ := by
  unfold fulcrum.kernel.k8.round_frac
  rw [ite_eq_right (by decide : ¬ core.num.I16.BITS = 128#u32)]
  exact WP.spec_bind k8_half_spec fun h hh => add_half_shape p h 4#i32 3 hh rfl (by decide) hfit

/-- L3 on the code: `kernel::k8::mul` is `round(a · b / 2^4)`. -/
theorem k8_mul_spec (a b : Std.I8) :
    fulcrum.kernel.k8.mul a b ⦃ r => r.val = roundHalfUp (exact 4 (a.val * b.val)) ⦄ := by
  unfold fulcrum.kernel.k8.mul
  rw [lift, bind_ok, lift, bind_ok]
  have ca : (IScalar.cast .I16 a).val = a.val := IScalar.val_mod_pow_greater_numBits _ _ (by decide)
  have cb : (IScalar.cast .I16 b).val = b.val := IScalar.val_mod_pow_greater_numBits _ _ (by decide)
  have ⟨lo, hi⟩ := abs_le.mp (show |a.val * b.val| ≤ 2 ^ 14 from prod_abs_le a b)
  refine WP.spec_bind (IScalar.mul_spec
    (by rw [ca, cb, IScalar.min_IScalarTy_I16_eq, I16.min_eq]; omega)
    (by rw [ca, cb, IScalar.max_IScalarTy_I16_eq, I16.max_eq]; omega)) fun p hp => ?_
  rw [ca, cb] at hp
  exact hp ▸ k8_round_frac_spec p (by rw [hp, IScalar.max_IScalarTy_I16_eq, I16.max_eq]; omega)

/-- `kernel::k16::HALF` is `2^7`. -/
theorem k16_half_spec : fulcrum.kernel.k16.HALF ⦃ h => h.val = 2 ^ 7 ⦄ := by
  unfold fulcrum.kernel.k16.HALF
  refine WP.spec_bind (IScalar.sub_spec (x := 8#i32) (y := 1#i32)
    (by rw [IScalar.min_IScalarTy_I32_eq, I32.min_eq]; decide)
    (by rw [IScalar.max_IScalarTy_I32_eq, I32.max_eq]; decide)) fun i hi => ?_
  have hk : i.val = 7 := hi
  refine WP.spec_mono (IScalar.ShiftLeft_IScalar_spec 1#i32 i (by rw [hk]; decide)
    (by rw [hk]; decide)) fun h ⟨hv, _⟩ => ?_
  rw [hv, IScalar.toNat, hk]
  rfl

/-- `kernel::k16::round_frac` rounds `p / 2^8` when `p + 2^7` fits. -/
theorem k16_round_frac_spec (p : Std.I32) (hfit : p.val + 2 ^ 7 ≤ IScalar.max .I32) :
    fulcrum.kernel.k16.round_frac p ⦃ r => r.val = roundHalfUp (exact 8 p.val) ⦄ := by
  unfold fulcrum.kernel.k16.round_frac
  rw [ite_eq_right (by decide : ¬ core.num.I32.BITS = 128#u32)]
  exact WP.spec_bind k16_half_spec fun h hh => add_half_shape p h 8#i32 7 hh rfl (by decide) hfit

/-- L3 on the code: `kernel::k16::mul` is `round(a · b / 2^8)`. -/
theorem k16_mul_spec (a b : Std.I16) :
    fulcrum.kernel.k16.mul a b ⦃ r => r.val = roundHalfUp (exact 8 (a.val * b.val)) ⦄ := by
  unfold fulcrum.kernel.k16.mul
  rw [lift, bind_ok, lift, bind_ok]
  have ca : (IScalar.cast .I32 a).val = a.val := IScalar.val_mod_pow_greater_numBits _ _ (by decide)
  have cb : (IScalar.cast .I32 b).val = b.val := IScalar.val_mod_pow_greater_numBits _ _ (by decide)
  have ⟨lo, hi⟩ := abs_le.mp (show |a.val * b.val| ≤ 2 ^ 30 from prod_abs_le a b)
  refine WP.spec_bind (IScalar.mul_spec
    (by rw [ca, cb, IScalar.min_IScalarTy_I32_eq, I32.min_eq]; omega)
    (by rw [ca, cb, IScalar.max_IScalarTy_I32_eq, I32.max_eq]; omega)) fun p hp => ?_
  rw [ca, cb] at hp
  exact hp ▸ k16_round_frac_spec p (by rw [hp, IScalar.max_IScalarTy_I32_eq, I32.max_eq]; omega)

/-- `kernel::k32::HALF` is `2^15`. -/
theorem k32_half_spec : fulcrum.kernel.k32.HALF ⦃ h => h.val = 2 ^ 15 ⦄ := by
  unfold fulcrum.kernel.k32.HALF
  refine WP.spec_bind (IScalar.sub_spec (x := 16#i32) (y := 1#i32)
    (by rw [IScalar.min_IScalarTy_I32_eq, I32.min_eq]; decide)
    (by rw [IScalar.max_IScalarTy_I32_eq, I32.max_eq]; decide)) fun i hi => ?_
  have hk : i.val = 15 := hi
  refine WP.spec_mono (IScalar.ShiftLeft_IScalar_spec 1#i64 i (by rw [hk]; decide)
    (by rw [hk]; decide)) fun h ⟨hv, _⟩ => ?_
  rw [hv, IScalar.toNat, hk]
  rfl

/-- `kernel::k32::round_frac` rounds `p / 2^16` when `p + 2^15` fits. -/
theorem k32_round_frac_spec (p : Std.I64) (hfit : p.val + 2 ^ 15 ≤ IScalar.max .I64) :
    fulcrum.kernel.k32.round_frac p ⦃ r => r.val = roundHalfUp (exact 16 p.val) ⦄ := by
  unfold fulcrum.kernel.k32.round_frac
  rw [ite_eq_right (by decide : ¬ core.num.I64.BITS = 128#u32)]
  exact WP.spec_bind k32_half_spec fun h hh => add_half_shape p h 16#i32 15 hh rfl (by decide) hfit

/-- L3 on the code: `kernel::k32::mul` is `round(a · b / 2^16)`. -/
theorem k32_mul_spec (a b : Std.I32) :
    fulcrum.kernel.k32.mul a b ⦃ r => r.val = roundHalfUp (exact 16 (a.val * b.val)) ⦄ := by
  unfold fulcrum.kernel.k32.mul
  rw [lift, bind_ok, lift, bind_ok]
  have ca : (IScalar.cast .I64 a).val = a.val := IScalar.val_mod_pow_greater_numBits _ _ (by decide)
  have cb : (IScalar.cast .I64 b).val = b.val := IScalar.val_mod_pow_greater_numBits _ _ (by decide)
  have ⟨lo, hi⟩ := abs_le.mp (show |a.val * b.val| ≤ 2 ^ 62 from prod_abs_le a b)
  refine WP.spec_bind (IScalar.mul_spec
    (by rw [ca, cb, IScalar.min_IScalarTy_I64_eq, I64.min_eq]; omega)
    (by rw [ca, cb, IScalar.max_IScalarTy_I64_eq, I64.max_eq]; omega)) fun p hp => ?_
  rw [ca, cb] at hp
  exact hp ▸ k32_round_frac_spec p (by rw [hp, IScalar.max_IScalarTy_I64_eq, I64.max_eq]; omega)

/-- `kernel::k64::round_frac` is `shr_round(p, 32)` for every `i128`: the floor
and the first dropped bit. -/
theorem k64_round_frac_spec (p : Std.I128) :
    fulcrum.kernel.k64.round_frac p ⦃ r => r.val = roundHalfUp (exact 32 p.val) ⦄ := by
  unfold fulcrum.kernel.k64.round_frac
  rw [ite_eq_left (by decide : core.num.I128.BITS = 128#u32)]
  refine WP.spec_bind (IScalar.ShiftRight_IScalar_spec p 32#i32 (by decide) (by decide))
    fun i ⟨hi, _⟩ => ?_
  refine WP.spec_bind (IScalar.sub_spec (x := 32#i32) (y := 1#i32)
    (by rw [IScalar.min_IScalarTy_I32_eq, I32.min_eq]; decide)
    (by rw [IScalar.max_IScalarTy_I32_eq, I32.max_eq]; decide)) fun i1 hi1 => ?_
  have h31 : i1.val = 31 := hi1
  refine WP.spec_bind (IScalar.ShiftRight_IScalar_spec p i1 (by rw [h31]; decide)
    (by rw [h31]; decide)) fun i2 ⟨hi2, _⟩ => ?_
  rw [lift, bind_ok]
  have t32 : (32#i32 : Std.I32).toNat = 32 := rfl
  have pos : (0 : ℤ) < 2 ^ 32 := pow_pos zero_lt_two _
  have lo : -2 ^ 95 ≤ i.val := by
    rw [hi, t32, shr_eq_div, Int.le_ediv_iff_mul_le pos]
    exact p.hmin
  have up : i.val < 2 ^ 95 := by
    rw [hi, t32, shr_eq_div, Int.ediv_lt_iff_lt_mul pos]
    exact p.hmax
  have bit := and_one_val i2
  have b0 : 0 ≤ i2.val % 2 := Int.emod_nonneg _ two_ne_zero
  have b1 : i2.val % 2 < 2 := Int.emod_lt_of_pos _ zero_lt_two
  refine WP.spec_mono (I128.add_spec (by rw [bit, I128.min_eq]; omega)
    (by rw [bit, I128.max_eq]; omega)) fun r hr => ?_
  rw [hr, bit, hi, hi2, t32, IScalar.toNat, h31, ← shrRound_eq]
  rfl

/-- L3 on the code: `kernel::k64::mul` is `round(a · b / 2^32)`. -/
theorem k64_mul_spec (a b : Std.I64) :
    fulcrum.kernel.k64.mul a b ⦃ r => r.val = roundHalfUp (exact 32 (a.val * b.val)) ⦄ := by
  unfold fulcrum.kernel.k64.mul
  rw [lift, bind_ok, lift, bind_ok]
  have ca : (IScalar.cast .I128 a).val = a.val := IScalar.val_mod_pow_greater_numBits _ _ (by decide)
  have cb : (IScalar.cast .I128 b).val = b.val := IScalar.val_mod_pow_greater_numBits _ _ (by decide)
  have ⟨lo, hi⟩ := abs_le.mp (show |a.val * b.val| ≤ 2 ^ 126 from prod_abs_le a b)
  refine WP.spec_bind (IScalar.mul_spec
    (by rw [ca, cb, IScalar.min_IScalarTy_I128_eq, I128.min_eq]; omega)
    (by rw [ca, cb, IScalar.max_IScalarTy_I128_eq, I128.max_eq]; omega)) fun p hp => ?_
  rw [ca, cb] at hp
  exact hp ▸ k64_round_frac_spec p

end Fulcrum

end
