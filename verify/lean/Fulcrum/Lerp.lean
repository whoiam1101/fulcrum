module

public import Fulcrum.Mul

/-!
# L3: `kernel::kN::mul_add` and `kernel::kN::lerp`

`mul_add(a, b, c)` is `round((a · b + c · 2^F) / 2^F)`, the product plus a raw
value rounded once, and `lerp(a, b, t)` is `a + round((b - a) · t / 2^F)`, for
every width, as Aeneas extracts them: neither fails.
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace Fulcrum

/-- Adding an integer `c` to the exact value adds it to the rounded value. -/
theorem roundHalfUp_add_int (x c : ℤ) (n : ℕ) :
    roundHalfUp (exact n (x + c * 2 ^ n)) = roundHalfUp (exact n x) + c := by
  have e : exact n (x + c * 2 ^ n) + 1 / 2 = (exact n x + 1 / 2) + c := by
    rw [exact, exact, Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, add_div,
      mul_div_cancel_right₀ _ (pow_ne_zero n two_ne_zero), add_right_comm]
  rw [roundHalfUp, roundHalfUp, e, Int.floor_add_intCast]

/-- Bounds of the rounded value from bounds of the exact one. -/
theorem roundHalfUp_bounds (x L U : ℤ) (k : ℕ) (hl : L * 2 ^ (k + 1) ≤ x + 2 ^ k)
    (hu : x + 2 ^ k < U * 2 ^ (k + 1)) :
    L ≤ roundHalfUp (exact (k + 1) x) ∧ roundHalfUp (exact (k + 1) x) < U := by
  have pos : (0 : ℤ) < 2 ^ (k + 1) := pow_pos zero_lt_two _
  rw [← add_half_shr, shr_eq_div]
  exact ⟨(Int.le_ediv_iff_mul_le pos).2 hl, (Int.ediv_lt_iff_lt_mul pos).2 hu⟩

/-- The difference of two raw values of `B` times a third is below
`2^(BITS-1) · 2^BITS` in magnitude. -/
theorem diff_prod_abs_le {B} (a b t : IScalar B) :
    |(b.val - a.val) * t.val| ≤ (2 ^ B.numBits - 1) * 2 ^ (B.numBits - 1) := by
  have ha := a.hBounds
  have hb := b.hBounds
  have hn : 0 < B.numBits := Nat.pos_of_ne_zero (IScalarTy.numBits_nonzero B)
  have e : (2 : ℤ) ^ B.numBits = 2 ^ (B.numBits - 1) * 2 := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
  rw [abs_mul]
  exact mul_le_mul (abs_le.mpr ⟨by omega, by omega⟩) (abs_le.mpr ⟨t.hmin, t.hmax.le⟩)
    (abs_nonneg _) (sub_nonneg.mpr (one_le_pow₀ one_le_two))

/-- L3 on the code: `kernel::k8::mul_add` is `round((a · b + c · 2^4) / 2^4)`. -/
theorem k8_mul_add_spec (a b c : Std.I8) :
    fulcrum.kernel.k8.mul_add a b c
      ⦃ r => r.val = roundHalfUp (exact 4 (a.val * b.val + c.val * 2 ^ 4)) ⦄ := by
  unfold fulcrum.kernel.k8.mul_add
  refine WP.spec_bind (k8_mul_spec a b) fun m hm => ?_
  rw [lift, bind_ok]
  have cc : (IScalar.cast .I16 c).val = c.val := IScalar.val_mod_pow_greater_numBits _ _ (by decide)
  have ⟨lo, hi⟩ := abs_le.mp (show |a.val * b.val| ≤ 2 ^ 14 from prod_abs_le a b)
  have mb : -2 ^ 10 ≤ roundHalfUp (exact 4 (a.val * b.val)) ∧ roundHalfUp (exact 4 (a.val * b.val)) < 2 ^ 10 + 1 :=
    roundHalfUp_bounds (a.val * b.val) (-2 ^ 10) (2 ^ 10 + 1) 3
    (by omega) (by omega)
  have c0 : -2 ^ 7 ≤ c.val := c.hmin
  have c1 : c.val < 2 ^ 7 := c.hmax
  refine WP.spec_mono (IScalar.add_spec
    (by rw [hm, cc, IScalar.min_IScalarTy_I16_eq, I16.min_eq]; omega)
    (by rw [hm, cc, IScalar.max_IScalarTy_I16_eq, I16.max_eq]; omega)) fun r hr => ?_
  rw [hr, hm, cc, roundHalfUp_add_int]

/-- L3 on the code: `kernel::k8::lerp` is `a + round((b - a) · t / 2^4)`. -/
theorem k8_lerp_spec (a b t : Std.I8) :
    fulcrum.kernel.k8.lerp a b t
      ⦃ r => r.val = a.val + roundHalfUp (exact 4 ((b.val - a.val) * t.val)) ⦄ := by
  unfold fulcrum.kernel.k8.lerp
  rw [lift, bind_ok, lift, bind_ok, bind_ok]
  have ca : (IScalar.cast .I16 a).val = a.val := IScalar.val_mod_pow_greater_numBits _ _ (by decide)
  have cb : (IScalar.cast .I16 b).val = b.val := IScalar.val_mod_pow_greater_numBits _ _ (by decide)
  have ct : (IScalar.cast .I16 t).val = t.val := IScalar.val_mod_pow_greater_numBits _ _ (by decide)
  have a0 : -2 ^ 7 ≤ a.val := a.hmin
  have a1 : a.val < 2 ^ 7 := a.hmax
  have b0 : -2 ^ 7 ≤ b.val := b.hmin
  have b1 : b.val < 2 ^ 7 := b.hmax
  refine WP.spec_bind (IScalar.sub_spec
    (by rw [ca, cb, IScalar.min_IScalarTy_I16_eq, I16.min_eq]; omega)
    (by rw [ca, cb, IScalar.max_IScalarTy_I16_eq, I16.max_eq]; omega)) fun d hd => ?_
  rw [lift, bind_ok]
  have ⟨lo, hi⟩ := abs_le.mp (show |(b.val - a.val) * t.val| ≤ (2 ^ 8 - 1) * 2 ^ 7 from
    diff_prod_abs_le a b t)
  rw [ca, cb] at hd
  refine WP.spec_bind (IScalar.mul_spec
    (by rw [hd, ct, IScalar.min_IScalarTy_I16_eq, I16.min_eq]; omega)
    (by rw [hd, ct, IScalar.max_IScalarTy_I16_eq, I16.max_eq]; omega)) fun p hp => ?_
  rw [hd, ct] at hp
  refine WP.spec_bind (k8_round_frac_spec p (by rw [hp, IScalar.max_IScalarTy_I16_eq, I16.max_eq]; omega)) fun q hq => ?_
  have qb : -2 ^ 11 ≤ roundHalfUp (exact 4 ((b.val - a.val) * t.val)) ∧ roundHalfUp (exact 4 ((b.val - a.val) * t.val)) < 2 ^ 11 :=
    roundHalfUp_bounds ((b.val - a.val) * t.val) (-2 ^ 11) (2 ^ 11) 3 (by omega) (by omega)
  refine WP.spec_mono (IScalar.add_spec
    (by rw [ca, hq, hp, IScalar.min_IScalarTy_I16_eq, I16.min_eq]; omega)
    (by rw [ca, hq, hp, IScalar.max_IScalarTy_I16_eq, I16.max_eq]; omega)) fun r hr => ?_
  rw [hr, ca, hq, hp]

/-- L3 on the code: `kernel::k16::mul_add` is `round((a · b + c · 2^8) / 2^8)`. -/
theorem k16_mul_add_spec (a b c : Std.I16) :
    fulcrum.kernel.k16.mul_add a b c
      ⦃ r => r.val = roundHalfUp (exact 8 (a.val * b.val + c.val * 2 ^ 8)) ⦄ := by
  unfold fulcrum.kernel.k16.mul_add
  refine WP.spec_bind (k16_mul_spec a b) fun m hm => ?_
  rw [lift, bind_ok]
  have cc : (IScalar.cast .I32 c).val = c.val := IScalar.val_mod_pow_greater_numBits _ _ (by decide)
  have ⟨lo, hi⟩ := abs_le.mp (show |a.val * b.val| ≤ 2 ^ 30 from prod_abs_le a b)
  have mb : -2 ^ 22 ≤ roundHalfUp (exact 8 (a.val * b.val)) ∧ roundHalfUp (exact 8 (a.val * b.val)) < 2 ^ 22 + 1 :=
    roundHalfUp_bounds (a.val * b.val) (-2 ^ 22) (2 ^ 22 + 1) 7
    (by omega) (by omega)
  have c0 : -2 ^ 15 ≤ c.val := c.hmin
  have c1 : c.val < 2 ^ 15 := c.hmax
  refine WP.spec_mono (IScalar.add_spec
    (by rw [hm, cc, IScalar.min_IScalarTy_I32_eq, I32.min_eq]; omega)
    (by rw [hm, cc, IScalar.max_IScalarTy_I32_eq, I32.max_eq]; omega)) fun r hr => ?_
  rw [hr, hm, cc, roundHalfUp_add_int]

/-- L3 on the code: `kernel::k16::lerp` is `a + round((b - a) · t / 2^8)`. -/
theorem k16_lerp_spec (a b t : Std.I16) :
    fulcrum.kernel.k16.lerp a b t
      ⦃ r => r.val = a.val + roundHalfUp (exact 8 ((b.val - a.val) * t.val)) ⦄ := by
  unfold fulcrum.kernel.k16.lerp
  rw [lift, bind_ok, lift, bind_ok, bind_ok]
  have ca : (IScalar.cast .I32 a).val = a.val := IScalar.val_mod_pow_greater_numBits _ _ (by decide)
  have cb : (IScalar.cast .I32 b).val = b.val := IScalar.val_mod_pow_greater_numBits _ _ (by decide)
  have ct : (IScalar.cast .I32 t).val = t.val := IScalar.val_mod_pow_greater_numBits _ _ (by decide)
  have a0 : -2 ^ 15 ≤ a.val := a.hmin
  have a1 : a.val < 2 ^ 15 := a.hmax
  have b0 : -2 ^ 15 ≤ b.val := b.hmin
  have b1 : b.val < 2 ^ 15 := b.hmax
  refine WP.spec_bind (IScalar.sub_spec
    (by rw [ca, cb, IScalar.min_IScalarTy_I32_eq, I32.min_eq]; omega)
    (by rw [ca, cb, IScalar.max_IScalarTy_I32_eq, I32.max_eq]; omega)) fun d hd => ?_
  rw [lift, bind_ok]
  have ⟨lo, hi⟩ := abs_le.mp (show |(b.val - a.val) * t.val| ≤ (2 ^ 16 - 1) * 2 ^ 15 from
    diff_prod_abs_le a b t)
  rw [ca, cb] at hd
  refine WP.spec_bind (IScalar.mul_spec
    (by rw [hd, ct, IScalar.min_IScalarTy_I32_eq, I32.min_eq]; omega)
    (by rw [hd, ct, IScalar.max_IScalarTy_I32_eq, I32.max_eq]; omega)) fun p hp => ?_
  rw [hd, ct] at hp
  refine WP.spec_bind (k16_round_frac_spec p (by rw [hp, IScalar.max_IScalarTy_I32_eq, I32.max_eq]; omega)) fun q hq => ?_
  have qb : -2 ^ 23 ≤ roundHalfUp (exact 8 ((b.val - a.val) * t.val)) ∧ roundHalfUp (exact 8 ((b.val - a.val) * t.val)) < 2 ^ 23 :=
    roundHalfUp_bounds ((b.val - a.val) * t.val) (-2 ^ 23) (2 ^ 23) 7 (by omega) (by omega)
  refine WP.spec_mono (IScalar.add_spec
    (by rw [ca, hq, hp, IScalar.min_IScalarTy_I32_eq, I32.min_eq]; omega)
    (by rw [ca, hq, hp, IScalar.max_IScalarTy_I32_eq, I32.max_eq]; omega)) fun r hr => ?_
  rw [hr, ca, hq, hp]

/-- L3 on the code: `kernel::k32::mul_add` is `round((a · b + c · 2^16) / 2^16)`. -/
theorem k32_mul_add_spec (a b c : Std.I32) :
    fulcrum.kernel.k32.mul_add a b c
      ⦃ r => r.val = roundHalfUp (exact 16 (a.val * b.val + c.val * 2 ^ 16)) ⦄ := by
  unfold fulcrum.kernel.k32.mul_add
  refine WP.spec_bind (k32_mul_spec a b) fun m hm => ?_
  rw [lift, bind_ok]
  have cc : (IScalar.cast .I64 c).val = c.val := IScalar.val_mod_pow_greater_numBits _ _ (by decide)
  have ⟨lo, hi⟩ := abs_le.mp (show |a.val * b.val| ≤ 2 ^ 62 from prod_abs_le a b)
  have mb : -2 ^ 46 ≤ roundHalfUp (exact 16 (a.val * b.val)) ∧ roundHalfUp (exact 16 (a.val * b.val)) < 2 ^ 46 + 1 :=
    roundHalfUp_bounds (a.val * b.val) (-2 ^ 46) (2 ^ 46 + 1) 15
    (by omega) (by omega)
  have c0 : -2 ^ 31 ≤ c.val := c.hmin
  have c1 : c.val < 2 ^ 31 := c.hmax
  refine WP.spec_mono (IScalar.add_spec
    (by rw [hm, cc, IScalar.min_IScalarTy_I64_eq, I64.min_eq]; omega)
    (by rw [hm, cc, IScalar.max_IScalarTy_I64_eq, I64.max_eq]; omega)) fun r hr => ?_
  rw [hr, hm, cc, roundHalfUp_add_int]

/-- L3 on the code: `kernel::k32::lerp` is `a + round((b - a) · t / 2^16)`. -/
theorem k32_lerp_spec (a b t : Std.I32) :
    fulcrum.kernel.k32.lerp a b t
      ⦃ r => r.val = a.val + roundHalfUp (exact 16 ((b.val - a.val) * t.val)) ⦄ := by
  unfold fulcrum.kernel.k32.lerp
  rw [lift, bind_ok, lift, bind_ok, bind_ok]
  have ca : (IScalar.cast .I64 a).val = a.val := IScalar.val_mod_pow_greater_numBits _ _ (by decide)
  have cb : (IScalar.cast .I64 b).val = b.val := IScalar.val_mod_pow_greater_numBits _ _ (by decide)
  have ct : (IScalar.cast .I64 t).val = t.val := IScalar.val_mod_pow_greater_numBits _ _ (by decide)
  have a0 : -2 ^ 31 ≤ a.val := a.hmin
  have a1 : a.val < 2 ^ 31 := a.hmax
  have b0 : -2 ^ 31 ≤ b.val := b.hmin
  have b1 : b.val < 2 ^ 31 := b.hmax
  refine WP.spec_bind (IScalar.sub_spec
    (by rw [ca, cb, IScalar.min_IScalarTy_I64_eq, I64.min_eq]; omega)
    (by rw [ca, cb, IScalar.max_IScalarTy_I64_eq, I64.max_eq]; omega)) fun d hd => ?_
  rw [lift, bind_ok]
  have ⟨lo, hi⟩ := abs_le.mp (show |(b.val - a.val) * t.val| ≤ (2 ^ 32 - 1) * 2 ^ 31 from
    diff_prod_abs_le a b t)
  rw [ca, cb] at hd
  refine WP.spec_bind (IScalar.mul_spec
    (by rw [hd, ct, IScalar.min_IScalarTy_I64_eq, I64.min_eq]; omega)
    (by rw [hd, ct, IScalar.max_IScalarTy_I64_eq, I64.max_eq]; omega)) fun p hp => ?_
  rw [hd, ct] at hp
  refine WP.spec_bind (k32_round_frac_spec p (by rw [hp, IScalar.max_IScalarTy_I64_eq, I64.max_eq]; omega)) fun q hq => ?_
  have qb : -2 ^ 47 ≤ roundHalfUp (exact 16 ((b.val - a.val) * t.val)) ∧ roundHalfUp (exact 16 ((b.val - a.val) * t.val)) < 2 ^ 47 :=
    roundHalfUp_bounds ((b.val - a.val) * t.val) (-2 ^ 47) (2 ^ 47) 15 (by omega) (by omega)
  refine WP.spec_mono (IScalar.add_spec
    (by rw [ca, hq, hp, IScalar.min_IScalarTy_I64_eq, I64.min_eq]; omega)
    (by rw [ca, hq, hp, IScalar.max_IScalarTy_I64_eq, I64.max_eq]; omega)) fun r hr => ?_
  rw [hr, ca, hq, hp]

/-- L3 on the code: `kernel::k64::mul_add` is `round((a · b + c · 2^32) / 2^32)`. -/
theorem k64_mul_add_spec (a b c : Std.I64) :
    fulcrum.kernel.k64.mul_add a b c
      ⦃ r => r.val = roundHalfUp (exact 32 (a.val * b.val + c.val * 2 ^ 32)) ⦄ := by
  unfold fulcrum.kernel.k64.mul_add
  refine WP.spec_bind (k64_mul_spec a b) fun m hm => ?_
  rw [lift, bind_ok]
  have cc : (IScalar.cast .I128 c).val = c.val := IScalar.val_mod_pow_greater_numBits _ _ (by decide)
  have ⟨lo, hi⟩ := abs_le.mp (show |a.val * b.val| ≤ 2 ^ 126 from prod_abs_le a b)
  have mb : -2 ^ 94 ≤ roundHalfUp (exact 32 (a.val * b.val)) ∧ roundHalfUp (exact 32 (a.val * b.val)) < 2 ^ 94 + 1 :=
    roundHalfUp_bounds (a.val * b.val) (-2 ^ 94) (2 ^ 94 + 1) 31
    (by omega) (by omega)
  have c0 : -2 ^ 63 ≤ c.val := c.hmin
  have c1 : c.val < 2 ^ 63 := c.hmax
  refine WP.spec_mono (IScalar.add_spec
    (by rw [hm, cc, IScalar.min_IScalarTy_I128_eq, I128.min_eq]; omega)
    (by rw [hm, cc, IScalar.max_IScalarTy_I128_eq, I128.max_eq]; omega)) fun r hr => ?_
  rw [hr, hm, cc, roundHalfUp_add_int]

/-- L3 on the code: `kernel::k64::lerp` is `a + round((b - a) · t / 2^32)`. -/
theorem k64_lerp_spec (a b t : Std.I64) :
    fulcrum.kernel.k64.lerp a b t
      ⦃ r => r.val = a.val + roundHalfUp (exact 32 ((b.val - a.val) * t.val)) ⦄ := by
  unfold fulcrum.kernel.k64.lerp
  rw [lift, bind_ok, lift, bind_ok, bind_ok]
  have ca : (IScalar.cast .I128 a).val = a.val := IScalar.val_mod_pow_greater_numBits _ _ (by decide)
  have cb : (IScalar.cast .I128 b).val = b.val := IScalar.val_mod_pow_greater_numBits _ _ (by decide)
  have ct : (IScalar.cast .I128 t).val = t.val := IScalar.val_mod_pow_greater_numBits _ _ (by decide)
  have a0 : -2 ^ 63 ≤ a.val := a.hmin
  have a1 : a.val < 2 ^ 63 := a.hmax
  have b0 : -2 ^ 63 ≤ b.val := b.hmin
  have b1 : b.val < 2 ^ 63 := b.hmax
  refine WP.spec_bind (IScalar.sub_spec
    (by rw [ca, cb, IScalar.min_IScalarTy_I128_eq, I128.min_eq]; omega)
    (by rw [ca, cb, IScalar.max_IScalarTy_I128_eq, I128.max_eq]; omega)) fun d hd => ?_
  rw [lift, bind_ok]
  have ⟨lo, hi⟩ := abs_le.mp (show |(b.val - a.val) * t.val| ≤ (2 ^ 64 - 1) * 2 ^ 63 from
    diff_prod_abs_le a b t)
  rw [ca, cb] at hd
  refine WP.spec_bind (IScalar.mul_spec
    (by rw [hd, ct, IScalar.min_IScalarTy_I128_eq, I128.min_eq]; omega)
    (by rw [hd, ct, IScalar.max_IScalarTy_I128_eq, I128.max_eq]; omega)) fun p hp => ?_
  rw [hd, ct] at hp
  refine WP.spec_bind (k64_round_frac_spec p) fun q hq => ?_
  have qb : -2 ^ 95 ≤ roundHalfUp (exact 32 ((b.val - a.val) * t.val)) ∧ roundHalfUp (exact 32 ((b.val - a.val) * t.val)) < 2 ^ 95 :=
    roundHalfUp_bounds ((b.val - a.val) * t.val) (-2 ^ 95) (2 ^ 95) 31 (by omega) (by omega)
  refine WP.spec_mono (IScalar.add_spec
    (by rw [ca, hq, hp, IScalar.min_IScalarTy_I128_eq, I128.min_eq]; omega)
    (by rw [ca, hq, hp, IScalar.max_IScalarTy_I128_eq, I128.max_eq]; omega)) fun r hr => ?_
  rw [hr, ca, hq, hp]

end Fulcrum

end
