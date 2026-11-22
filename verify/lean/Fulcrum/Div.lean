module

public import Fulcrum.Lerp
public import Fulcrum.Narrow

/-!
# L3: `kernel::kN::mul_div`, `div`, `div_int`

The `unsigned_abs` of `FunsExternal.lean` is the natural absolute value. On
magnitudes, `⌊(2·n + d) / 2·d⌋` rounds `n / d` and `-⌊(2·n + d - 1) / 2·d⌋`
rounds `-n / d` to nearest with ties toward `+∞` (`roundHalfUp_div`,
`roundHalfUp_neg_div`); `round_magnitude_div` of every width is that, once
`2·n + 2·d` fits its unsigned wide type (`rmd_shape`). The sign of the result
is the parity of the signs of the operands (`signed_div_eq`), so `mul_div(a,
b, c)` is `round(a · b / c)` for every width, and the magnitude forms of `div`
and `div_int` (`k8`, `k64`) are `round(a · 2^F / b)` and `round(a / n)`. The
signed form of `k16` and `k32` divides `2·n + bias` by `2·d` truncating
(`tdiv_round`), with the same results.
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace Fulcrum

/-- The bits of `BitVec.abs` read as unsigned are the natural absolute value. -/
theorem toNat_abs_eq_natAbs {w : ℕ} (x : BitVec w) : x.abs.toNat = x.toInt.natAbs := by
  have lt := x.isLt
  rw [BitVec.toNat_abs, BitVec.toInt_eq_msb_cond]
  cases x.msb
  · exact (Int.natAbs_natCast _).symm
  · rw [ite_eq_left rfl, ite_eq_left rfl]
    omega

/-- `i8::unsigned_abs` is `natAbs`. -/
theorem I8_unsigned_abs_spec (x : Std.I8) :
    core.num.I8.unsigned_abs x ⦃ u => u.val = x.val.natAbs ⦄ := by
  rw [core.num.I8.unsigned_abs, WP.spec_ok]
  exact toNat_abs_eq_natAbs x.bv

/-- `i16::unsigned_abs` is `natAbs`. -/
theorem I16_unsigned_abs_spec (x : Std.I16) :
    core.num.I16.unsigned_abs x ⦃ u => u.val = x.val.natAbs ⦄ := by
  rw [core.num.I16.unsigned_abs, WP.spec_ok]
  exact toNat_abs_eq_natAbs x.bv

/-- `i32::unsigned_abs` is `natAbs`. -/
theorem I32_unsigned_abs_spec (x : Std.I32) :
    core.num.I32.unsigned_abs x ⦃ u => u.val = x.val.natAbs ⦄ := by
  rw [core.num.I32.unsigned_abs, WP.spec_ok]
  exact toNat_abs_eq_natAbs x.bv

/-- `i64::unsigned_abs` is `natAbs`. -/
theorem I64_unsigned_abs_spec (x : Std.I64) :
    core.num.I64.unsigned_abs x ⦃ u => u.val = x.val.natAbs ⦄ := by
  rw [core.num.I64.unsigned_abs, WP.spec_ok]
  exact toNat_abs_eq_natAbs x.bv

/-- `⌊(2·n + d) / 2·d⌋` rounds `n / d` for `d > 0`. -/
theorem roundHalfUp_div (n d : ℤ) (hd : 0 < d) :
    roundHalfUp ((n : ℚ) / d) = (2 * n + d) / (2 * d) := by
  have hq : (d : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hd.ne'
  have h2 : (0 : ℤ) ≤ 2 * d := by omega
  have e : (n : ℚ) / d + 1 / 2 = ((2 * n + d : ℤ) : ℚ) / (((2 * d).toNat : ℕ) : ℚ) := by
    rw [← Int.cast_natCast (R := ℚ), Int.toNat_of_nonneg h2, Int.cast_add, Int.cast_mul,
      Int.cast_mul, Int.cast_ofNat, div_add_div _ _ hq two_ne_zero, mul_one, mul_comm (n : ℚ) 2,
      mul_comm (d : ℚ) 2]
  rw [roundHalfUp, e, Rat.floor_intCast_div_natCast, Int.toNat_of_nonneg h2]

/-- `⌊(-x + D - 1) / D⌋ = -⌊x / D⌋` for `D > 0`. -/
theorem neg_ediv_shape (x D : ℤ) (hD : 0 < D) : (-x + D - 1) / D = -(x / D) := by
  have h := Int.emod_add_mul_ediv x D
  have r0 := Int.emod_nonneg x hD.ne'
  have r1 := Int.emod_lt_of_pos x hD
  refine ((Int.ediv_emod_unique (r := D - 1 - x % D) hD).2 ⟨?_, ?_, ?_⟩).1
  · rw [mul_neg]; omega
  · omega
  · omega

/-- `-⌊(2·n + d - 1) / 2·d⌋` rounds `-n / d` for `d > 0`. -/
theorem roundHalfUp_neg_div (n d : ℤ) (hd : 0 < d) :
    roundHalfUp ((-n : ℤ) / (d : ℚ)) = -((2 * n + d - 1) / (2 * d)) := by
  rw [roundHalfUp_div _ _ hd, ← neg_ediv_shape _ _ (by omega)]
  congr 1
  omega

/-- `x << 1` doubles an unsigned `x` when the double fits. -/
theorem shl_one_spec {U} (x : UScalar U) (one : IScalar .I32) (h1 : one.val = 1)
    (hx : 2 * x.val < 2 ^ U.numBits) (hb : 1 < U.numBits) :
    (x <<< one) ⦃ z => z.val = 2 * x.val ⦄ := by
  have hs : one.toNat = 1 := by rw [IScalar.toNat, h1]; rfl
  refine WP.spec_mono (UScalar.ShiftLeft_IScalar_spec x one _ (by rw [h1]; decide)
    (by rw [h1]; exact_mod_cast hb) rfl) fun z ⟨hz, _⟩ => ?_
  rw [hz, hs, Nat.shiftLeft_eq, pow_one, mul_comm, UScalar.size_def]
  exact Nat.mod_eq_of_lt hx

/-- The body of `kernel::kN::round_magnitude_div`: `round(±un / ud)`. -/
theorem rmd_shape {U : UScalarTy} {W : IScalarTy} (un ud : UScalar U) (neg : Bool)
    (one : IScalar .I32) (h1 : one.val = 1) (hbits : W.numBits = U.numBits) (hb : 1 < U.numBits)
    (hd : 0 < ud.val) (hfit : 2 * un.val + 2 * ud.val < 2 ^ U.numBits) :
    (do
        let i ← un <<< one
        let i1 ← lift (UScalar.cast_fromBool U neg)
        let i2 ← ud - i1
        let i3 ← i + i2
        let i4 ← ud <<< one
        let m ← i3 / i4
        let m1 ← lift (UScalar.hcast W m)
        if neg then -. m1 else ok m1)
      ⦃ r => r.val = roundHalfUp ((if neg then -(un.val : ℤ) else un.val : ℤ) / (ud.val : ℚ)) ⦄ := by
  refine WP.spec_bind (shl_one_spec un one h1 (by omega) hb) fun i hi => ?_
  rw [lift, bind_ok]
  have hc := UScalar.cast_fromBool_val_eq U neg
  have hn1 : neg.toNat ≤ 1 := Bool.toNat_le neg
  refine WP.spec_bind (UScalar.sub_spec (x := ud) (y := UScalar.cast_fromBool U neg)
    (by rw [hc]; omega)) fun i2 ⟨hi2, _⟩ => ?_
  refine WP.spec_bind (UScalar.add_spec (x := i) (y := i2)
    (by rw [hi, hi2, hc, UScalar.max_def]; omega)) fun i3 hi3 => ?_
  refine WP.spec_bind (shl_one_spec ud one h1 (by omega) hb) fun i4 hi4 => ?_
  obtain ⟨m, hm, hmv⟩ := UScalar.div_spec i3 (y := i4) (by rw [hi4]; omega)
  rw [hi3, hi, hi2, hc, hi4] at hmv
  rw [hm, bind_ok]
  have hm2 : m.val ≤ (2 * un.val + ud.val) / 2 :=
    hmv ▸ Nat.div_le_div (by omega) (by omega) two_ne_zero
  have hmax : (m.val : ℤ) ≤ IScalar.max W := by
    rw [IScalar.max_def, hbits]
    have : (2 * un.val + ud.val) / 2 < 2 ^ (U.numBits - 1) := by
      rw [Nat.div_lt_iff_lt_mul two_pos, ← pow_succ, Nat.sub_add_cancel (by omega)]
      omega
    have e : ((2 ^ (U.numBits - 1) : ℕ) : ℤ) = (2 : ℤ) ^ (U.numBits - 1) := by
      rw [Nat.cast_pow, Nat.cast_ofNat]
    omega
  refine WP.spec_bind (UScalar.hcast_inBounds_spec W m hmax) fun m1 hm1 => ?_
  have hdz : (0 : ℤ) < ud.val := Int.ofNat_lt.mpr hd
  cases neg
  · rw [Bool.toNat_false, Nat.sub_zero] at hmv
    rw [ite_eq_right Bool.false_ne_true, WP.spec_ok, ite_eq_right Bool.false_ne_true, hm1, hmv,
      ← Int.cast_natCast (R := ℚ) ud.val, roundHalfUp_div _ _ hdz, Int.natCast_ediv, Nat.cast_add, Nat.cast_mul, Nat.cast_mul,
      Nat.cast_ofNat]
  · rw [Bool.toNat_true] at hmv
    have hmin : (m1 : ℤ) ≠ IScalar.min W := by
      rw [hm1, IScalar.min_def]
      have := pow_pos (zero_lt_two (α := ℤ)) (W.numBits - 1)
      omega
    rw [ite_eq_left rfl, ite_eq_left rfl]
    refine WP.spec_mono (HNeg.hNeg.step m1 hmin) fun r hr => ?_
    rw [hr, hm1, hmv, ← Int.cast_natCast (R := ℚ) ud.val, roundHalfUp_neg_div _ _ hdz, Int.natCast_ediv, Nat.cast_add, Nat.cast_mul,
      Nat.cast_mul, Nat.cast_sub hd, Nat.cast_ofNat, Nat.cast_one, add_sub_assoc]

/-- `±|x| / |y|` with the sign of the parity of the signs is `x / y`. -/
theorem signed_div_eq (x y : ℤ) (hy : y ≠ 0) (s : Bool)
    (hs : x ≠ 0 → s = (decide (x < 0) != decide (y < 0))) :
    (((if s then -(x.natAbs : ℤ) else x.natAbs : ℤ) : ℚ) / (y.natAbs : ℚ)) = (x : ℚ) / y := by
  by_cases hx : x = 0
  · cases s <;> simp only [hx, Int.natAbs_zero, Nat.cast_zero, neg_zero, Bool.false_eq_true,
      ↓reduceIte, Int.cast_zero, zero_div]
  rw [hs hx]
  rcases lt_or_gt_of_ne hx with hxn | hxp <;> rcases lt_or_gt_of_ne hy with hyn | hyp
  · rw [decide_eq_true hxn, decide_eq_true hyn, ite_eq_right (by decide),
      Int.natCast_natAbs, abs_of_neg hxn, ← Int.cast_natCast, Int.natCast_natAbs, abs_of_neg hyn,
      Int.cast_neg, Int.cast_neg, neg_div_neg_eq]
  · rw [decide_eq_true hxn, decide_eq_false (not_lt.mpr hyp.le), ite_eq_left (by decide),
      Int.natCast_natAbs, abs_of_neg hxn, neg_neg, ← Int.cast_natCast, Int.natCast_natAbs,
      abs_of_pos hyp]
  · rw [decide_eq_false (not_lt.mpr hxp.le), decide_eq_true hyn, ite_eq_left (by decide),
      Int.natCast_natAbs, abs_of_pos hxp, ← Int.cast_natCast, Int.natCast_natAbs, abs_of_neg hyn,
      Int.cast_neg, Int.cast_neg, neg_div_neg_eq]
  · rw [decide_eq_false (not_lt.mpr hxp.le), decide_eq_false (not_lt.mpr hyp.le),
      ite_eq_right (by decide), Int.natCast_natAbs, abs_of_pos hxp, ← Int.cast_natCast,
      Int.natCast_natAbs, abs_of_pos hyp]

/-- A non-zero product is negative exactly when one factor is. -/
theorem decide_mul_neg (a b : ℤ) (h : a * b ≠ 0) :
    decide (a * b < 0) = (decide (a < 0) != decide (b < 0)) := by
  have ha : a ≠ 0 := left_ne_zero_of_mul h
  have hb : b ≠ 0 := right_ne_zero_of_mul h
  rcases lt_or_gt_of_ne ha with an | ap <;> rcases lt_or_gt_of_ne hb with nn | bp
  · rw [decide_eq_false (not_lt.mpr (mul_pos_of_neg_of_neg an nn).le), decide_eq_true an,
      decide_eq_true nn]; rfl
  · rw [decide_eq_true (mul_neg_of_neg_of_pos an bp), decide_eq_true an,
      decide_eq_false (not_lt.mpr bp.le)]; rfl
  · rw [decide_eq_true (mul_neg_of_pos_of_neg ap nn), decide_eq_false (not_lt.mpr ap.le),
      decide_eq_true nn]; rfl
  · rw [decide_eq_false (not_lt.mpr (mul_pos ap bp).le), decide_eq_false (not_lt.mpr ap.le),
      decide_eq_false (not_lt.mpr bp.le)]; rfl


/-- `kernel::k8::round_magnitude_div` rounds `±un / ud`. -/
theorem k8_rmd_spec (un ud : Std.U16) (neg : Bool) (hd : 0 < ud.val)
    (hfit : 2 * un.val + 2 * ud.val < 2 ^ 16) :
    fulcrum.kernel.k8.round_magnitude_div un ud neg
      ⦃ r => r.val = roundHalfUp ((if neg then -(un.val : ℤ) else un.val : ℤ) / (ud.val : ℚ)) ⦄ := by
  unfold fulcrum.kernel.k8.round_magnitude_div
  exact rmd_shape un ud neg 1#i32 rfl rfl (by decide) hd hfit

/-- L3 on the code: `kernel::k8::mul_div` is `round(a · b / c)` for `c ≠ 0`. -/
theorem k8_mul_div_spec (a b c : Std.I8) (hc : c.val ≠ 0) :
    fulcrum.kernel.k8.mul_div a b c
      ⦃ r => r.val = roundHalfUp ((a.val * b.val : ℤ) / (c.val : ℚ)) ⦄ := by
  unfold fulcrum.kernel.k8.mul_div
  have na : a.val.natAbs ≤ 2 ^ 7 := by
    have h0 : -2 ^ 7 ≤ a.val := a.hmin
    have h1 : a.val < 2 ^ 7 := a.hmax
    omega
  have nb : b.val.natAbs ≤ 2 ^ 7 := by
    have h0 : -2 ^ 7 ≤ b.val := b.hmin
    have h1 : b.val < 2 ^ 7 := b.hmax
    omega
  have nc : c.val.natAbs ≤ 2 ^ 7 := by
    have h0 : -2 ^ 7 ≤ c.val := c.hmin
    have h1 : c.val < 2 ^ 7 := c.hmax
    omega
  refine WP.spec_bind (I8_unsigned_abs_spec a) fun ua hua => ?_
  rw [lift, bind_ok]
  refine WP.spec_bind (I8_unsigned_abs_spec b) fun ub hub => ?_
  rw [lift, bind_ok]
  have ca : (UScalar.cast .U16 ua).val = a.val.natAbs := by
    rw [UScalar.cast_val_eq, hua, UScalarTy.U16_numBits_eq]; exact Nat.mod_eq_of_lt (by omega)
  have cb : (UScalar.cast .U16 ub).val = b.val.natAbs := by
    rw [UScalar.cast_val_eq, hub, UScalarTy.U16_numBits_eq]; exact Nat.mod_eq_of_lt (by omega)
  have hab : a.val.natAbs * b.val.natAbs ≤ 2 ^ 7 * 2 ^ 7 := Nat.mul_le_mul na nb
  refine WP.spec_bind (UScalar.mul_spec (by rw [ca, cb, UScalar.max_def, UScalarTy.U16_numBits_eq]; omega))
    fun p hp => ?_
  refine WP.spec_bind (I8_unsigned_abs_spec c) fun uc huc => ?_
  rw [lift, bind_ok]
  have cc : (UScalar.cast .U16 uc).val = c.val.natAbs := by
    rw [UScalar.cast_val_eq, huc, UScalarTy.U16_numBits_eq]; exact Nat.mod_eq_of_lt (by omega)
  rw [ca, cb] at hp
  refine WP.spec_mono (k8_rmd_spec p _ _ (cc ▸ Int.natAbs_pos.mpr hc)
    (by rw [hp, cc]; omega)) fun r hr => ?_
  rw [hr, hp, cc, ← Int.natAbs_mul, signed_div_eq _ _ hc]
  intro h
  rw [decide_mul_neg _ _ h]
  rfl

/-- `kernel::k16::round_magnitude_div` rounds `±un / ud`. -/
theorem k16_rmd_spec (un ud : Std.U32) (neg : Bool) (hd : 0 < ud.val)
    (hfit : 2 * un.val + 2 * ud.val < 2 ^ 32) :
    fulcrum.kernel.k16.round_magnitude_div un ud neg
      ⦃ r => r.val = roundHalfUp ((if neg then -(un.val : ℤ) else un.val : ℤ) / (ud.val : ℚ)) ⦄ := by
  unfold fulcrum.kernel.k16.round_magnitude_div
  exact rmd_shape un ud neg 1#i32 rfl rfl (by decide) hd hfit

/-- L3 on the code: `kernel::k16::mul_div` is `round(a · b / c)` for `c ≠ 0`. -/
theorem k16_mul_div_spec (a b c : Std.I16) (hc : c.val ≠ 0) :
    fulcrum.kernel.k16.mul_div a b c
      ⦃ r => r.val = roundHalfUp ((a.val * b.val : ℤ) / (c.val : ℚ)) ⦄ := by
  unfold fulcrum.kernel.k16.mul_div
  have na : a.val.natAbs ≤ 2 ^ 15 := by
    have h0 : -2 ^ 15 ≤ a.val := a.hmin
    have h1 : a.val < 2 ^ 15 := a.hmax
    omega
  have nb : b.val.natAbs ≤ 2 ^ 15 := by
    have h0 : -2 ^ 15 ≤ b.val := b.hmin
    have h1 : b.val < 2 ^ 15 := b.hmax
    omega
  have nc : c.val.natAbs ≤ 2 ^ 15 := by
    have h0 : -2 ^ 15 ≤ c.val := c.hmin
    have h1 : c.val < 2 ^ 15 := c.hmax
    omega
  refine WP.spec_bind (I16_unsigned_abs_spec a) fun ua hua => ?_
  rw [lift, bind_ok]
  refine WP.spec_bind (I16_unsigned_abs_spec b) fun ub hub => ?_
  rw [lift, bind_ok]
  have ca : (UScalar.cast .U32 ua).val = a.val.natAbs := by
    rw [UScalar.cast_val_eq, hua, UScalarTy.U32_numBits_eq]; exact Nat.mod_eq_of_lt (by omega)
  have cb : (UScalar.cast .U32 ub).val = b.val.natAbs := by
    rw [UScalar.cast_val_eq, hub, UScalarTy.U32_numBits_eq]; exact Nat.mod_eq_of_lt (by omega)
  have hab : a.val.natAbs * b.val.natAbs ≤ 2 ^ 15 * 2 ^ 15 := Nat.mul_le_mul na nb
  refine WP.spec_bind (UScalar.mul_spec (by rw [ca, cb, UScalar.max_def, UScalarTy.U32_numBits_eq]; omega))
    fun p hp => ?_
  refine WP.spec_bind (I16_unsigned_abs_spec c) fun uc huc => ?_
  rw [lift, bind_ok]
  have cc : (UScalar.cast .U32 uc).val = c.val.natAbs := by
    rw [UScalar.cast_val_eq, huc, UScalarTy.U32_numBits_eq]; exact Nat.mod_eq_of_lt (by omega)
  rw [ca, cb] at hp
  refine WP.spec_mono (k16_rmd_spec p _ _ (cc ▸ Int.natAbs_pos.mpr hc)
    (by rw [hp, cc]; omega)) fun r hr => ?_
  rw [hr, hp, cc, ← Int.natAbs_mul, signed_div_eq _ _ hc]
  intro h
  rw [decide_mul_neg _ _ h]
  rfl

/-- `kernel::k32::round_magnitude_div` rounds `±un / ud`. -/
theorem k32_rmd_spec (un ud : Std.U64) (neg : Bool) (hd : 0 < ud.val)
    (hfit : 2 * un.val + 2 * ud.val < 2 ^ 64) :
    fulcrum.kernel.k32.round_magnitude_div un ud neg
      ⦃ r => r.val = roundHalfUp ((if neg then -(un.val : ℤ) else un.val : ℤ) / (ud.val : ℚ)) ⦄ := by
  unfold fulcrum.kernel.k32.round_magnitude_div
  exact rmd_shape un ud neg 1#i32 rfl rfl (by decide) hd hfit

/-- L3 on the code: `kernel::k32::mul_div` is `round(a · b / c)` for `c ≠ 0`. -/
theorem k32_mul_div_spec (a b c : Std.I32) (hc : c.val ≠ 0) :
    fulcrum.kernel.k32.mul_div a b c
      ⦃ r => r.val = roundHalfUp ((a.val * b.val : ℤ) / (c.val : ℚ)) ⦄ := by
  unfold fulcrum.kernel.k32.mul_div
  have na : a.val.natAbs ≤ 2 ^ 31 := by
    have h0 : -2 ^ 31 ≤ a.val := a.hmin
    have h1 : a.val < 2 ^ 31 := a.hmax
    omega
  have nb : b.val.natAbs ≤ 2 ^ 31 := by
    have h0 : -2 ^ 31 ≤ b.val := b.hmin
    have h1 : b.val < 2 ^ 31 := b.hmax
    omega
  have nc : c.val.natAbs ≤ 2 ^ 31 := by
    have h0 : -2 ^ 31 ≤ c.val := c.hmin
    have h1 : c.val < 2 ^ 31 := c.hmax
    omega
  refine WP.spec_bind (I32_unsigned_abs_spec a) fun ua hua => ?_
  rw [lift, bind_ok]
  refine WP.spec_bind (I32_unsigned_abs_spec b) fun ub hub => ?_
  rw [lift, bind_ok]
  have ca : (UScalar.cast .U64 ua).val = a.val.natAbs := by
    rw [UScalar.cast_val_eq, hua, UScalarTy.U64_numBits_eq]; exact Nat.mod_eq_of_lt (by omega)
  have cb : (UScalar.cast .U64 ub).val = b.val.natAbs := by
    rw [UScalar.cast_val_eq, hub, UScalarTy.U64_numBits_eq]; exact Nat.mod_eq_of_lt (by omega)
  have hab : a.val.natAbs * b.val.natAbs ≤ 2 ^ 31 * 2 ^ 31 := Nat.mul_le_mul na nb
  refine WP.spec_bind (UScalar.mul_spec (by rw [ca, cb, UScalar.max_def, UScalarTy.U64_numBits_eq]; omega))
    fun p hp => ?_
  refine WP.spec_bind (I32_unsigned_abs_spec c) fun uc huc => ?_
  rw [lift, bind_ok]
  have cc : (UScalar.cast .U64 uc).val = c.val.natAbs := by
    rw [UScalar.cast_val_eq, huc, UScalarTy.U64_numBits_eq]; exact Nat.mod_eq_of_lt (by omega)
  rw [ca, cb] at hp
  refine WP.spec_mono (k32_rmd_spec p _ _ (cc ▸ Int.natAbs_pos.mpr hc)
    (by rw [hp, cc]; omega)) fun r hr => ?_
  rw [hr, hp, cc, ← Int.natAbs_mul, signed_div_eq _ _ hc]
  intro h
  rw [decide_mul_neg _ _ h]
  rfl

/-- `kernel::k64::round_magnitude_div` rounds `±un / ud`. -/
theorem k64_rmd_spec (un ud : Std.U128) (neg : Bool) (hd : 0 < ud.val)
    (hfit : 2 * un.val + 2 * ud.val < 2 ^ 128) :
    fulcrum.kernel.k64.round_magnitude_div un ud neg
      ⦃ r => r.val = roundHalfUp ((if neg then -(un.val : ℤ) else un.val : ℤ) / (ud.val : ℚ)) ⦄ := by
  unfold fulcrum.kernel.k64.round_magnitude_div
  exact rmd_shape un ud neg 1#i32 rfl rfl (by decide) hd hfit

/-- L3 on the code: `kernel::k64::mul_div` is `round(a · b / c)` for `c ≠ 0`. -/
theorem k64_mul_div_spec (a b c : Std.I64) (hc : c.val ≠ 0) :
    fulcrum.kernel.k64.mul_div a b c
      ⦃ r => r.val = roundHalfUp ((a.val * b.val : ℤ) / (c.val : ℚ)) ⦄ := by
  unfold fulcrum.kernel.k64.mul_div
  have na : a.val.natAbs ≤ 2 ^ 63 := by
    have h0 : -2 ^ 63 ≤ a.val := a.hmin
    have h1 : a.val < 2 ^ 63 := a.hmax
    omega
  have nb : b.val.natAbs ≤ 2 ^ 63 := by
    have h0 : -2 ^ 63 ≤ b.val := b.hmin
    have h1 : b.val < 2 ^ 63 := b.hmax
    omega
  have nc : c.val.natAbs ≤ 2 ^ 63 := by
    have h0 : -2 ^ 63 ≤ c.val := c.hmin
    have h1 : c.val < 2 ^ 63 := c.hmax
    omega
  refine WP.spec_bind (I64_unsigned_abs_spec a) fun ua hua => ?_
  rw [lift, bind_ok]
  refine WP.spec_bind (I64_unsigned_abs_spec b) fun ub hub => ?_
  rw [lift, bind_ok]
  have ca : (UScalar.cast .U128 ua).val = a.val.natAbs := by
    rw [UScalar.cast_val_eq, hua, UScalarTy.U128_numBits_eq]; exact Nat.mod_eq_of_lt (by omega)
  have cb : (UScalar.cast .U128 ub).val = b.val.natAbs := by
    rw [UScalar.cast_val_eq, hub, UScalarTy.U128_numBits_eq]; exact Nat.mod_eq_of_lt (by omega)
  have hab : a.val.natAbs * b.val.natAbs ≤ 2 ^ 63 * 2 ^ 63 := Nat.mul_le_mul na nb
  refine WP.spec_bind (UScalar.mul_spec (by rw [ca, cb, UScalar.max_def, UScalarTy.U128_numBits_eq]; omega))
    fun p hp => ?_
  refine WP.spec_bind (I64_unsigned_abs_spec c) fun uc huc => ?_
  rw [lift, bind_ok]
  have cc : (UScalar.cast .U128 uc).val = c.val.natAbs := by
    rw [UScalar.cast_val_eq, huc, UScalarTy.U128_numBits_eq]; exact Nat.mod_eq_of_lt (by omega)
  rw [ca, cb] at hp
  refine WP.spec_mono (k64_rmd_spec p _ _ (cc ▸ Int.natAbs_pos.mpr hc)
    (by rw [hp, cc]; omega)) fun r hr => ?_
  rw [hr, hp, cc, ← Int.natAbs_mul, signed_div_eq _ _ hc]
  intro h
  rw [decide_mul_neg _ _ h]
  rfl


/-- L3 on the code: `kernel::k8::div` is `round(a · 2^4 / b)` for `b ≠ 0`. -/
theorem k8_div_spec (a b : Std.I8) (hb : b.val ≠ 0) :
    fulcrum.kernel.k8.div a b ⦃ r => r.val = roundHalfUp ((a.val * 2 ^ 4 : ℤ) / (b.val : ℚ)) ⦄ := by
  unfold fulcrum.kernel.k8.div
  have na : a.val.natAbs ≤ 2 ^ 7 := by
    have h0 : -2 ^ 7 ≤ a.val := a.hmin
    have h1 : a.val < 2 ^ 7 := a.hmax
    omega
  have nb : b.val.natAbs ≤ 2 ^ 7 := by
    have h0 : -2 ^ 7 ≤ b.val := b.hmin
    have h1 : b.val < 2 ^ 7 := b.hmax
    omega
  refine WP.spec_bind (I8_unsigned_abs_spec a) fun ua hua => ?_
  rw [lift, bind_ok]
  have ca : (UScalar.cast .U16 ua).val = a.val.natAbs := by
    rw [UScalar.cast_val_eq, hua, UScalarTy.U16_numBits_eq]; exact Nat.mod_eq_of_lt (by omega)
  have t : (4#i32 : Std.I32).toNat = 4 := rfl
  refine WP.spec_bind (UScalar.ShiftLeft_IScalar_spec (UScalar.cast .U16 ua) 4#i32 _ (by decide)
    (by decide) rfl) fun p ⟨hp, _⟩ => ?_
  have hp' : p.val = a.val.natAbs * 2 ^ 4 := by
    rw [hp, t, ca, Nat.shiftLeft_eq, UScalar.size_def, UScalarTy.U16_numBits_eq]
    exact Nat.mod_eq_of_lt (by omega)
  refine WP.spec_bind (I8_unsigned_abs_spec b) fun ub hub => ?_
  rw [lift, bind_ok]
  have cb : (UScalar.cast .U16 ub).val = b.val.natAbs := by
    rw [UScalar.cast_val_eq, hub, UScalarTy.U16_numBits_eq]; exact Nat.mod_eq_of_lt (by omega)
  refine WP.spec_mono (k8_rmd_spec p _ _ (cb ▸ Int.natAbs_pos.mpr hb)
    (by rw [hp', cb]; omega)) fun r hr => ?_
  have e : (a.val * 2 ^ 4).natAbs = a.val.natAbs * 2 ^ 4 := by rw [Int.natAbs_mul]; rfl
  rw [hr, hp', cb, ← e, signed_div_eq _ _ hb]
  intro h
  rw [decide_mul_neg _ _ h, show decide ((2 : ℤ) ^ 4 < 0) = false from rfl, Bool.bne_false]
  rfl

/-- L3 on the code: `kernel::k8::div_int` is `round(a / n)` for `n ≠ 0`. -/
theorem k8_div_int_spec (a n : Std.I8) (hn : n.val ≠ 0) :
    fulcrum.kernel.k8.div_int a n ⦃ r => r.val = roundHalfUp ((a.val : ℤ) / (n.val : ℚ)) ⦄ := by
  unfold fulcrum.kernel.k8.div_int
  have na : a.val.natAbs ≤ 2 ^ 7 := by
    have h0 : -2 ^ 7 ≤ a.val := a.hmin
    have h1 : a.val < 2 ^ 7 := a.hmax
    omega
  have nn : n.val.natAbs ≤ 2 ^ 7 := by
    have h0 : -2 ^ 7 ≤ n.val := n.hmin
    have h1 : n.val < 2 ^ 7 := n.hmax
    omega
  refine WP.spec_bind (I8_unsigned_abs_spec a) fun ua hua => ?_
  rw [lift, bind_ok]
  have ca : (UScalar.cast .U16 ua).val = a.val.natAbs := by
    rw [UScalar.cast_val_eq, hua, UScalarTy.U16_numBits_eq]; exact Nat.mod_eq_of_lt (by omega)
  refine WP.spec_bind (I8_unsigned_abs_spec n) fun un hun => ?_
  rw [lift, bind_ok]
  have cn : (UScalar.cast .U16 un).val = n.val.natAbs := by
    rw [UScalar.cast_val_eq, hun, UScalarTy.U16_numBits_eq]; exact Nat.mod_eq_of_lt (by omega)
  refine WP.spec_mono (k8_rmd_spec _ _ _ (cn ▸ Int.natAbs_pos.mpr hn)
    (by rw [ca, cn]; omega)) fun r hr => ?_
  rw [hr, ca, cn, signed_div_eq _ _ hn]
  intro _
  rfl

/-- L3 on the code: `kernel::k64::div` is `round(a · 2^32 / b)` for `b ≠ 0`. -/
theorem k64_div_spec (a b : Std.I64) (hb : b.val ≠ 0) :
    fulcrum.kernel.k64.div a b ⦃ r => r.val = roundHalfUp ((a.val * 2 ^ 32 : ℤ) / (b.val : ℚ)) ⦄ := by
  unfold fulcrum.kernel.k64.div
  have na : a.val.natAbs ≤ 2 ^ 63 := by
    have h0 : -2 ^ 63 ≤ a.val := a.hmin
    have h1 : a.val < 2 ^ 63 := a.hmax
    omega
  have nb : b.val.natAbs ≤ 2 ^ 63 := by
    have h0 : -2 ^ 63 ≤ b.val := b.hmin
    have h1 : b.val < 2 ^ 63 := b.hmax
    omega
  refine WP.spec_bind (I64_unsigned_abs_spec a) fun ua hua => ?_
  rw [lift, bind_ok]
  have ca : (UScalar.cast .U128 ua).val = a.val.natAbs := by
    rw [UScalar.cast_val_eq, hua, UScalarTy.U128_numBits_eq]; exact Nat.mod_eq_of_lt (by omega)
  have t : (32#i32 : Std.I32).toNat = 32 := rfl
  refine WP.spec_bind (UScalar.ShiftLeft_IScalar_spec (UScalar.cast .U128 ua) 32#i32 _ (by decide)
    (by decide) rfl) fun p ⟨hp, _⟩ => ?_
  have hp' : p.val = a.val.natAbs * 2 ^ 32 := by
    rw [hp, t, ca, Nat.shiftLeft_eq, UScalar.size_def, UScalarTy.U128_numBits_eq]
    exact Nat.mod_eq_of_lt (by omega)
  refine WP.spec_bind (I64_unsigned_abs_spec b) fun ub hub => ?_
  rw [lift, bind_ok]
  have cb : (UScalar.cast .U128 ub).val = b.val.natAbs := by
    rw [UScalar.cast_val_eq, hub, UScalarTy.U128_numBits_eq]; exact Nat.mod_eq_of_lt (by omega)
  refine WP.spec_mono (k64_rmd_spec p _ _ (cb ▸ Int.natAbs_pos.mpr hb)
    (by rw [hp', cb]; omega)) fun r hr => ?_
  have e : (a.val * 2 ^ 32).natAbs = a.val.natAbs * 2 ^ 32 := by rw [Int.natAbs_mul]; rfl
  rw [hr, hp', cb, ← e, signed_div_eq _ _ hb]
  intro h
  rw [decide_mul_neg _ _ h, show decide ((2 : ℤ) ^ 32 < 0) = false from rfl, Bool.bne_false]
  rfl

/-- L3 on the code: `kernel::k64::div_int` is `round(a / n)` for `n ≠ 0`. -/
theorem k64_div_int_spec (a n : Std.I64) (hn : n.val ≠ 0) :
    fulcrum.kernel.k64.div_int a n ⦃ r => r.val = roundHalfUp ((a.val : ℤ) / (n.val : ℚ)) ⦄ := by
  unfold fulcrum.kernel.k64.div_int
  have na : a.val.natAbs ≤ 2 ^ 63 := by
    have h0 : -2 ^ 63 ≤ a.val := a.hmin
    have h1 : a.val < 2 ^ 63 := a.hmax
    omega
  have nn : n.val.natAbs ≤ 2 ^ 63 := by
    have h0 : -2 ^ 63 ≤ n.val := n.hmin
    have h1 : n.val < 2 ^ 63 := n.hmax
    omega
  refine WP.spec_bind (I64_unsigned_abs_spec a) fun ua hua => ?_
  rw [lift, bind_ok]
  have ca : (UScalar.cast .U128 ua).val = a.val.natAbs := by
    rw [UScalar.cast_val_eq, hua, UScalarTy.U128_numBits_eq]; exact Nat.mod_eq_of_lt (by omega)
  refine WP.spec_bind (I64_unsigned_abs_spec n) fun un hun => ?_
  rw [lift, bind_ok]
  have cn : (UScalar.cast .U128 un).val = n.val.natAbs := by
    rw [UScalar.cast_val_eq, hun, UScalarTy.U128_numBits_eq]; exact Nat.mod_eq_of_lt (by omega)
  refine WP.spec_mono (k64_rmd_spec _ _ _ (cn ▸ Int.natAbs_pos.mpr hn)
    (by rw [ca, cn]; omega)) fun r hr => ?_
  rw [hr, ca, cn, signed_div_eq _ _ hn]
  intro _
  rfl

/-- The signed form of `div_kernel!`: `tdiv(2·n + bias, 2·d)` with the bias
`±(|d| - [d < 0])` of the sign of `n` rounds `n / d`. -/
theorem tdiv_round (n d : ℤ) (hd : d ≠ 0) :
    (2 * n + (if n < 0 then 1 - (decide (d < 0)).toInt - d.natAbs
      else d.natAbs - (decide (d < 0)).toInt)).tdiv (2 * d) = roundHalfUp ((n : ℚ) / d) := by
  rcases lt_or_gt_of_ne hd with dn | dp <;> rcases lt_or_ge n 0 with nn | np
  · rw [ite_eq_left nn, decide_eq_true dn, Bool.toInt_true, Int.ofNat_natAbs_of_nonpos dn.le,
      show 2 * n + (1 - 1 - -d) = -(2 * -n + -d) by omega, show 2 * d = -(2 * -d) by omega,
      Int.neg_tdiv_neg, Int.tdiv_eq_ediv_of_nonneg (by omega),
      ← roundHalfUp_div _ _ (by omega), Int.cast_neg, Int.cast_neg, neg_div_neg_eq]
  · rw [ite_eq_right (not_lt.mpr np), decide_eq_true dn, Bool.toInt_true,
      Int.ofNat_natAbs_of_nonpos dn.le, show 2 * d = -(2 * -d) by omega, Int.tdiv_neg,
      Int.tdiv_eq_ediv_of_nonneg (by omega), show 2 * n + (-d - 1) = 2 * n + -d - 1 by omega,
      ← roundHalfUp_neg_div _ _ (by omega), Int.cast_neg, Int.cast_neg, neg_div_neg_eq]
  · rw [ite_eq_left nn, decide_eq_false (not_lt.mpr dp.le), Bool.toInt_false,
      Int.natAbs_of_nonneg dp.le, show 2 * n + (1 - 0 - d) = -(2 * -n + d - 1) by omega,
      Int.neg_tdiv, Int.tdiv_eq_ediv_of_nonneg (by omega), ← roundHalfUp_neg_div _ _ dp, neg_neg]
  · rw [ite_eq_right (not_lt.mpr np), decide_eq_false (not_lt.mpr dp.le), Bool.toInt_false,
      Int.natAbs_of_nonneg dp.le, sub_zero, Int.tdiv_eq_ediv_of_nonneg (by omega),
      ← roundHalfUp_div _ _ dp]

/-- `x << 1` doubles a signed `x` when the double fits. -/
theorem ishl_one_spec {W} (x : IScalar W) (k : ℕ) (hk : W.numBits = k + 1) (hk1 : 1 ≤ k)
    (h : InRange k (2 * x.val)) : (x <<< (1#i32 : Std.I32)) ⦃ z => z.val = 2 * x.val ⦄ := by
  have one : (1#i32 : Std.I32).val = 1 := rfl
  refine WP.spec_mono (IScalar.ShiftLeft_IScalar_spec x 1#i32 (by rw [one]; decide)
    (by rw [one, hk]; omega)) fun z ⟨hz, _⟩ => ?_
  rw [hz, show (1#i32 : Std.I32).toNat = 1 from rfl, Int.shiftLeft_eq, pow_one, mul_comm, hk]
  exact (wrap_eq_self_iff k _).2 h

/-- `kernel::k16::round_div` rounds `n / d` for `d ≠ 0` and small enough `n`, `d`. -/
theorem k16_round_div_spec (n d : Std.I32) (hd : d.val ≠ 0) (hn : n.val.natAbs < 2 ^ 29)
    (hd' : d.val.natAbs < 2 ^ 29) :
    fulcrum.kernel.k16.round_div n d ⦃ r => r.val = roundHalfUp ((n.val : ℚ) / d.val) ⦄ := by
  unfold fulcrum.kernel.k16.round_div
  refine WP.spec_bind (I32_unsigned_abs_spec d) fun i hi => ?_
  refine WP.spec_bind (UScalar.hcast_inBounds_spec .I32 i
    (by rw [hi, IScalar.max_IScalarTy_I32_eq, I32.max_eq]; omega)) fun ud hud => ?_
  rw [lift, bind_ok]
  have hsd := IScalar.cast_fromBool_val_eq .I32 (decide (d < 0#i32))
  have one : (1#i32 : Std.I32).val = 1 := rfl
  have hs : (decide (d < 0#i32)).toInt ≤ 1 ∧ 0 ≤ (decide (d < 0#i32)).toInt := by
    cases decide (d < 0#i32) <;> decide
  have hbias : (if n < 0#i32 then do
        let i1 ← 1#i32 - IScalar.cast_fromBool .I32 (decide (d < 0#i32))
        i1 - ud
      else ud - IScalar.cast_fromBool .I32 (decide (d < 0#i32)))
      ⦃ b => b.val = if n.val < 0 then 1 - (decide (d.val < 0)).toInt - d.val.natAbs
        else d.val.natAbs - (decide (d.val < 0)).toInt ⦄ := by
    by_cases hneg : n < 0#i32
    · rw [ite_eq_left hneg]
      refine WP.spec_bind (IScalar.sub_spec
        (by rw [one, hsd, IScalar.min_IScalarTy_I32_eq, I32.min_eq]; omega)
        (by rw [one, hsd, IScalar.max_IScalarTy_I32_eq, I32.max_eq]; omega)) fun i1 hi1 => ?_
      refine WP.spec_mono (IScalar.sub_spec
        (by rw [hi1, one, hud, hi, hsd, IScalar.min_IScalarTy_I32_eq, I32.min_eq]; omega)
        (by rw [hi1, one, hud, hi, hsd, IScalar.max_IScalarTy_I32_eq, I32.max_eq]; omega))
        fun b hb => ?_
      rw [hb, hi1, one, hud, hi, hsd, ite_eq_left (show n.val < 0 from hneg)]
      rfl
    · rw [ite_eq_right hneg]
      refine WP.spec_mono (IScalar.sub_spec
        (by rw [hud, hi, hsd, IScalar.min_IScalarTy_I32_eq, I32.min_eq]; omega)
        (by rw [hud, hi, hsd, IScalar.max_IScalarTy_I32_eq, I32.max_eq]; omega)) fun b hb => ?_
      rw [hb, hud, hi, hsd, ite_eq_right (show ¬ n.val < 0 from hneg)]
      rfl
  refine WP.spec_bind hbias fun bias hb => ?_
  refine WP.spec_bind (ishl_one_spec n 31 rfl (by decide) (by unfold InRange minOf maxOf; omega))
    fun i1 hi1 => ?_
  have hbb : |bias.val| ≤ 2 ^ 29 + 1 := by
    rw [hb]; split <;> (cases decide (d.val < 0) <;> rw [abs_le] <;> constructor <;> simp only [Bool.toInt_true, Bool.toInt_false] <;> omega)
  have ⟨bl, bu⟩ := abs_le.mp hbb
  refine WP.spec_bind (IScalar.add_spec (x := i1) (y := bias)
    (by rw [hi1, IScalar.min_IScalarTy_I32_eq, I32.min_eq]; omega)
    (by rw [hi1, IScalar.max_IScalarTy_I32_eq, I32.max_eq]; omega)) fun i2 hi2 => ?_
  refine WP.spec_bind (ishl_one_spec d 31 rfl (by decide) (by unfold InRange minOf maxOf; omega))
    fun i3 hi3 => ?_
  obtain ⟨z, hz, hzv⟩ := IScalar.div_spec (x := i2) (y := i3) (by rw [hi3]; omega)
    (fun ⟨h, _⟩ => by rw [hi2, hi1, IScalar.min_IScalarTy_I32_eq, I32.min_eq] at h; omega)
  rw [hz, WP.spec_ok, hzv, hi2, hi1, hi3, hb]
  exact tdiv_round n.val d.val hd

/-- L3 on the code: `kernel::k16::div` is `round(a · 2^8 / b)` for `b ≠ 0`. -/
theorem k16_div_spec (a b : Std.I16) (hb : b.val ≠ 0) :
    fulcrum.kernel.k16.div a b ⦃ r => r.val = roundHalfUp ((a.val * 2 ^ 8 : ℤ) / (b.val : ℚ)) ⦄ := by
  unfold fulcrum.kernel.k16.div
  rw [lift, bind_ok]
  have ca : (IScalar.cast .I32 a).val = a.val := IScalar.val_mod_pow_greater_numBits _ _ (by decide)
  have cb : (IScalar.cast .I32 b).val = b.val := IScalar.val_mod_pow_greater_numBits _ _ (by decide)
  have a0 : -2 ^ 15 ≤ a.val := a.hmin
  have a1 : a.val < 2 ^ 15 := a.hmax
  have b0 : -2 ^ 15 ≤ b.val := b.hmin
  have b1 : b.val < 2 ^ 15 := b.hmax
  refine WP.spec_bind (IScalar.ShiftLeft_IScalar_spec (IScalar.cast .I32 a) 8#i32 (by decide)
    (by decide)) fun p ⟨hp, _⟩ => ?_
  have hp' : p.val = a.val * 2 ^ 8 := by
    rw [hp, show (8#i32 : Std.I32).toNat = 8 from rfl, Int.shiftLeft_eq, ca]
    exact (wrap_eq_self_iff 31 _).2 (by unfold InRange minOf maxOf; omega)
  rw [lift, bind_ok]
  refine WP.spec_mono (k16_round_div_spec p _ (by rw [cb]; exact hb) (by rw [hp']; omega)
    (by rw [cb]; omega)) fun r hr => ?_
  rw [hr, hp', cb]

/-- L3 on the code: `kernel::k16::div_int` is `round(a / n)` for `n ≠ 0`. -/
theorem k16_div_int_spec (a n : Std.I16) (hn : n.val ≠ 0) :
    fulcrum.kernel.k16.div_int a n ⦃ r => r.val = roundHalfUp ((a.val : ℤ) / (n.val : ℚ)) ⦄ := by
  unfold fulcrum.kernel.k16.div_int
  rw [lift, bind_ok, lift, bind_ok]
  have ca : (IScalar.cast .I32 a).val = a.val := IScalar.val_mod_pow_greater_numBits _ _ (by decide)
  have cn : (IScalar.cast .I32 n).val = n.val := IScalar.val_mod_pow_greater_numBits _ _ (by decide)
  have a0 : -2 ^ 15 ≤ a.val := a.hmin
  have a1 : a.val < 2 ^ 15 := a.hmax
  have n0 : -2 ^ 15 ≤ n.val := n.hmin
  have n1 : n.val < 2 ^ 15 := n.hmax
  refine WP.spec_mono (k16_round_div_spec _ _ (by rw [cn]; exact hn) (by rw [ca]; omega)
    (by rw [cn]; omega)) fun r hr => ?_
  rw [hr, ca, cn]

/-- `kernel::k32::round_div` rounds `n / d` for `d ≠ 0` and small enough `n`, `d`. -/
theorem k32_round_div_spec (n d : Std.I64) (hd : d.val ≠ 0) (hn : n.val.natAbs < 2 ^ 61)
    (hd' : d.val.natAbs < 2 ^ 61) :
    fulcrum.kernel.k32.round_div n d ⦃ r => r.val = roundHalfUp ((n.val : ℚ) / d.val) ⦄ := by
  unfold fulcrum.kernel.k32.round_div
  refine WP.spec_bind (I64_unsigned_abs_spec d) fun i hi => ?_
  refine WP.spec_bind (UScalar.hcast_inBounds_spec .I64 i
    (by rw [hi, IScalar.max_IScalarTy_I64_eq, I64.max_eq]; omega)) fun ud hud => ?_
  rw [lift, bind_ok]
  have hsd := IScalar.cast_fromBool_val_eq .I64 (decide (d < 0#i64))
  have one : (1#i64 : Std.I64).val = 1 := rfl
  have hs : (decide (d < 0#i64)).toInt ≤ 1 ∧ 0 ≤ (decide (d < 0#i64)).toInt := by
    cases decide (d < 0#i64) <;> decide
  have hbias : (if n < 0#i64 then do
        let i1 ← 1#i64 - IScalar.cast_fromBool .I64 (decide (d < 0#i64))
        i1 - ud
      else ud - IScalar.cast_fromBool .I64 (decide (d < 0#i64)))
      ⦃ b => b.val = if n.val < 0 then 1 - (decide (d.val < 0)).toInt - d.val.natAbs
        else d.val.natAbs - (decide (d.val < 0)).toInt ⦄ := by
    by_cases hneg : n < 0#i64
    · rw [ite_eq_left hneg]
      refine WP.spec_bind (IScalar.sub_spec
        (by rw [one, hsd, IScalar.min_IScalarTy_I64_eq, I64.min_eq]; omega)
        (by rw [one, hsd, IScalar.max_IScalarTy_I64_eq, I64.max_eq]; omega)) fun i1 hi1 => ?_
      refine WP.spec_mono (IScalar.sub_spec
        (by rw [hi1, one, hud, hi, hsd, IScalar.min_IScalarTy_I64_eq, I64.min_eq]; omega)
        (by rw [hi1, one, hud, hi, hsd, IScalar.max_IScalarTy_I64_eq, I64.max_eq]; omega))
        fun b hb => ?_
      rw [hb, hi1, one, hud, hi, hsd, ite_eq_left (show n.val < 0 from hneg)]
      rfl
    · rw [ite_eq_right hneg]
      refine WP.spec_mono (IScalar.sub_spec
        (by rw [hud, hi, hsd, IScalar.min_IScalarTy_I64_eq, I64.min_eq]; omega)
        (by rw [hud, hi, hsd, IScalar.max_IScalarTy_I64_eq, I64.max_eq]; omega)) fun b hb => ?_
      rw [hb, hud, hi, hsd, ite_eq_right (show ¬ n.val < 0 from hneg)]
      rfl
  refine WP.spec_bind hbias fun bias hb => ?_
  refine WP.spec_bind (ishl_one_spec n 63 rfl (by decide) (by unfold InRange minOf maxOf; omega))
    fun i1 hi1 => ?_
  have hbb : |bias.val| ≤ 2 ^ 61 + 1 := by
    rw [hb]; split <;> (cases decide (d.val < 0) <;> rw [abs_le] <;> constructor <;> simp only [Bool.toInt_true, Bool.toInt_false] <;> omega)
  have ⟨bl, bu⟩ := abs_le.mp hbb
  refine WP.spec_bind (IScalar.add_spec (x := i1) (y := bias)
    (by rw [hi1, IScalar.min_IScalarTy_I64_eq, I64.min_eq]; omega)
    (by rw [hi1, IScalar.max_IScalarTy_I64_eq, I64.max_eq]; omega)) fun i2 hi2 => ?_
  refine WP.spec_bind (ishl_one_spec d 63 rfl (by decide) (by unfold InRange minOf maxOf; omega))
    fun i3 hi3 => ?_
  obtain ⟨z, hz, hzv⟩ := IScalar.div_spec (x := i2) (y := i3) (by rw [hi3]; omega)
    (fun ⟨h, _⟩ => by rw [hi2, hi1, IScalar.min_IScalarTy_I64_eq, I64.min_eq] at h; omega)
  rw [hz, WP.spec_ok, hzv, hi2, hi1, hi3, hb]
  exact tdiv_round n.val d.val hd

/-- L3 on the code: `kernel::k32::div` is `round(a · 2^16 / b)` for `b ≠ 0`. -/
theorem k32_div_spec (a b : Std.I32) (hb : b.val ≠ 0) :
    fulcrum.kernel.k32.div a b ⦃ r => r.val = roundHalfUp ((a.val * 2 ^ 16 : ℤ) / (b.val : ℚ)) ⦄ := by
  unfold fulcrum.kernel.k32.div
  rw [lift, bind_ok]
  have ca : (IScalar.cast .I64 a).val = a.val := IScalar.val_mod_pow_greater_numBits _ _ (by decide)
  have cb : (IScalar.cast .I64 b).val = b.val := IScalar.val_mod_pow_greater_numBits _ _ (by decide)
  have a0 : -2 ^ 31 ≤ a.val := a.hmin
  have a1 : a.val < 2 ^ 31 := a.hmax
  have b0 : -2 ^ 31 ≤ b.val := b.hmin
  have b1 : b.val < 2 ^ 31 := b.hmax
  refine WP.spec_bind (IScalar.ShiftLeft_IScalar_spec (IScalar.cast .I64 a) 16#i32 (by decide)
    (by decide)) fun p ⟨hp, _⟩ => ?_
  have hp' : p.val = a.val * 2 ^ 16 := by
    rw [hp, show (16#i32 : Std.I32).toNat = 16 from rfl, Int.shiftLeft_eq, ca]
    exact (wrap_eq_self_iff 63 _).2 (by unfold InRange minOf maxOf; omega)
  rw [lift, bind_ok]
  refine WP.spec_mono (k32_round_div_spec p _ (by rw [cb]; exact hb) (by rw [hp']; omega)
    (by rw [cb]; omega)) fun r hr => ?_
  rw [hr, hp', cb]

/-- L3 on the code: `kernel::k32::div_int` is `round(a / n)` for `n ≠ 0`. -/
theorem k32_div_int_spec (a n : Std.I32) (hn : n.val ≠ 0) :
    fulcrum.kernel.k32.div_int a n ⦃ r => r.val = roundHalfUp ((a.val : ℤ) / (n.val : ℚ)) ⦄ := by
  unfold fulcrum.kernel.k32.div_int
  rw [lift, bind_ok, lift, bind_ok]
  have ca : (IScalar.cast .I64 a).val = a.val := IScalar.val_mod_pow_greater_numBits _ _ (by decide)
  have cn : (IScalar.cast .I64 n).val = n.val := IScalar.val_mod_pow_greater_numBits _ _ (by decide)
  have a0 : -2 ^ 31 ≤ a.val := a.hmin
  have a1 : a.val < 2 ^ 31 := a.hmax
  have n0 : -2 ^ 31 ≤ n.val := n.hmin
  have n1 : n.val < 2 ^ 31 := n.hmax
  refine WP.spec_mono (k32_round_div_spec _ _ (by rw [cn]; exact hn) (by rw [ca]; omega)
    (by rw [cn]; omega)) fun r hr => ?_
  rw [hr, ca, cn]

end Fulcrum

end
