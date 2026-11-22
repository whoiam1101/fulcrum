module

public import Fulcrum.Math.Div
public import Fulcrum.Lemmas.Scalar
public import Fulcrum.Lemmas.Nat

/-!
# L3: `mul_div` of every width, `div` and `div_int` of `k8` and `k64`

The magnitude form of `div_kernel!`: `round_magnitude_div` of every width
rounds `±un / ud` once `2·n + 2·d` fits its unsigned wide type (`rmd_shape`),
and the sign is the parity of the signs of the operands, so `mul_div(a, b, c)`
is `round(a · b / c)` for every width (`mul_div_shape`), and `div` and
`div_int` of `k8` and `k64` are `round(a · 2^F / b)` and `round(a / n)`
(`div_shape`, `div_int_shape`), as Aeneas extracts them.
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace Fulcrum

/-! ## The magnitude form -/

/-- `x << 1` doubles an unsigned `x` when the double fits. -/
theorem shl_one_spec {U} (x : UScalar U) (one : IScalar .I32) (h1 : one.val = 1)
    (hx : 2 * x.val < 2 ^ U.numBits) (hb : 1 < U.numBits) :
    (x <<< one) ⦃ z => z.val = 2 * x.val ⦄ :=
  WP.spec_mono (shl_i32_spec x one 1 h1 hb (by rw [pow_one, mul_comm]; exact hx)) fun z hz => by
    rw [hz, pow_one, mul_comm]

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
  have hn : 2 * un.val + ud.val < 2 ^ U.numBits :=
    lt_of_le_of_lt (Nat.add_le_add_left (Nat.le_mul_of_pos_left _ two_pos) _) hfit
  refine WP.spec_bind (shl_one_spec un one h1
    (lt_of_le_of_lt (Nat.le_add_right _ _) hfit) hb) fun i hi => ?_
  rw [lift, bind_ok]
  have hc := UScalar.cast_fromBool_val_eq U neg
  have hsub : 2 * un.val + (ud.val - neg.toNat) ≤ 2 * un.val + ud.val :=
    Nat.add_le_add_left (Nat.sub_le _ _) _
  refine WP.spec_bind (UScalar.sub_spec (x := ud) (y := UScalar.cast_fromBool U neg)
    (by rw [hc]; exact (Bool.toNat_le neg).trans hd)) fun i2 ⟨hi2, _⟩ => ?_
  refine WP.spec_bind (UScalar.add_spec (x := i) (y := i2)
    (by rw [hi, hi2, hc, UScalar.max_def]; exact Nat.le_sub_one_of_lt (lt_of_le_of_lt hsub hn)))
    fun i3 hi3 => ?_
  refine WP.spec_bind (shl_one_spec ud one h1
    (lt_of_le_of_lt (Nat.le_add_left _ _) hfit) hb) fun i4 hi4 => ?_
  obtain ⟨m, hm, hmv⟩ := UScalar.div_spec i3 (y := i4)
    (by rw [hi4]; exact Nat.mul_ne_zero two_ne_zero hd.ne')
  rw [hi3, hi, hi2, hc, hi4] at hmv
  rw [hm, bind_ok]
  have hm2 : m.val ≤ (2 * un.val + ud.val) / 2 :=
    hmv ▸ Nat.div_le_div hsub (Nat.le_mul_of_pos_right 2 hd) two_ne_zero
  have hlt : (2 * un.val + ud.val) / 2 < 2 ^ (U.numBits - 1) := by
    rw [Nat.div_lt_iff_lt_mul two_pos, ← pow_succ, Nat.sub_add_cancel hb.le]
    exact hn
  have hmax : (m.val : ℤ) ≤ IScalar.max W := by
    rw [IScalar.max_def, hbits]
    exact Int.le_sub_one_of_lt (by exact_mod_cast lt_of_le_of_lt hm2 hlt)
  refine WP.spec_bind (UScalar.hcast_inBounds_spec W m hmax) fun m1 hm1 => ?_
  have hdz : (0 : ℤ) < ud.val := Int.ofNat_lt.mpr hd
  cases neg
  · rw [Bool.toNat_false, Nat.sub_zero] at hmv
    rw [ite_eq_right Bool.false_ne_true, WP.spec_ok, ite_eq_right Bool.false_ne_true, hm1, hmv,
      ← Int.cast_natCast (R := ℚ) ud.val, roundHalfUp_div _ _ hdz, Int.natCast_ediv,
      Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat]
  · rw [Bool.toNat_true] at hmv
    have hmin : (m1 : ℤ) ≠ IScalar.min W := by
      rw [hm1, IScalar.min_def]
      exact ne_of_gt (lt_of_lt_of_le (neg_neg_of_pos (pow_pos zero_lt_two _))
        (Int.natCast_nonneg _))
    rw [ite_eq_left rfl, ite_eq_left rfl]
    refine WP.spec_mono (HNeg.hNeg.step m1 hmin) fun r hr => ?_
    rw [hr, hm1, hmv, ← Int.cast_natCast (R := ℚ) ud.val, roundHalfUp_neg_div _ _ hdz,
      Int.natCast_ediv, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hd, Nat.cast_ofNat,
      Nat.cast_one, add_sub_assoc]

/-- The contract of `round_magnitude_div`: `rmd` rounds `±un / ud` once
`2·un + 2·ud` fits `U`. -/
def RoundsMagnitude {U W} (rmd : UScalar U → UScalar U → Bool → Result (IScalar W)) : Prop :=
  ∀ un ud neg, 0 < ud.val → 2 * un.val + 2 * ud.val < 2 ^ U.numBits → rmd un ud neg ⦃ r =>
    r.val = roundHalfUp ((if neg then -(un.val : ℤ) else un.val : ℤ) / (ud.val : ℚ)) ⦄

/-- `unsigned_abs` of a signed `x`, widened to `U`, is `|x|`. -/
theorem abs_cast_bind {S V U β} (abs : IScalar S → Result (UScalar V))
    (habs : ∀ x, abs x ⦃ u => u.val = x.val.natAbs ⦄) (hVU : V.numBits ≤ U.numBits)
    (x : IScalar S) (f : UScalar U → Result β) (P : β → Prop)
    (h : ∀ u : UScalar U, u.val = x.val.natAbs → f u ⦃ r => P r ⦄) :
    (do
        let i ← abs x
        let i1 ← lift (UScalar.cast U i)
        f i1) ⦃ r => P r ⦄ :=
  WP.spec_bind (habs x) fun i hi => by
    rw [lift, bind_ok]
    exact h _ ((UScalar.cast_val_mod_pow_greater_numBits_eq _ i hVU).trans hi)

/-- `kernel::kN::mul_div` of every width: `round(a · b / c)` from the magnitudes. -/
theorem mul_div_shape {S V U W} (k : ℕ) (hS : S.numBits = k + 1) (hV : V.numBits = k + 1)
    (hU : U.numBits = 2 * k + 2) (hk : 0 < k) (abs : IScalar S → Result (UScalar V))
    (habs : ∀ x, abs x ⦃ u => u.val = x.val.natAbs ⦄)
    (rmd : UScalar U → UScalar U → Bool → Result (IScalar W)) (hrmd : RoundsMagnitude rmd)
    (zero : IScalar S) (hz : ∀ x : IScalar S, decide (x < zero) = decide (x.val < 0))
    (a b c : IScalar S) (hc : c.val ≠ 0) :
    (do
        let i ← abs a
        let i1 ← lift (UScalar.cast U i)
        let i2 ← abs b
        let i3 ← lift (UScalar.cast U i2)
        let i4 ← i1 * i3
        let i5 ← abs c
        let i6 ← lift (UScalar.cast U i5)
        rmd i4 i6 (((a < zero) != (b < zero)) != (c < zero)))
      ⦃ r => r.val = roundHalfUp ((a.val * b.val : ℤ) / (c.val : ℚ)) ⦄ := by
  have hVU : V.numBits ≤ U.numBits := hV ▸ hU ▸ succ_le_two_mul_add_two k
  have fit := fit_mul_add k _ _ _ hk (natAbs_le_pow a k hS) (natAbs_le_pow b k hS)
    (natAbs_le_pow c k hS)
  refine abs_cast_bind abs habs hVU a _ _ fun ua ca => ?_
  refine abs_cast_bind abs habs hVU b _ _ fun ub cb => ?_
  refine WP.spec_bind (UScalar.mul_spec (by
    rw [ca, cb, UScalar.max_def, hU]; exact Nat.le_sub_one_of_lt (lt_of_two_mul_add_lt fit)))
    fun p hp => ?_
  refine abs_cast_bind abs habs hVU c _ _ fun uc cc => ?_
  rw [ca, cb] at hp
  refine WP.spec_mono (hrmd p uc _ (cc ▸ Int.natAbs_pos.mpr hc)
    (by rw [hp, cc, hU]; exact fit)) fun r hr => ?_
  rw [hr, hp, cc, ← Int.natAbs_mul, signed_div_eq _ _ hc]
  intro h
  rw [decide_mul_neg _ _ h, hz, hz, hz]

/-- `kernel::kN::div` of the magnitude form: `round(a · 2^F / b)` from the magnitudes. -/
theorem div_shape {S V U W} (k F : ℕ) (hS : S.numBits = k + 1) (hV : V.numBits = k + 1)
    (hU : U.numBits = 2 * k + 2) (hk : 0 < k) (hF : F ≤ k)
    (abs : IScalar S → Result (UScalar V))
    (habs : ∀ x, abs x ⦃ u => u.val = x.val.natAbs ⦄)
    (rmd : UScalar U → UScalar U → Bool → Result (IScalar W)) (hrmd : RoundsMagnitude rmd)
    (zero : IScalar S) (hz : ∀ x : IScalar S, decide (x < zero) = decide (x.val < 0))
    (f : Std.I32) (hf : f.val = F) (a b : IScalar S) (hb : b.val ≠ 0) :
    (do
        let i ← abs a
        let i1 ← lift (UScalar.cast U i)
        let i2 ← i1 <<< f
        let i3 ← abs b
        let i4 ← lift (UScalar.cast U i3)
        rmd i2 i4 ((a < zero) != (b < zero)))
      ⦃ r => r.val = roundHalfUp ((a.val * 2 ^ F : ℤ) / (b.val : ℚ)) ⦄ := by
  have hkU := succ_le_two_mul_add_two k
  have hVU : V.numBits ≤ U.numBits := by rw [hV, hU]; exact hkU
  have fit := fit_mul_add k _ _ _ hk (natAbs_le_pow a k hS) (Nat.pow_le_pow_right two_pos hF)
    (natAbs_le_pow b k hS)
  have ft : IScalar.toNat f = F := by rw [IScalar.toNat, hf, Int.toNat_natCast]
  refine abs_cast_bind abs habs hVU a _ _ fun ua ca => ?_
  refine WP.spec_bind (UScalar.ShiftLeft_IScalar_spec ua f _ (hf ▸ Int.natCast_nonneg F)
    (by rw [hf, hU]; exact Int.ofNat_lt.mpr (lt_of_le_of_lt hF hkU)) rfl) fun p ⟨hp, _⟩ => ?_
  have hp' : p.val = a.val.natAbs * 2 ^ F := by
    rw [hp, ft, ca, Nat.shiftLeft_eq, UScalar.size_def, hU]
    exact Nat.mod_eq_of_lt (lt_of_two_mul_add_lt fit)
  refine abs_cast_bind abs habs hVU b _ _ fun ub cb => ?_
  refine WP.spec_mono (hrmd p ub _ (cb ▸ Int.natAbs_pos.mpr hb)
    (by rw [hp', cb, hU]; exact fit)) fun r hr => ?_
  have e : (a.val * 2 ^ F).natAbs = a.val.natAbs * 2 ^ F := by
    rw [Int.natAbs_mul, Int.natAbs_pow]; rfl
  rw [hr, hp', cb, ← e, signed_div_eq _ _ hb]
  intro h
  rw [decide_mul_neg _ _ h, decide_eq_false (not_lt.mpr (pow_pos zero_lt_two F).le),
    Bool.bne_false, hz, hz]

/-- `kernel::kN::div_int` of the magnitude form: `round(a / n)` from the magnitudes. -/
theorem div_int_shape {S V U W} (k : ℕ) (hS : S.numBits = k + 1) (hV : V.numBits = k + 1)
    (hU : U.numBits = 2 * k + 2) (hk : 0 < k) (abs : IScalar S → Result (UScalar V))
    (habs : ∀ x, abs x ⦃ u => u.val = x.val.natAbs ⦄)
    (rmd : UScalar U → UScalar U → Bool → Result (IScalar W)) (hrmd : RoundsMagnitude rmd)
    (zero : IScalar S) (hz : ∀ x : IScalar S, decide (x < zero) = decide (x.val < 0))
    (a n : IScalar S) (hn : n.val ≠ 0) :
    (do
        let i ← abs a
        let i1 ← lift (UScalar.cast U i)
        let i2 ← abs n
        let i3 ← lift (UScalar.cast U i2)
        rmd i1 i3 ((a < zero) != (n < zero)))
      ⦃ r => r.val = roundHalfUp ((a.val : ℤ) / (n.val : ℚ)) ⦄ := by
  have hVU : V.numBits ≤ U.numBits := hV ▸ hU ▸ succ_le_two_mul_add_two k
  refine abs_cast_bind abs habs hVU a _ _ fun ua ca => ?_
  refine abs_cast_bind abs habs hVU n _ _ fun un cn => ?_
  refine WP.spec_mono (hrmd ua un _ (cn ▸ Int.natAbs_pos.mpr hn) (by
    rw [ca, cn, hU, ← mul_one a.val.natAbs]
    exact fit_mul_add k _ _ _ hk (natAbs_le_pow a k hS) Nat.one_le_two_pow (natAbs_le_pow n k hS)))
    fun r hr => ?_
  rw [hr, ca, cn, signed_div_eq _ _ hn]
  intro _
  rw [hz, hz]

/-! ## Every width -/

/-- `kernel::k8::round_magnitude_div` rounds `±un / ud`. -/
theorem k8_rmd_spec (un ud : Std.U16) (neg : Bool) (hd : 0 < ud.val)
    (hfit : 2 * un.val + 2 * ud.val < 2 ^ 16) :
    fulcrum.kernel.k8.round_magnitude_div un ud neg
      ⦃ r => r.val = roundHalfUp ((if neg then -(un.val : ℤ) else un.val : ℤ) / (ud.val : ℚ)) ⦄ := by
  unfold fulcrum.kernel.k8.round_magnitude_div
  exact rmd_shape un ud neg 1#i32 rfl rfl (Nat.one_lt_succ_succ _) hd hfit

/-- L3 on the code: `kernel::k8::mul_div` is `round(a · b / c)` for `c ≠ 0`. -/
theorem k8_mul_div_spec (a b c : Std.I8) (hc : c.val ≠ 0) :
    fulcrum.kernel.k8.mul_div a b c
      ⦃ r => r.val = roundHalfUp ((a.val * b.val : ℤ) / (c.val : ℚ)) ⦄ := by
  unfold fulcrum.kernel.k8.mul_div
  exact mul_div_shape 7 rfl rfl rfl (Nat.succ_pos _) _ I8_unsigned_abs_spec _ k8_rmd_spec 0#i8
    (fun _ => rfl) a b c hc

/-- `kernel::k16::round_magnitude_div` rounds `±un / ud`. -/
theorem k16_rmd_spec (un ud : Std.U32) (neg : Bool) (hd : 0 < ud.val)
    (hfit : 2 * un.val + 2 * ud.val < 2 ^ 32) :
    fulcrum.kernel.k16.round_magnitude_div un ud neg
      ⦃ r => r.val = roundHalfUp ((if neg then -(un.val : ℤ) else un.val : ℤ) / (ud.val : ℚ)) ⦄ := by
  unfold fulcrum.kernel.k16.round_magnitude_div
  exact rmd_shape un ud neg 1#i32 rfl rfl (Nat.one_lt_succ_succ _) hd hfit

/-- L3 on the code: `kernel::k16::mul_div` is `round(a · b / c)` for `c ≠ 0`. -/
theorem k16_mul_div_spec (a b c : Std.I16) (hc : c.val ≠ 0) :
    fulcrum.kernel.k16.mul_div a b c
      ⦃ r => r.val = roundHalfUp ((a.val * b.val : ℤ) / (c.val : ℚ)) ⦄ := by
  unfold fulcrum.kernel.k16.mul_div
  exact mul_div_shape 15 rfl rfl rfl (Nat.succ_pos _) _ I16_unsigned_abs_spec _ k16_rmd_spec 0#i16
    (fun _ => rfl) a b c hc

/-- `kernel::k32::round_magnitude_div` rounds `±un / ud`. -/
theorem k32_rmd_spec (un ud : Std.U64) (neg : Bool) (hd : 0 < ud.val)
    (hfit : 2 * un.val + 2 * ud.val < 2 ^ 64) :
    fulcrum.kernel.k32.round_magnitude_div un ud neg
      ⦃ r => r.val = roundHalfUp ((if neg then -(un.val : ℤ) else un.val : ℤ) / (ud.val : ℚ)) ⦄ := by
  unfold fulcrum.kernel.k32.round_magnitude_div
  exact rmd_shape un ud neg 1#i32 rfl rfl (Nat.one_lt_succ_succ _) hd hfit

/-- L3 on the code: `kernel::k32::mul_div` is `round(a · b / c)` for `c ≠ 0`. -/
theorem k32_mul_div_spec (a b c : Std.I32) (hc : c.val ≠ 0) :
    fulcrum.kernel.k32.mul_div a b c
      ⦃ r => r.val = roundHalfUp ((a.val * b.val : ℤ) / (c.val : ℚ)) ⦄ := by
  unfold fulcrum.kernel.k32.mul_div
  exact mul_div_shape 31 rfl rfl rfl (Nat.succ_pos _) _ I32_unsigned_abs_spec _ k32_rmd_spec 0#i32
    (fun _ => rfl) a b c hc

/-- `kernel::k64::round_magnitude_div` rounds `±un / ud`. -/
theorem k64_rmd_spec (un ud : Std.U128) (neg : Bool) (hd : 0 < ud.val)
    (hfit : 2 * un.val + 2 * ud.val < 2 ^ 128) :
    fulcrum.kernel.k64.round_magnitude_div un ud neg
      ⦃ r => r.val = roundHalfUp ((if neg then -(un.val : ℤ) else un.val : ℤ) / (ud.val : ℚ)) ⦄ := by
  unfold fulcrum.kernel.k64.round_magnitude_div
  exact rmd_shape un ud neg 1#i32 rfl rfl (Nat.one_lt_succ_succ _) hd hfit

/-- L3 on the code: `kernel::k64::mul_div` is `round(a · b / c)` for `c ≠ 0`. -/
theorem k64_mul_div_spec (a b c : Std.I64) (hc : c.val ≠ 0) :
    fulcrum.kernel.k64.mul_div a b c
      ⦃ r => r.val = roundHalfUp ((a.val * b.val : ℤ) / (c.val : ℚ)) ⦄ := by
  unfold fulcrum.kernel.k64.mul_div
  exact mul_div_shape 63 rfl rfl rfl (Nat.succ_pos _) _ I64_unsigned_abs_spec _ k64_rmd_spec 0#i64
    (fun _ => rfl) a b c hc

/-- L3 on the code: `kernel::k8::div` is `round(a · 2^4 / b)` for `b ≠ 0`. -/
theorem k8_div_spec (a b : Std.I8) (hb : b.val ≠ 0) :
    fulcrum.kernel.k8.div a b ⦃ r => r.val = roundHalfUp ((a.val * 2 ^ 4 : ℤ) / (b.val : ℚ)) ⦄ := by
  unfold fulcrum.kernel.k8.div
  exact div_shape 7 4 rfl rfl rfl (Nat.succ_pos _) (Nat.le_of_ble_eq_true rfl) _
    I8_unsigned_abs_spec _ k8_rmd_spec 0#i8 (fun _ => rfl) 4#i32 rfl a b hb

/-- L3 on the code: `kernel::k8::div_int` is `round(a / n)` for `n ≠ 0`. -/
theorem k8_div_int_spec (a n : Std.I8) (hn : n.val ≠ 0) :
    fulcrum.kernel.k8.div_int a n ⦃ r => r.val = roundHalfUp ((a.val : ℤ) / (n.val : ℚ)) ⦄ := by
  unfold fulcrum.kernel.k8.div_int
  exact div_int_shape 7 rfl rfl rfl (Nat.succ_pos _) _ I8_unsigned_abs_spec _ k8_rmd_spec 0#i8
    (fun _ => rfl) a n hn

/-- L3 on the code: `kernel::k64::div` is `round(a · 2^32 / b)` for `b ≠ 0`. -/
theorem k64_div_spec (a b : Std.I64) (hb : b.val ≠ 0) :
    fulcrum.kernel.k64.div a b ⦃ r => r.val = roundHalfUp ((a.val * 2 ^ 32 : ℤ) / (b.val : ℚ)) ⦄ := by
  unfold fulcrum.kernel.k64.div
  exact div_shape 63 32 rfl rfl rfl (Nat.succ_pos _) (Nat.le_of_ble_eq_true rfl) _
    I64_unsigned_abs_spec _ k64_rmd_spec 0#i64 (fun _ => rfl) 32#i32 rfl a b hb

/-- L3 on the code: `kernel::k64::div_int` is `round(a / n)` for `n ≠ 0`. -/
theorem k64_div_int_spec (a n : Std.I64) (hn : n.val ≠ 0) :
    fulcrum.kernel.k64.div_int a n ⦃ r => r.val = roundHalfUp ((a.val : ℤ) / (n.val : ℚ)) ⦄ := by
  unfold fulcrum.kernel.k64.div_int
  exact div_int_shape 63 rfl rfl rfl (Nat.succ_pos _) _ I64_unsigned_abs_spec _ k64_rmd_spec 0#i64
    (fun _ => rfl) a n hn

end Fulcrum

end
