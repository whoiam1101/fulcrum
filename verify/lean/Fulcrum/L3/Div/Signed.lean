module

public import Fulcrum.L3.Div.Magnitude
public import Fulcrum.Math.Range
public import Fulcrum.Lemmas.Scalar

/-!
# L3: `div` and `div_int` of `k16` and `k32`

The signed form of `div_kernel!`: `round_div` divides `2·n + bias` by `2·d`
truncating (`tdiv_round`, `round_div_shape`), so `div` and `div_int` of `k16`
and `k32`, as Aeneas extracts them, are `round(a · 2^F / b)` and `round(a / n)`
(`div_signed_shape`, `div_int_signed_shape`).
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace Fulcrum

/-! ## The signed form -/

/-- `x << 1` doubles a signed `x` when the double fits. -/
theorem ishl_one_spec {W} (x : IScalar W) (k : ℕ) (hk : W.numBits = k + 1) (hk1 : 1 ≤ k)
    (h : InRange k (2 * x.val)) : (x <<< (1#i32 : Std.I32)) ⦃ z => z.val = 2 * x.val ⦄ := by
  have one : (1#i32 : Std.I32).val = 1 := rfl
  refine WP.spec_mono (IScalar.ShiftLeft_IScalar_spec x 1#i32 (one ▸ zero_le_one)
    (by rw [one, hk]; exact_mod_cast Nat.succ_lt_succ hk1)) fun z ⟨hz, _⟩ => ?_
  rw [hz, IScalar.toNat, one, Int.toNat_one, Int.shiftLeft_eq, pow_one, mul_comm, hk]
  exact (wrap_eq_self_iff k _).2 h

/-- The body of `kernel::kN::round_div`: `round(n / d)` for `d ≠ 0` and
`|n|, |d| < 2^j` on `j + 3` bits. -/
theorem round_div_shape {W U} (j : ℕ) (hW : W.numBits = j + 2 + 1)
    (abs : IScalar W → Result (UScalar U)) (habs : ∀ x, abs x ⦃ u => u.val = x.val.natAbs ⦄)
    (zero one : IScalar W) (hz : ∀ x : IScalar W, decide (x < zero) = decide (x.val < 0))
    (h1 : one.val = 1) (n d : IScalar W) (hd : d.val ≠ 0) (hn : n.val.natAbs < 2 ^ j)
    (hd' : d.val.natAbs < 2 ^ j) :
    (do
        let i ← abs d
        let ud ← lift (UScalar.hcast W i)
        let sd ← lift (IScalar.cast_fromBool W (d < zero))
        let bias ← if n < zero then do
            let i1 ← one - sd
            i1 - ud
          else ud - sd
        let i1 ← n <<< (1#i32 : Std.I32)
        let i2 ← i1 + bias
        let i3 ← d <<< (1#i32 : Std.I32)
        i2 / i3)
      ⦃ r => r.val = roundHalfUp ((n.val : ℚ) / d.val) ⦄ := by
  have e : (2 : ℤ) ^ (j + 2) = 4 * 2 ^ j := (pow_add 2 j 2).trans (mul_comm _ _)
  have hmin : IScalar.min W = -(4 * 2 ^ j) := by rw [min_eq_neg_pow hW, e]
  have hmax : IScalar.max W = 4 * 2 ^ j - 1 := by rw [max_eq_pow_sub_one hW, e]
  have ⟨n0, n1⟩ := lt_of_natAbs_lt hn
  have ⟨d0, d1⟩ := lt_of_natAbs_lt hd'
  have hdn : ((d.val.natAbs : ℕ) : ℤ) < 2 ^ j := by exact_mod_cast hd'
  have ⟨s0, s1⟩ := toInt_bounds (decide (d.val < 0))
  refine WP.spec_bind (habs d) fun i hi => ?_
  refine WP.spec_bind (UScalar.hcast_inBounds_spec W i (by rw [hi, hmax]; omega)) fun ud hud => ?_
  rw [lift, bind_ok]
  have hsd : (IScalar.cast_fromBool W (decide (d < zero))).val = (decide (d.val < 0)).toInt := by
    rw [IScalar.cast_fromBool_val_eq, hz d]
  have hbias : (if n < zero then do
        let i1 ← one - IScalar.cast_fromBool W (decide (d < zero))
        i1 - ud
      else ud - IScalar.cast_fromBool W (decide (d < zero)))
      ⦃ b => b.val = if n.val < 0 then 1 - (decide (d.val < 0)).toInt - d.val.natAbs
        else d.val.natAbs - (decide (d.val < 0)).toInt ⦄ := by
    have nz := decide_eq_decide.mp (hz n)
    by_cases hneg : n < zero
    · rw [ite_eq_left hneg]
      refine WP.spec_bind (IScalar.sub_spec (by rw [h1, hsd, hmin]; omega)
        (by rw [h1, hsd, hmax]; omega)) fun i1 hi1 => ?_
      refine WP.spec_mono (IScalar.sub_spec (by rw [hi1, h1, hud, hi, hsd, hmin]; omega)
        (by rw [hi1, h1, hud, hi, hsd, hmax]; omega)) fun b hb => ?_
      rw [hb, hi1, h1, hud, hi, hsd, ite_eq_left (nz.mp hneg)]
    · rw [ite_eq_right hneg]
      refine WP.spec_mono (IScalar.sub_spec (by rw [hud, hi, hsd, hmin]; omega)
        (by rw [hud, hi, hsd, hmax]; omega)) fun b hb => ?_
      rw [hb, hud, hi, hsd, ite_eq_right (mt nz.mpr hneg)]
  refine WP.spec_bind hbias fun bias hb => ?_
  have hbb : -2 ^ j ≤ bias.val ∧ bias.val ≤ 2 ^ j := by rw [hb]; split <;> omega
  have ⟨b0, b1⟩ := hbb
  refine WP.spec_bind (ishl_one_spec n (j + 2) hW (Nat.succ_pos _)
    (by unfold InRange minOf maxOf; rw [e]; omega)) fun i1 hi1 => ?_
  refine WP.spec_bind (IScalar.add_spec (x := i1) (y := bias) (by rw [hi1, hmin]; omega)
    (by rw [hi1, hmax]; omega)) fun i2 hi2 => ?_
  refine WP.spec_bind (ishl_one_spec d (j + 2) hW (Nat.succ_pos _)
    (by unfold InRange minOf maxOf; rw [e]; omega)) fun i3 hi3 => ?_
  obtain ⟨z, hz', hzv⟩ := IScalar.div_spec (x := i2) (y := i3)
    (by rw [hi3]; exact mul_ne_zero two_ne_zero hd)
    (fun ⟨h, _⟩ => by rw [hi2, hi1, hmin] at h; omega)
  rw [hz', WP.spec_ok, hzv, hi2, hi1, hi3, hb]
  exact tdiv_round n.val d.val hd

/-- `kernel::kN::div` of the signed form: `round(a · 2^F / b)` through `round_div`
on `j + 3` bits, for `a`, `b` of `s + 1` bits and `s + F < j`. -/
theorem div_signed_shape {S W} (s j F : ℕ) (hS : S.numBits = s + 1) (hW : W.numBits = j + 2 + 1)
    (hsj : s + F < j) (rd : IScalar W → IScalar W → Result (IScalar W))
    (hrd : ∀ n d : IScalar W, d.val ≠ 0 → n.val.natAbs < 2 ^ j → d.val.natAbs < 2 ^ j →
      rd n d ⦃ r => r.val = roundHalfUp ((n.val : ℚ) / d.val) ⦄)
    (f : Std.I32) (hf : f.val = F) (a b : IScalar S) (hb : b.val ≠ 0) :
    (do
        let i ← lift (IScalar.cast W a)
        let i1 ← i <<< f
        let i2 ← lift (IScalar.cast W b)
        rd i1 i2)
      ⦃ r => r.val = roundHalfUp ((a.val * 2 ^ F : ℤ) / (b.val : ℚ)) ⦄ := by
  have hsj' : s < j := Nat.lt_of_le_of_lt (Nat.le_add_right s F) hsj
  have hSW : S.numBits ≤ W.numBits := by
    rw [hS, hW]; exact Nat.succ_le_succ (Nat.le_add_right_of_le hsj'.le)
  have ca := IScalar.val_mod_pow_greater_numBits W a hSW
  have cb := IScalar.val_mod_pow_greater_numBits W b hSW
  have ha : (a.val * 2 ^ F).natAbs < 2 ^ j := by
    rw [Int.natAbs_mul, Int.natAbs_pow]
    exact lt_of_le_of_lt (Nat.mul_le_mul (natAbs_le_pow a s hS) le_rfl)
      ((pow_add 2 s F).symm ▸ Nat.pow_lt_pow_right one_lt_two hsj)
  have ⟨a0, a1⟩ := lt_of_natAbs_lt ha
  rw [lift, bind_ok]
  refine WP.spec_bind (IScalar.ShiftLeft_IScalar_spec (IScalar.cast W a) f
    (hf ▸ Int.natCast_nonneg F)
    (by rw [hf, hW]; exact Int.ofNat_lt.mpr (Nat.lt_succ_of_lt (Nat.lt_add_right 2
      (Nat.lt_of_le_of_lt (Nat.le_add_left F s) hsj))))) fun p ⟨hp, _⟩ => ?_
  have hp' : p.val = a.val * 2 ^ F := by
    rw [hp, show IScalar.toNat f = F by rw [IScalar.toNat, hf, Int.toNat_natCast], Int.shiftLeft_eq,
      ca, hW]
    refine (wrap_eq_self_iff (j + 2) _).2 ?_
    have e : (2 : ℤ) ^ (j + 2) = 4 * 2 ^ j := (pow_add 2 j 2).trans (mul_comm _ _)
    unfold InRange minOf maxOf
    rw [e]
    omega
  rw [lift, bind_ok]
  refine WP.spec_mono (hrd p _ (by rw [cb]; exact hb) (by rw [hp']; exact ha) (by
    rw [cb]; exact lt_of_le_of_lt (natAbs_le_pow b s hS) (Nat.pow_lt_pow_right one_lt_two hsj')))
    fun r hr => ?_
  rw [hr, hp', cb]

/-- `kernel::kN::div_int` of the signed form: `round(a / n)` through `round_div`
on `j + 3` bits, for `a`, `n` of `s + 1` bits and `s < j`. -/
theorem div_int_signed_shape {S W} (s j : ℕ) (hS : S.numBits = s + 1)
    (hW : W.numBits = j + 2 + 1) (hsj : s < j) (rd : IScalar W → IScalar W → Result (IScalar W))
    (hrd : ∀ n d : IScalar W, d.val ≠ 0 → n.val.natAbs < 2 ^ j → d.val.natAbs < 2 ^ j →
      rd n d ⦃ r => r.val = roundHalfUp ((n.val : ℚ) / d.val) ⦄)
    (a n : IScalar S) (hn : n.val ≠ 0) :
    (do
        let i ← lift (IScalar.cast W a)
        let i1 ← lift (IScalar.cast W n)
        rd i i1)
      ⦃ r => r.val = roundHalfUp ((a.val : ℤ) / (n.val : ℚ)) ⦄ := by
  have hSW : S.numBits ≤ W.numBits := by
    rw [hS, hW]; exact Nat.succ_le_succ (Nat.le_add_right_of_le hsj.le)
  have ca := IScalar.val_mod_pow_greater_numBits W a hSW
  have cn := IScalar.val_mod_pow_greater_numBits W n hSW
  have hp := Nat.pow_lt_pow_right one_lt_two hsj
  rw [lift, bind_ok, lift, bind_ok]
  refine WP.spec_mono (hrd _ _ (by rw [cn]; exact hn)
    (by rw [ca]; exact lt_of_le_of_lt (natAbs_le_pow a s hS) hp)
    (by rw [cn]; exact lt_of_le_of_lt (natAbs_le_pow n s hS) hp)) fun r hr => ?_
  rw [hr, ca, cn]

/-! ## `k16` and `k32` -/

/-- `kernel::k16::round_div` rounds `n / d` for `d ≠ 0` and small enough `n`, `d`. -/
theorem k16_round_div_spec (n d : Std.I32) (hd : d.val ≠ 0) (hn : n.val.natAbs < 2 ^ 29)
    (hd' : d.val.natAbs < 2 ^ 29) :
    fulcrum.kernel.k16.round_div n d ⦃ r => r.val = roundHalfUp ((n.val : ℚ) / d.val) ⦄ := by
  unfold fulcrum.kernel.k16.round_div
  exact round_div_shape 29 rfl _ I32_unsigned_abs_spec 0#i32 1#i32 (fun _ => rfl) rfl n d hd hn hd'

/-- L3 on the code: `kernel::k16::div` is `round(a · 2^8 / b)` for `b ≠ 0`. -/
theorem k16_div_spec (a b : Std.I16) (hb : b.val ≠ 0) :
    fulcrum.kernel.k16.div a b ⦃ r => r.val = roundHalfUp ((a.val * 2 ^ 8 : ℤ) / (b.val : ℚ)) ⦄ := by
  unfold fulcrum.kernel.k16.div
  exact div_signed_shape 15 29 8 rfl rfl (Nat.le_of_ble_eq_true rfl) _ k16_round_div_spec 8#i32
    rfl a b hb

/-- L3 on the code: `kernel::k16::div_int` is `round(a / n)` for `n ≠ 0`. -/
theorem k16_div_int_spec (a n : Std.I16) (hn : n.val ≠ 0) :
    fulcrum.kernel.k16.div_int a n ⦃ r => r.val = roundHalfUp ((a.val : ℤ) / (n.val : ℚ)) ⦄ := by
  unfold fulcrum.kernel.k16.div_int
  exact div_int_signed_shape 15 29 rfl rfl (Nat.le_of_ble_eq_true rfl) _ k16_round_div_spec a n hn

/-- `kernel::k32::round_div` rounds `n / d` for `d ≠ 0` and small enough `n`, `d`. -/
theorem k32_round_div_spec (n d : Std.I64) (hd : d.val ≠ 0) (hn : n.val.natAbs < 2 ^ 61)
    (hd' : d.val.natAbs < 2 ^ 61) :
    fulcrum.kernel.k32.round_div n d ⦃ r => r.val = roundHalfUp ((n.val : ℚ) / d.val) ⦄ := by
  unfold fulcrum.kernel.k32.round_div
  exact round_div_shape 61 rfl _ I64_unsigned_abs_spec 0#i64 1#i64 (fun _ => rfl) rfl n d hd hn hd'

/-- L3 on the code: `kernel::k32::div` is `round(a · 2^16 / b)` for `b ≠ 0`. -/
theorem k32_div_spec (a b : Std.I32) (hb : b.val ≠ 0) :
    fulcrum.kernel.k32.div a b ⦃ r => r.val = roundHalfUp ((a.val * 2 ^ 16 : ℤ) / (b.val : ℚ)) ⦄ := by
  unfold fulcrum.kernel.k32.div
  exact div_signed_shape 31 61 16 rfl rfl (Nat.le_of_ble_eq_true rfl) _ k32_round_div_spec 16#i32
    rfl a b hb

/-- L3 on the code: `kernel::k32::div_int` is `round(a / n)` for `n ≠ 0`. -/
theorem k32_div_int_spec (a n : Std.I32) (hn : n.val ≠ 0) :
    fulcrum.kernel.k32.div_int a n ⦃ r => r.val = roundHalfUp ((a.val : ℤ) / (n.val : ℚ)) ⦄ := by
  unfold fulcrum.kernel.k32.div_int
  exact div_int_signed_shape 31 61 rfl rfl (Nat.le_of_ble_eq_true rfl) _ k32_round_div_spec a n hn

end Fulcrum

end
