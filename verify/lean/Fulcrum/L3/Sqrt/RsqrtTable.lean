module

public import Fulcrum.Lemmas.List
public import Fulcrum.Lemmas.Scalar

/-!
# L3: the table `RSQRT_START`

The table of `isqrt` of `k32`, built by bisection, is at `t - 64` the largest
`Y` with `Y² · (2t + 1) ≤ 2^71`, for every leading byte `t ∈ [64, 256)`
(`rsqrt_start_spec`).
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace Fulcrum

/-- The bisection of `rsqrt_start`: the largest `y` with `y² · d ≤ 2^71`. -/
theorem bisect_spec (d lo hi : Std.U128) (hd : d.val ≤ 511) (hlt : lo.val < hi.val)
    (hh : hi.val ≤ 2 ^ 33) (hl : lo.val * lo.val * d.val ≤ 2 ^ 71)
    (hu : 2 ^ 71 < hi.val * hi.val * d.val) :
    fulcrum.kernel.rsqrt_start_loop0_loop0 d lo hi ⦃ r =>
      r.val * r.val * d.val ≤ 2 ^ 71 ∧ 2 ^ 71 < (r.val + 1) * (r.val + 1) * d.val ⦄ := by
  unfold fulcrum.kernel.rsqrt_start_loop0_loop0
  refine loop.spec_decr_nat (fun y => y.2.val - y.1.val)
    (fun y => y.1.val < y.2.val ∧ y.2.val ≤ 2 ^ 33 ∧ y.1.val * y.1.val * d.val ≤ 2 ^ 71 ∧
      2 ^ 71 < y.2.val * y.2.val * d.val) _ _ _ ?_ ⟨hlt, hh, hl, hu⟩
  rintro ⟨l, h⟩ ⟨i1, i2, i3, i4⟩
  unfold fulcrum.kernel.rsqrt_start_loop0_loop0.body
  dsimp only at i1 i2 i3 i4 ⊢
  refine WP.spec_bind (UScalar.sub_spec (x := h) (y := l) i1.le) fun w ⟨hw, _⟩ => ?_
  by_cases hg : w > 1#u128
  · have hg' : 1 < h.val - l.val := hw ▸ hg
    rw [ite_eq_left hg]
    refine WP.spec_bind (UScalar.add_spec (x := l) (y := h) (by rw [U128_max_val]; omega)) fun s hs => ?_
    obtain ⟨mid, hm, hmv⟩ := UScalar.div_spec s (y := 2#u128) (Nat.succ_ne_zero _)
    rw [hm, bind_ok]
    rw [hs, lit_val] at hmv
    have m33 : mid.val ≤ 2 ^ 33 := by omega
    have mm : mid.val * mid.val ≤ 2 ^ 33 * 2 ^ 33 := Nat.mul_le_mul m33 m33
    refine WP.spec_bind (UScalar.mul_spec (x := mid) (y := mid)
      (by rw [U128_max_val]; exact mm.trans (Nat.le_of_ble_eq_true rfl)))
      fun p hp => ?_
    have pd : p.val * d.val ≤ 2 ^ 33 * 2 ^ 33 * 511 := hp ▸ Nat.mul_le_mul mm hd
    refine WP.spec_bind (UScalar.mul_spec (x := p) (y := d)
      (by rw [U128_max_val]; exact pd.trans (Nat.le_of_ble_eq_true rfl))) fun q hq => ?_
    refine WP.spec_bind (shl_i32_spec 1#u128 71#i32 71 rfl (Nat.le_of_ble_eq_true rfl)
      (by rw [lit_val]; exact Nat.le_of_ble_eq_true rfl)) fun k hk' => ?_
    rw [lit_val, one_mul] at hk'
    by_cases hc : q ≤ k
    · have hc' : mid.val * mid.val * d.val ≤ 2 ^ 71 := by rw [← hp, ← hq, ← hk']; exact hc
      rw [ite_eq_left hc, WP.spec_ok]
      dsimp only
      exact ⟨⟨by omega, i2, hc', i4⟩, by omega⟩
    · have hc' : 2 ^ 71 < mid.val * mid.val * d.val := by
        rw [← hp, ← hq, ← hk']; exact not_le.mp hc
      rw [ite_eq_right hc, WP.spec_ok]
      dsimp only
      exact ⟨⟨by omega, by omega, i3, hc'⟩, by omega⟩
  · have hg' : h.val - l.val ≤ 1 := hw ▸ not_lt.mp hg
    rw [ite_eq_right hg, WP.spec_ok]
    have e : h.val = l.val + 1 := by omega
    exact ⟨i3, e ▸ i4⟩

/-- The table `RSQRT_START`: at `t - 64` the largest `y` with `y² · (2t + 1) ≤ 2^71`. -/
theorem rsqrt_start_spec :
    fulcrum.kernel.RSQRT_START ⦃ a => ∀ k < 192,
      (a.val[k]!).val * (a.val[k]!).val * (2 * (k + 64) + 1) ≤ 2 ^ 71 ∧
      2 ^ 71 < ((a.val[k]!).val + 1) * ((a.val[k]!).val + 1) * (2 * (k + 64) + 1) ⦄ := by
  unfold fulcrum.kernel.RSQRT_START fulcrum.kernel.rsqrt_start fulcrum.kernel.rsqrt_start_loop0
  refine loop.spec_decr_nat (fun y => 256 - y.2.val)
    (fun y => 64 ≤ y.2.val ∧ y.2.val ≤ 256 ∧ ∀ k < y.2.val - 64,
      (y.1.val[k]!).val * (y.1.val[k]!).val * (2 * (k + 64) + 1) ≤ 2 ^ 71 ∧
      2 ^ 71 < ((y.1.val[k]!).val + 1) * ((y.1.val[k]!).val + 1) * (2 * (k + 64) + 1))
    _ _ _ ?_ ⟨le_refl _, Nat.le_of_ble_eq_true rfl, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  rintro ⟨table, t⟩ ⟨h64, ht, htab⟩
  unfold fulcrum.kernel.rsqrt_start_loop0.body
  dsimp only at h64 ht htab ⊢
  by_cases hlt : t < 256#usize
  · have hlt' : t.val < 256 := hlt
    rw [ite_eq_left hlt]
    have um := usize_max_ge
    refine WP.spec_bind (UScalar.mul_spec (x := 2#usize) (y := t) (by rw [lit_val]; omega))
      fun i hi => ?_
    refine WP.spec_bind (UScalar.add_spec (x := i) (y := 1#usize) (by rw [hi, lit_val, lit_val]; omega))
      fun i1 hi1 => ?_
    rw [lift, bind_ok]
    have cd : (UScalar.cast .U128 i1).val = 2 * t.val + 1 := by
      rw [UScalar.cast_val_eq, hi1, hi, lit_val, lit_val, UScalarTy.U128_numBits_eq]
      exact Nat.mod_eq_of_lt (by omega)
    refine WP.spec_bind (shl_i32_spec 1#u128 33#i32 33 rfl (Nat.le_of_ble_eq_true rfl)
      (by rw [lit_val]; exact Nat.le_of_ble_eq_true rfl)) fun hi0 hh0' => ?_
    rw [lit_val, one_mul] at hh0'
    have big : 2 ^ 71 < 2 ^ 33 * 2 ^ 33 * (2 * t.val + 1) :=
      calc 2 ^ 71 < 2 ^ 33 * 2 ^ 33 * 129 := Nat.le_of_ble_eq_true rfl
        _ ≤ 2 ^ 33 * 2 ^ 33 * (2 * t.val + 1) := Nat.mul_le_mul_left _ (by omega)
    refine WP.spec_bind (bisect_spec _ 0#u128 hi0 (by rw [cd]; omega)
      (by rw [hh0']; exact Nat.le_of_ble_eq_true rfl) (by rw [hh0']) (by rw [lit_val, zero_mul, zero_mul]; exact pow_nonneg zero_le_two _)
      (by rw [hh0', cd]; exact big)) fun lo ⟨l1, l2⟩ => ?_
    rw [cd] at l1 l2
    refine WP.spec_bind (UScalar.sub_spec (x := t) (y := 64#usize) h64) fun i2 ⟨hi2, _⟩ => ?_
    rw [lit_val] at hi2
    rw [lift, bind_ok]
    have l32 : lo.val < 2 ^ 32 := by
      have : lo.val * lo.val * 129 ≤ lo.val * lo.val * (2 * t.val + 1) :=
        Nat.mul_le_mul_left _ (by omega)
      exact Nat.mul_self_lt_mul_self_iff.mp (Nat.lt_of_mul_lt_mul_right
        ((this.trans l1).trans_lt (Nat.le_of_ble_eq_true rfl : 2 ^ 71 < 2 ^ 32 * 2 ^ 32 * 129)))
    have c32 : (UScalar.cast .U32 lo).val = lo.val :=
      UScalar.cast_val_mod_pow_of_inBounds_eq _ _ l32
    refine WP.spec_bind (Array.update_spec table i2 _
      (by rw [Array.length, table.property, hi2]; show t.val - 64 < 192; omega)) fun a ha => ?_
    refine WP.spec_bind (UScalar.add_spec (x := t) (y := 1#usize) (by rw [lit_val]; omega))
      fun t1 ht1 => ?_
    rw [WP.spec_ok]
    dsimp only
    rw [lit_val] at ht1
    refine ⟨⟨by omega, by omega, fun k hk => ?_⟩, by omega⟩
    rw [ha, Array.set_val_eq, getElem!_set_of_lt _ _ _ _
      (by rw [table.property, hi2]; show t.val - 64 < 192; omega)]
    split
    · next e =>
      rw [c32]
      have : k + 64 = t.val := by omega
      rw [this]
      exact ⟨l1, l2⟩
    · exact htab k (by omega)
  · rw [ite_eq_right hlt, WP.spec_ok]
    have : t.val = 256 := Nat.le_antisymm ht (not_lt.mp hlt)
    exact fun k hk => htab k (by rw [this]; exact hk)

end Fulcrum

end
