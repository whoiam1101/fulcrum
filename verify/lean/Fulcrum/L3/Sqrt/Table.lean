module

public import Fulcrum.Kernel.Funs
import Fulcrum.Lemmas.List
import Fulcrum.Lemmas.Scalar

/-!
# L3: the table `SQRT_START`

The table of `isqrt` of `k8` and `k16`, built by the compiler, is
`⌊√((2t + 1) · 2^15)⌋` at every `t < 256` (`sqrt_start_spec`): its inner loop
steps up to the root (`ascend_spec`).
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace Fulcrum

/-- The inner loop of `sqrt_start`: from `s ≤ ⌊√v⌋`, step up while `(s+1)² ≤ v`. -/
theorem ascend_spec (s v : Std.U32) (hs : Nat.sqrt v.val ≤ 2 ^ 15)
    (h : s.val ≤ Nat.sqrt v.val) :
    fulcrum.kernel.sqrt_start_loop0_loop0 s v ⦃ r => r.val = Nat.sqrt v.val ⦄ := by
  unfold fulcrum.kernel.sqrt_start_loop0_loop0
  refine loop.spec_decr_nat (fun y => Nat.sqrt v.val + 1 - y.val)
    (fun y => y.val ≤ Nat.sqrt v.val) _ _ s ?_ h
  intro y hy
  unfold fulcrum.kernel.sqrt_start_loop0_loop0.body
  refine WP.spec_bind (UScalar.add_spec (x := y) (y := 1#u32)
    (by rw [lit_val, U32_max_val]; exact Nat.succ_le_of_lt ((hy.trans hs).trans_lt (Nat.le_of_ble_eq_true rfl))))
    fun i hi => ?_
  rw [lit_val] at hi
  have i15 : i.val ≤ 2 ^ 15 + 1 := hi ▸ Nat.succ_le_succ (hy.trans hs)
  refine WP.spec_bind (UScalar.mul_spec (x := i) (y := i)
    (by rw [U32_max_val]; exact (Nat.mul_le_mul i15 i15).trans (Nat.le_of_ble_eq_true rfl))) fun i1 hi1 => ?_
  by_cases hle : i1 ≤ v
  · rw [ite_eq_left hle, WP.spec_ok]
    have : i.val ≤ Nat.sqrt v.val := Nat.le_sqrt.mpr (hi1 ▸ hle)
    exact ⟨this, Nat.sub_lt_sub_left (Nat.lt_succ_of_le hy) (hi ▸ Nat.lt_succ_self _)⟩
  · rw [ite_eq_right hle, WP.spec_ok]
    have lt : v.val < i.val * i.val := hi1 ▸ not_le.mp hle
    exact Nat.eq_sqrt.mpr ⟨(Nat.le_sqrt.mp hy), hi ▸ lt⟩

/-- The table `SQRT_START`: `⌊√((2t + 1) · 2^15)⌋` at every `t < 256`. -/
theorem sqrt_start_spec :
    fulcrum.kernel.SQRT_START
      ⦃ a => ∀ t < 256, (a.val[t]!).val = Nat.sqrt ((2 * t + 1) * 2 ^ 15) ⦄ := by
  unfold fulcrum.kernel.SQRT_START fulcrum.kernel.sqrt_start fulcrum.kernel.sqrt_start_loop0
  refine loop.spec_decr_nat (fun y => 256 - y.2.1.val)
    (fun y => y.2.1.val ≤ 256 ∧
      y.2.2.val = (if y.2.1.val = 0 then 0 else Nat.sqrt ((2 * y.2.1.val - 1) * 2 ^ 15)) ∧
      (∀ t < y.2.1.val, (y.1.val[t]!).val = Nat.sqrt ((2 * t + 1) * 2 ^ 15))) _ _ _ ?_
    ⟨Nat.zero_le _, rfl, fun t ht => absurd ht (Nat.not_lt_zero t)⟩
  rintro ⟨table, t, s⟩ ⟨ht, hs, htab⟩
  unfold fulcrum.kernel.sqrt_start_loop0.body
  dsimp only at ht hs htab ⊢
  by_cases hlt : t < 256#usize
  · have hlt' : t.val < 256 := hlt
    rw [ite_eq_left hlt]
    have um := usize_max_ge
    have t2 : 2 * t.val + 1 ≤ 2 * 256 + 1 := Nat.succ_le_succ (Nat.mul_le_mul_left 2 hlt'.le)
    have h513 : 2 * 256 + 1 ≤ UScalar.max .Usize :=
      (show 2 * 256 + 1 ≤ 2 ^ 32 - 1 from Nat.le_of_ble_eq_true rfl).trans um
    have t512 : 2 * t.val ≤ UScalar.max .Usize :=
      (Nat.le_succ_of_le (Nat.le_of_succ_le_succ t2)).trans h513
    refine WP.spec_bind (UScalar.mul_spec (x := 2#usize) (y := t) (by rw [lit_val]; exact t512))
      fun i hi => ?_
    refine WP.spec_bind (UScalar.add_spec (x := i) (y := 1#usize)
      (by rw [hi, lit_val, lit_val]; exact t2.trans h513)) fun i1 hi1 => ?_
    rw [lift, bind_ok]
    have c1 : (UScalar.cast .U32 i1).val = 2 * t.val + 1 := by
      rw [UScalar.cast_val_eq, hi1, hi, lit_val, lit_val, UScalarTy.U32_numBits_eq]
      exact Nat.mod_eq_of_lt (t2.trans_lt (Nat.le_of_ble_eq_true rfl))
    refine WP.spec_bind (shl_i32_spec (UScalar.cast .U32 i1) 15#i32 15 rfl
      (Nat.le_of_ble_eq_true rfl)
      (by rw [c1]; exact (Nat.mul_le_mul_right _ t2).trans_lt (Nat.le_of_ble_eq_true rfl)))
      fun v hv => ?_
    rw [c1] at hv
    have sq : Nat.sqrt v.val ≤ 2 ^ 15 :=
      (Nat.sqrt_lt'.mpr (by rw [hv]; exact (Nat.mul_le_mul_right _ t2).trans_lt (Nat.le_of_ble_eq_true rfl))).le
    have mono : s.val ≤ Nat.sqrt v.val := by
      rw [hs, hv]
      split
      · exact Nat.zero_le _
      · exact Nat.sqrt_le_sqrt (Nat.mul_le_mul_right _ ((Nat.sub_le _ _).trans (Nat.le_succ _)))
    refine WP.spec_bind (ascend_spec s v sq mono) fun s1 hs1 => ?_
    rw [lift, bind_ok]
    have c2 : (UScalar.cast .U16 s1).val = s1.val := UScalar.cast_val_mod_pow_of_inBounds_eq _ _
      (hs1 ▸ Nat.lt_of_le_of_lt sq (Nat.le_of_ble_eq_true rfl))
    refine WP.spec_bind
      (Array.update_spec table t _ (by rw [Array.length, table.property]; exact hlt'))
      fun a ha => ?_
    have t1 : t.val + 1 ≤ UScalar.max .Usize :=
      (Nat.succ_le_succ (Nat.le_mul_of_pos_left _ Nat.two_pos)).trans (t2.trans h513)
    refine WP.spec_bind (UScalar.add_spec (x := t) (y := 1#usize) (by rw [lit_val]; exact t1))
      fun t1 ht1 => ?_
    rw [WP.spec_ok]
    dsimp only
    rw [lit_val] at ht1
    refine ⟨⟨ht1 ▸ hlt', ?_, fun k hk => ?_⟩,
      Nat.sub_lt_sub_left hlt' (ht1 ▸ Nat.lt_succ_self _)⟩
    · rw [ite_eq_right (ht1 ▸ Nat.succ_ne_zero _), hs1, hv, ht1]
      congr 2
    · rw [ha, Array.set_val_eq, getElem!_set_of_lt _ _ _ _ (by rw [table.property]; exact hlt')]
      split
      · next e => rw [c2, hs1, hv, e]
      · next e =>
        exact htab k (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ (hk.trans_eq ht1)) (Ne.symm e))
  · rw [ite_eq_right hlt, WP.spec_ok]
    exact fun k hk => htab k (hk.trans_le (le_of_not_gt hlt))

end Fulcrum

end
