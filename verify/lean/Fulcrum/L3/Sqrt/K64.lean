module

public import Fulcrum.Kernel.Funs
import Fulcrum.L3.Sqrt.K32
import Fulcrum.Lemmas.Loop
import Fulcrum.Lemmas.Nat
import Fulcrum.Lemmas.Scalar
import Fulcrum.Math.Newton

/-!
# L3: `kernel::k64::isqrt`

`isqrt(n)` of `k64`, as Aeneas extracts it, never fails and is `⌊√n⌋` on its
domain `n ≤ 3 · 2^126`: below `2^63` the `isqrt` of `k32`, otherwise the start
`(isqrt(n >> 2j) + 1) · 2^j` from the `isqrt` of `k32` on the leading bits.
Its square is above `n` by at most `2^(j+1)` times the start, so one Newton
step fits `u128` (`newton_bound`), and the square check and the final loop
step down to `⌊√n⌋` (`check_descend_spec`).
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace Fulcrum

/-- The Newton loop of `k64::isqrt`: `NEWTON_STEPS = 1`, one step from `x > 0`. -/
theorem k64_newton_spec (n x : Std.U128) (hx : 0 < x.val)
    (hf : x.val + n.val / x.val ≤ UScalar.max .U128) :
    fulcrum.kernel.k64.isqrt_loop0 n x 0#u32 ⦃ r => r.val = (x.val + n.val / x.val) / 2 ⦄ := by
  unfold fulcrum.kernel.k64.isqrt_loop0
  exact newton_once_spec n x _ (by unfold fulcrum.kernel.k64.NEWTON_STEPS; rfl)
    (Nat.le_of_ble_eq_true rfl) hx hf

/-- L3 on the code: `kernel::k64::isqrt` is `⌊√n⌋` for `n ≤ 3 · 2^126`: below `2^63` the
`isqrt` of `k32`, otherwise one Newton step from `(isqrt(n >> 2j) + 1) · 2^j`. -/
theorem k64_isqrt_spec (n : Std.U128) (hn : n.val ≤ 3 * 2 ^ 126) :
    fulcrum.kernel.k64.isqrt n ⦃ r => r.val = Nat.sqrt n.val ⦄ := by
  unfold fulcrum.kernel.k64.isqrt
  by_cases h2 : n < 2#u128
  · rw [ite_eq_left h2, WP.spec_ok]
    exact sqrt_eq_self_of_lt_two n.val h2
  rw [ite_eq_right h2]
  have hn2 : 2 ≤ n.val := Nat.le_of_not_lt h2
  obtain ⟨L, hL⟩ : ∃ L, L = Nat.log 2 n.val := ⟨_, rfl⟩
  have hlo : 2 ^ L ≤ n.val := hL ▸ Nat.pow_log_le_self 2 (Nat.ne_zero_of_lt hn2)
  have hhi : n.val < 2 ^ (L + 1) := hL ▸ Nat.lt_pow_succ_log_self Nat.one_lt_two _
  have L127 : L ≤ 127 := Nat.le_of_lt_succ ((Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp
    (hlo.trans_lt (hn.trans_lt (Nat.le_of_ble_eq_true rfl))))
  have hlz : (core.num.U128.leading_zeros n).val = 128 - Nat.log 2 n.val - 1 :=
    leading_zeros_val n (Nat.ne_zero_of_lt hn2) (Nat.le_of_ble_eq_true rfl)
  rw [← hL] at hlz
  rw [lift, bind_ok]
  refine WP.spec_bind (UScalar.sub_spec (x := core.num.U128.BITS) (y := core.num.U128.leading_zeros n)
    (by rw [hlz, show core.num.U128.BITS.val = 128 from rfl]; omega)) fun bits ⟨hbits, _⟩ => ?_
  rw [hlz, show core.num.U128.BITS.val = 128 from rfl] at hbits
  refine WP.spec_bind (UScalar.sub_spec (x := core.num.U64.BITS) (y := 1#u32)
    (by rw [show core.num.U64.BITS.val = 64 from rfl, lit_val];
        omega)) fun low ⟨hlow, _⟩ => ?_
  rw [show core.num.U64.BITS.val = 64 from rfl, lit_val] at hlow
  by_cases hs : bits ≤ low
  · have hs' : L + 1 ≤ 63 := by have : bits.val ≤ low.val := hs; omega
    rw [ite_eq_left hs, lift, bind_ok]
    have n63 : n.val < 2 ^ 63 := hhi.trans_le (Nat.pow_le_pow_right two_pos hs')
    have c1 : (UScalar.cast .U64 n).val = n.val :=
      UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (n63.trans (Nat.le_of_ble_eq_true rfl))
    refine WP.spec_bind (k32_isqrt_spec _ (by rw [c1]; exact n63.le.trans (Nat.le_of_ble_eq_true rfl)))
      fun r hr => ?_
    rw [WP.spec_ok, UScalar.cast_val_mod_pow_greater_numBits_eq _ _ (Nat.le_of_ble_eq_true rfl), hr,
      c1]
  have hs' : 64 ≤ L + 1 := by have : ¬ bits.val ≤ low.val := hs; omega
  rw [ite_eq_right hs]
  refine WP.spec_bind (UScalar.sub_spec (x := bits) (y := low) (by omega)) fun i1 ⟨hi1, _⟩ => ?_
  refine WP.spec_bind (UScalar.add_spec (x := i1) (y := 1#u32)
    (by rw [lit_val, U32_max_val]; omega))
    fun i2 hi2 => ?_
  rw [lit_val] at hi2
  obtain ⟨j, hj, hjv⟩ := UScalar.div_spec i2 (y := 2#u32) (Nat.succ_ne_zero _)
  rw [hj, bind_ok]
  rw [hi2, hi1, hbits, hlow, lit_val] at hjv
  have jv : j.val = (L - 61) / 2 := by omega
  refine WP.spec_bind (UScalar.mul_spec (x := 2#u32) (y := j)
    (by rw [lit_val, U32_max_val]; omega))
    fun i3 hi3 => ?_
  rw [lit_val] at hi3
  refine WP.spec_bind (UScalar.ShiftRight_spec n i3 (by rw [hi3, UScalarTy.U128_numBits_eq]; omega))
    fun i4 ⟨hi4, _⟩ => ?_
  rw [hi3, Nat.shiftRight_eq_div_pow] at hi4
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = 2 ^ j.val := ⟨_, rfl⟩
  have QQ : 2 ^ (2 * j.val) = Q * Q := by rw [hQ, two_mul, pow_add]
  obtain ⟨n'1, n'2⟩ := div_pow_bounds hi4
  rw [QQ] at n'1 n'2
  have n'63 : i4.val < 2 ^ 63 := by
    rw [hi4, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    calc n.val < 2 ^ (L + 1) := hhi
      _ ≤ 2 ^ (63 + 2 * j.val) := Nat.pow_le_pow_right two_pos (by omega)
      _ = 2 ^ 63 * 2 ^ (2 * j.val) := pow_add _ _ _
  have Q33 : Q ≤ 2 ^ 33 := by rw [hQ]; exact Nat.pow_le_pow_right two_pos (by omega)
  rw [lift, bind_ok]
  have c4 : (UScalar.cast .U64 i4).val = i4.val :=
    UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (n'63.trans (Nat.le_of_ble_eq_true rfl))
  refine WP.spec_bind (k32_isqrt_spec _ (by rw [c4]; exact n'63.le.trans (Nat.le_of_ble_eq_true rfl)))
    fun r hr => ?_
  rw [c4] at hr
  rw [lift, bind_ok]
  have r32 : r.val < 2 ^ 32 := by rw [hr]; exact Nat.sqrt_lt'.mpr (n'63.trans (Nat.le_of_ble_eq_true rfl))
  have c7 : (UScalar.cast .U128 r).val = r.val :=
    UScalar.cast_val_mod_pow_greater_numBits_eq _ _ (Nat.le_of_ble_eq_true rfl)
  refine WP.spec_bind (UScalar.add_spec (x := UScalar.cast .U128 r) (y := 1#u128)
    (by rw [c7, lit_val, U128_max_val]; omega)) fun i8 hi8 => ?_
  rw [c7, lit_val] at hi8
  refine WP.spec_bind (UScalar.ShiftLeft_spec i8 j _ (by rw [UScalarTy.U128_numBits_eq]; omega) rfl)
    fun x ⟨hx, _⟩ => ?_
  have xv : x.val = (r.val + 1) * Q := by
    rw [hx, hi8, Nat.shiftLeft_eq, ← hQ, UScalar.size_def, UScalarTy.U128_numBits_eq]
    exact Nat.mod_eq_of_lt (calc (r.val + 1) * Q ≤ 2 ^ 32 * 2 ^ 33 := Nat.mul_le_mul r32 Q33
      _ < 2 ^ 128 := Nat.le_of_ble_eq_true rfl)
  have rs1 : r.val * r.val ≤ i4.val := hr ▸ Nat.sqrt_le _
  have rs2 : i4.val < (r.val + 1) * (r.val + 1) := hr ▸ Nat.lt_succ_sqrt _
  have Q0 : 0 < Q := (Nat.two_pow_pos _).trans_eq hQ.symm
  have up : n.val < x.val * x.val := by
    rw [xv]
    calc n.val < (i4.val + 1) * (Q * Q) := n'2
      _ ≤ ((r.val + 1) * (r.val + 1)) * (Q * Q) := Nat.mul_le_mul_right _ rs2
      _ = (r.val + 1) * Q * ((r.val + 1) * Q) := by ring
  have gu : x.val * x.val ≤ n.val + (2 ^ 64 - 2) * x.val := by
    rw [xv]
    have e : (r.val + 1) * Q * ((r.val + 1) * Q) = r.val * r.val * (Q * Q) + (2 * r.val + 1) * (Q * Q) := by ring
    have h1 : r.val * r.val * (Q * Q) ≤ n.val := (Nat.mul_le_mul_right _ rs1).trans n'1
    have h2 : (2 * r.val + 1) * (Q * Q) ≤ (2 ^ 64 - 2) * ((r.val + 1) * Q) := by
      calc (2 * r.val + 1) * (Q * Q) ≤ (2 * (r.val + 1) * Q) * Q := by
            have : (2 * r.val + 1) * (Q * Q) = (2 * r.val + 1) * Q * Q := by ring
            rw [this]; exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.le_succ _))
        _ = (2 * Q) * ((r.val + 1) * Q) := by ring
        _ ≤ (2 ^ 64 - 2) * ((r.val + 1) * Q) :=
          Nat.mul_le_mul_right _ ((Nat.mul_le_mul_left 2 Q33).trans (Nat.le_of_ble_eq_true rfl))
    omega
  have g1 : 1 ≤ x.val := by rw [xv]; exact Nat.mul_pos (Nat.succ_pos _) Q0
  have nb := newton_bound n.val x.val (2 ^ 64 - 2) g1 gu (up.le.trans (Nat.le_add_right _ _))
  have x65 : x.val ≤ 2 ^ 65 := by
    rw [xv]; exact (Nat.mul_le_mul r32 Q33).trans (Nat.le_of_ble_eq_true rfl)
  refine WP.spec_bind (k64_newton_spec n x g1 (by rw [U128_max_val]; omega)) fun x1 hx1 => ?_
  have ge := sqrt_le_newton n.val x.val g1
  rw [← hx1] at ge nb
  unfold fulcrum.kernel.k64.isqrt_loop1
  exact check_descend_spec n x1 1#u128 rfl ge (by rw [U128_max_val]; omega)

end Fulcrum

end
