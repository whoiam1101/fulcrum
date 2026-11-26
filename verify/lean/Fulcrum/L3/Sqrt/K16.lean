module

public import Fulcrum.Kernel.Funs
import Fulcrum.L3.Sqrt.Common
import Fulcrum.Lemmas.Loop
import Fulcrum.Lemmas.Nat
import Fulcrum.Lemmas.Scalar

/-!
# L3: `kernel::k16::isqrt`

`isqrt(n)` of `k16`, as Aeneas extracts it, never fails and is `⌊√n⌋` on its
domain `n ≤ 3 · 2^30`. The start is `SQRT_START` at the leading bits of `n`
taken in pairs (`start_lookup_spec`); with the half width `P = 2^16` its square
is close to `n`, so the square of one Newton step fits `u32`, and the final
loop steps down to `⌊√n⌋` exactly (`start_tail_spec`).
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace Fulcrum

/-- The Newton loop of `k16::isqrt`: `NEWTON_STEPS = 1`, one step from `x > 0`. -/
theorem k16_newton_spec (n x : Std.U32) (hx : 0 < x.val)
    (hf : x.val + n.val / x.val ≤ UScalar.max .U32) :
    fulcrum.kernel.k16.isqrt_loop0 n x 0#u32 ⦃ r => r.val = (x.val + n.val / x.val) / 2 ⦄ := by
  unfold fulcrum.kernel.k16.isqrt_loop0
  exact newton_once_spec n x _ (by unfold fulcrum.kernel.k16.NEWTON_STEPS; rfl) (Nat.le_of_ble_eq_true rfl) hx hf

/-- L3 on the code: `kernel::k16::isqrt` is `⌊√n⌋` for `n ≤ 3 · 2^30`. -/
theorem k16_isqrt_spec (n : Std.U32) (hn : n.val ≤ 3 * 2 ^ 30) :
    fulcrum.kernel.k16.isqrt n ⦃ r => r.val = Nat.sqrt n.val ⦄ := by
  unfold fulcrum.kernel.k16.isqrt
  by_cases h2 : n < 2#u32
  · rw [ite_eq_left h2, WP.spec_ok]
    exact sqrt_eq_self_of_lt_two n.val h2
  rw [ite_eq_right h2, lift, bind_ok]
  have hn2 : 2 ≤ n.val := le_of_not_gt h2
  refine start_lookup_spec n core.num.U32.BITS _ _ _ (Nat.le_of_ble_eq_true rfl) rfl hn2
    (leading_zeros_val n (Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.two_pos hn2))
      (Nat.le_of_ble_eq_true rfl))
    fun j t hj ht => ?_
  rw [lift, bind_ok]
  unfold fulcrum.kernel.k16.isqrt_loop1
  have c : (UScalar.cast .U32 t).val = t.val :=
    UScalar.cast_val_mod_pow_greater_numBits_eq _ t (Nat.le_of_ble_eq_true rfl)
  exact start_tail_spec n (UScalar.cast .U32 t) 1#u32 j
    (fun x => fulcrum.kernel.k16.isqrt_loop0 n x 0#u32) (2 ^ 16) (Nat.le_of_ble_eq_true rfl) rfl
    (Nat.le_of_ble_eq_true rfl) hn2 (Nat.mul_le_mul_left 4 hn)
    (by rw [U32_max_val]; exact Nat.le_of_ble_eq_true rfl)
    (by rw [U32_max_val]; exact Nat.le_of_ble_eq_true rfl) hj (c.trans ht) (k16_newton_spec n)

end Fulcrum

end
