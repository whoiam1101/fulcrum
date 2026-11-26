module

public import Fulcrum.Kernel.Funs
import Fulcrum.L3.Sqrt.Common
import Fulcrum.Lemmas.Loop
import Fulcrum.Lemmas.Nat
import Fulcrum.Lemmas.Scalar

/-!
# L3: `kernel::k8::isqrt`

`isqrt(n)` of `k8`, as Aeneas extracts it, never fails and is `⌊√n⌋` on its
domain `n ≤ 3 · 2^14`, by the same steps as `k16` with the half width
`P = 2^8`: the start from `SQRT_START` (`start_lookup_spec`), one Newton step
whose square fits `u16`, and the final loop down to `⌊√n⌋`
(`start_tail_spec`).
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace Fulcrum

/-- The Newton loop of `k8::isqrt`: `NEWTON_STEPS = 1`, one step from `x > 0`. -/
theorem k8_newton_spec (n x : Std.U16) (hx : 0 < x.val)
    (hf : x.val + n.val / x.val ≤ UScalar.max .U16) :
    fulcrum.kernel.k8.isqrt_loop0 n x 0#u32 ⦃ r => r.val = (x.val + n.val / x.val) / 2 ⦄ := by
  unfold fulcrum.kernel.k8.isqrt_loop0
  exact newton_once_spec n x _ (by unfold fulcrum.kernel.k8.NEWTON_STEPS; rfl) (Nat.le_of_ble_eq_true rfl) hx hf

/-- L3 on the code: `kernel::k8::isqrt` is `⌊√n⌋` for `n ≤ 3 · 2^14`. -/
theorem k8_isqrt_spec (n : Std.U16) (hn : n.val ≤ 3 * 2 ^ 14) :
    fulcrum.kernel.k8.isqrt n ⦃ r => r.val = Nat.sqrt n.val ⦄ := by
  unfold fulcrum.kernel.k8.isqrt
  by_cases h2 : n < 2#u16
  · rw [ite_eq_left h2, WP.spec_ok]
    exact sqrt_eq_self_of_lt_two n.val h2
  rw [ite_eq_right h2, lift, bind_ok]
  have hn2 : 2 ≤ n.val := le_of_not_gt h2
  refine start_lookup_spec n core.num.U16.BITS _ _ _ (Nat.le_of_ble_eq_true rfl) rfl hn2
    (leading_zeros_val n (Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.two_pos hn2))
      (Nat.le_of_ble_eq_true rfl))
    fun j t hj ht => ?_
  unfold fulcrum.kernel.k8.isqrt_loop1
  exact start_tail_spec n t 1#u16 j (fun x => fulcrum.kernel.k8.isqrt_loop0 n x 0#u32) (2 ^ 8)
    (Nat.le_of_ble_eq_true rfl) rfl (Nat.le_of_ble_eq_true rfl) hn2 (Nat.mul_le_mul_left 4 hn)
    (by rw [U16_max_val]; exact Nat.le_of_ble_eq_true rfl)
    (by rw [U16_max_val]; exact Nat.le_of_ble_eq_true rfl) hj ht (k8_newton_spec n)

end Fulcrum

end
