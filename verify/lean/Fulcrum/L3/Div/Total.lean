module

public import Fulcrum.L3.Div.Signed

/-!
# L3: `kernel::div_total`

`div_total(a, b)` of every width, as Aeneas extracts it, never fails, also for
`b = 0`, and equals `div(a, b)` for `b ≠ 0`. `k8`, `k32` and `k64` branch on
`b = 0` (`div_total_shape`); `k16` divides by `b | (b == 0)`, which is `b`
for `b ≠ 0` and `1` for `b = 0` (`k16_or_zero`).
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace Fulcrum

/-- The body of `kernel::kN::div_total` with a branch: a constant for
`b = 0`, the division `d` otherwise. -/
theorem div_total_shape {B W} (b zero : IScalar B) (z : IScalar W) (hz : zero.val = 0)
    (d : Result (IScalar W)) (P : IScalar W → Prop) (hd : b.val ≠ 0 → d ⦃ P ⦄) :
    (if b = zero then ok z else d) ⦃ r => b.val ≠ 0 → P r ⦄ := by
  by_cases h : b = zero
  · rw [ite_eq_left h, WP.spec_ok]
    exact fun hb => absurd (h ▸ hz) hb
  · rw [ite_eq_right h]
    have hb : b.val ≠ 0 := fun e => h (IScalar.eq_of_val_eq (e.trans hz.symm))
    exact WP.spec_mono (hd hb) fun r hr _ => hr

/-- The divisor of `kernel::k16::div_total`: `b | (b == 0)` is `1` for `b = 0`
and `b` otherwise. -/
theorem k16_or_zero (b : Std.I16) :
    (b ||| IScalar.cast_fromBool .I16 (b = 0#i16)) = if b = 0#i16 then 1#i16 else b := by
  by_cases h : b = 0#i16
  · rw [ite_eq_left h, h]; rfl
  · rw [ite_eq_right h, decide_eq_false h]
    exact congrArg IScalar.mk ((IScalar.bv_or _ _).trans BitVec.or_zero)

/-- L3 on the code: `kernel::k8::div_total` never fails and is `div` for `b ≠ 0`. -/
theorem k8_div_total_spec (a b : Std.I8) :
    fulcrum.kernel.k8.div_total a b
      ⦃ r => b.val ≠ 0 → r.val = roundHalfUp ((a.val * 2 ^ 4 : ℤ) / (b.val : ℚ)) ⦄ := by
  unfold fulcrum.kernel.k8.div_total
  exact div_total_shape b _ _ rfl _ _ (k8_div_spec a b)

/-- L3 on the code: `kernel::k16::div_total` never fails and is `div` for `b ≠ 0`. -/
theorem k16_div_total_spec (a b : Std.I16) :
    fulcrum.kernel.k16.div_total a b
      ⦃ r => b.val ≠ 0 → r.val = roundHalfUp ((a.val * 2 ^ 8 : ℤ) / (b.val : ℚ)) ⦄ := by
  unfold fulcrum.kernel.k16.div_total
  rw [lift, bind_ok, lift, bind_ok, k16_or_zero]
  by_cases h : b = 0#i16
  · rw [ite_eq_left h]
    exact WP.spec_mono (k16_div_spec a 1#i16 one_ne_zero) fun _ _ hb => absurd (h ▸ rfl) hb
  · rw [ite_eq_right h]
    exact WP.spec_mono (k16_div_spec a b fun e => h (IScalar.eq_of_val_eq e)) fun _ hr _ => hr

/-- L3 on the code: `kernel::k32::div_total` never fails and is `div` for `b ≠ 0`. -/
theorem k32_div_total_spec (a b : Std.I32) :
    fulcrum.kernel.k32.div_total a b
      ⦃ r => b.val ≠ 0 → r.val = roundHalfUp ((a.val * 2 ^ 16 : ℤ) / (b.val : ℚ)) ⦄ := by
  unfold fulcrum.kernel.k32.div_total
  exact div_total_shape b _ _ rfl _ _ (k32_div_spec a b)

/-- L3 on the code: `kernel::k64::div_total` never fails and is `div` for `b ≠ 0`. -/
theorem k64_div_total_spec (a b : Std.I64) :
    fulcrum.kernel.k64.div_total a b
      ⦃ r => b.val ≠ 0 → r.val = roundHalfUp ((a.val * 2 ^ 32 : ℤ) / (b.val : ℚ)) ⦄ := by
  unfold fulcrum.kernel.k64.div_total
  exact div_total_shape b _ _ rfl _ _ (k64_div_spec a b)

end Fulcrum

end
