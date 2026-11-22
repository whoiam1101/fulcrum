module

public import Fulcrum.Math.Range
public import Fulcrum.Kernel.Funs

/-!
# L2: range checks of `kernel::fits`, `narrow` and `saturate`

On the code extracted by Aeneas, for `k8`..`k64`: `fits` is the comparison with
`[MIN, MAX]`, `narrow` returns `w` exactly when it fits, `saturate` is the
clamp. The models over the integers are in `Math/Range.lean`; the bodies of
every width go through `fits_shape`, `narrow_shape` and `saturate_shape`.
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace Fulcrum

/-- The body of `kernel::kN::fits`: `true` exactly when `w` is in `[lo, hi]`. -/
theorem fits_shape {W} (w lo hi : IScalar W) (k : ℕ) (hlo : lo.val = minOf k)
    (hhi : hi.val = maxOf k) :
    (do let i ← lift lo; if w ≥ i then do let i1 ← lift hi; ok (decide (w ≤ i1)) else ok false)
      ⦃ b => b = decide (InRange k w.val) ⦄ := by
  rw [lift, bind_ok]
  by_cases h : w ≥ lo
  · rw [ite_eq_left h, lift, bind_ok, WP.spec_ok]
    exact decide_eq_decide.mpr
      ⟨fun u => ⟨hlo ▸ h, hhi ▸ u⟩, fun u => show w.val ≤ hi.val from hhi ▸ u.2⟩
  · rw [ite_eq_right h, WP.spec_ok]
    exact (decide_eq_false fun u => h (show lo.val ≤ w.val from hlo ▸ u.1)).symm

/-- The body of `kernel::kN::saturate`: the clamp, given the cast to the
storage type is `wrap`. -/
theorem saturate_shape {B W} (w lo hi : IScalar W) (mn mx : IScalar B) (k : ℕ)
    (hlo : lo.val = minOf k) (hhi : hi.val = maxOf k) (hmn : mn.val = minOf k)
    (hmx : mx.val = maxOf k) (hc : (IScalar.cast B w).val = wrap k w.val) :
    (do
        let i ← lift hi
        if w > i then ok mx else do
          let i1 ← lift lo
          if w < i1 then ok mn else ok (IScalar.cast B w))
      ⦃ r => r.val = clamp k w.val ⦄ := by
  rw [lift, bind_ok, ← saturate_eq_clamp]
  unfold saturate
  by_cases h₁ : w > hi
  · rw [ite_eq_left h₁, WP.spec_ok, hmx, ite_eq_left (hhi ▸ h₁)]
  rw [ite_eq_right h₁, ite_eq_right (hhi ▸ h₁), lift, bind_ok]
  by_cases h₂ : w < lo
  · rw [ite_eq_left h₂, WP.spec_ok, hmn, ite_eq_left (hlo ▸ h₂)]
  · rw [ite_eq_right h₂, WP.spec_ok, hc, ite_eq_right (hlo ▸ h₂)]

/-- The body of `kernel::kN::narrow`: the value when `fits` says it is in range,
`none` otherwise. -/
theorem narrow_shape {B W} (f : Result Bool) (w : IScalar W) (k : ℕ)
    (hf : f ⦃ b => b = decide (InRange k w.val) ⦄)
    (hc : (IScalar.cast B w).val = wrap k w.val) :
    (do let b ← f; if b then do let i ← lift (IScalar.cast B w); ok (some i) else ok none)
      ⦃ r => r.map IScalar.val = if InRange k w.val then some w.val else none ⦄ :=
  WP.spec_bind hf fun b hb => by
    by_cases h : InRange k w.val
    · rw [hb, decide_eq_true h, ite_eq_left rfl, lift, bind_ok, WP.spec_ok, ite_eq_left h,
        Option.map_some, hc, (wrap_eq_self_iff k w.val).2 h]
    · rw [hb, decide_eq_false h, ite_eq_right Bool.false_ne_true, WP.spec_ok, ite_eq_right h,
        Option.map_none]

/-- L2 on the code: `kernel::k8::fits` is the range check of 8 bits. -/
theorem k8_fits_spec (w : Std.I16) :
    fulcrum.kernel.k8.fits w ⦃ b => b = decide (InRange 7 w.val) ⦄ :=
  fits_shape w _ _ 7 rfl rfl

/-- L2 on the code: `kernel::k8::narrow` returns `w` exactly when it fits 8 bits. -/
theorem k8_narrow_spec (w : Std.I16) :
    fulcrum.kernel.k8.narrow w
      ⦃ r => r.map IScalar.val = if InRange 7 w.val then some w.val else none ⦄ :=
  narrow_shape _ w 7 (k8_fits_spec w) (IScalar.cast_val_eq _ _)

/-- L2 on the code: `kernel::k8::saturate` is the clamp to 8 bits. -/
theorem k8_saturate_spec (w : Std.I16) :
    fulcrum.kernel.k8.saturate w ⦃ r => r.val = clamp 7 w.val ⦄ :=
  saturate_shape w _ _ _ _ 7 rfl rfl rfl rfl (IScalar.cast_val_eq _ _)

/-- L2 on the code: `kernel::k16::fits` is the range check of 16 bits. -/
theorem k16_fits_spec (w : Std.I32) :
    fulcrum.kernel.k16.fits w ⦃ b => b = decide (InRange 15 w.val) ⦄ :=
  fits_shape w _ _ 15 rfl rfl

/-- L2 on the code: `kernel::k16::narrow` returns `w` exactly when it fits 16 bits. -/
theorem k16_narrow_spec (w : Std.I32) :
    fulcrum.kernel.k16.narrow w
      ⦃ r => r.map IScalar.val = if InRange 15 w.val then some w.val else none ⦄ :=
  narrow_shape _ w 15 (k16_fits_spec w) (IScalar.cast_val_eq _ _)

/-- L2 on the code: `kernel::k16::saturate` is the clamp to 16 bits. -/
theorem k16_saturate_spec (w : Std.I32) :
    fulcrum.kernel.k16.saturate w ⦃ r => r.val = clamp 15 w.val ⦄ :=
  saturate_shape w _ _ _ _ 15 rfl rfl rfl rfl (IScalar.cast_val_eq _ _)

/-- L2 on the code: `kernel::k32::fits` is the range check of 32 bits. -/
theorem k32_fits_spec (w : Std.I64) :
    fulcrum.kernel.k32.fits w ⦃ b => b = decide (InRange 31 w.val) ⦄ :=
  fits_shape w _ _ 31 rfl rfl

/-- L2 on the code: `kernel::k32::narrow` returns `w` exactly when it fits 32 bits. -/
theorem k32_narrow_spec (w : Std.I64) :
    fulcrum.kernel.k32.narrow w
      ⦃ r => r.map IScalar.val = if InRange 31 w.val then some w.val else none ⦄ :=
  narrow_shape _ w 31 (k32_fits_spec w) (IScalar.cast_val_eq _ _)

/-- L2 on the code: `kernel::k32::saturate` is the clamp to 32 bits. -/
theorem k32_saturate_spec (w : Std.I64) :
    fulcrum.kernel.k32.saturate w ⦃ r => r.val = clamp 31 w.val ⦄ :=
  saturate_shape w _ _ _ _ 31 rfl rfl rfl rfl (IScalar.cast_val_eq _ _)

/-- L2 on the code: `kernel::k64::fits` is the range check of 64 bits. -/
theorem k64_fits_spec (w : Std.I128) :
    fulcrum.kernel.k64.fits w ⦃ b => b = decide (InRange 63 w.val) ⦄ :=
  fits_shape w _ _ 63 rfl rfl

/-- L2 on the code: `kernel::k64::narrow` returns `w` exactly when it fits 64 bits. -/
theorem k64_narrow_spec (w : Std.I128) :
    fulcrum.kernel.k64.narrow w
      ⦃ r => r.map IScalar.val = if InRange 63 w.val then some w.val else none ⦄ :=
  narrow_shape _ w 63 (k64_fits_spec w) (IScalar.cast_val_eq _ _)

/-- L2 on the code: `kernel::k64::saturate` is the clamp to 64 bits. -/
theorem k64_saturate_spec (w : Std.I128) :
    fulcrum.kernel.k64.saturate w ⦃ r => r.val = clamp 63 w.val ⦄ :=
  saturate_shape w _ _ _ _ 63 rfl rfl rfl rfl (IScalar.cast_val_eq _ _)

end Fulcrum

end
