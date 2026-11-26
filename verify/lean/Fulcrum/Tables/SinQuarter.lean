module

public import Fulcrum.Kernel.Funs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Fulcrum.Math.Series
import Fulcrum.Tables.Trig
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The table `SIN_QUARTER` of `src/tables/trig.rs`, within half a unit

Every entry `k ≤ 256` is `sin (k/256 · π/2) · 2^62` correctly rounded: 12 terms of the series of
`sin` at `k · piQ / 512` and the `1`-Lipschitz bound (`table_angle_near`), the kernel checks all
entries at once (`decide +kernel`).
-/

@[expose] public section

open Aeneas Aeneas.Std

namespace Fulcrum

/-- `SIN_QUARTER` is `sin(k/256 · π/2) · 2^62` rounded to nearest at every `k ≤ 256`. -/
theorem sin_quarter_entry (k : ℕ) (hk : k < 257) :
    |((fulcrum.tables.trig.SIN_QUARTER.val[k]!).val : ℝ) - Real.sin (k / 256 * (Real.pi / 2)) * 2 ^ 62| ≤
      1 / 2 := by
  have all : ∀ k : ℕ, k < 257 → ((k * piQ / 512) ^ 2 < (2 * 12 + 2) ^ 2 ∧
      |((fulcrum.tables.trig.SIN_QUARTER.val[k]!).val : ℚ) - sinSum (k * piQ / 512) 12 * 2 ^ 62| +
        (sinRem (k * piQ / 512) 12 + 1 / 2 ^ 270) * 2 ^ 62 ≤ 1 / 2) := by decide +kernel
  have ⟨hq, h⟩ := all k hk
  refine entry_near _ 62 _ _ _ ?_ h
  have s := sin_near (k * piQ / 512) 12 (by exact_mod_cast hq)
  have l := (Real.abs_sin_sub_sin_le ((k : ℝ) / 256 * (Real.pi / 2)) ((k * piQ / 512 : ℚ) : ℝ)).trans
    (table_angle_near k (by omega))
  push_cast at s l ⊢
  exact (abs_sub_le _ _ _).trans ((add_le_add l s).trans_eq (add_comm _ _))

end Fulcrum

end
