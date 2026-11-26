module

public import Fulcrum.Kernel.Funs
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Fulcrum.Tables.Exp

/-!
# The table `LOG2` of `src/tables/exp.rs`, within half a unit

Every entry `k < 256` is `log₂ (1 + k/256) · 2^62` correctly rounded: `log2_near` with 20 terms
of the series of `log (1 + x) - log (1 - x)`, the kernel checks all entries at once
(`decide +kernel`).
-/

@[expose] public section

open Aeneas Aeneas.Std

namespace Fulcrum

/-- `LOG2` is `log₂ (1 + k/256) · 2^62` rounded to nearest at every `k < 256`. -/
theorem log2_entry (k : ℕ) (hk : k < 256) :
    |((fulcrum.tables.exp.LOG2.val[k]!).val : ℝ) - Real.logb 2 (1 + (k : ℝ) / 256) * 2 ^ 62| ≤
      1 / 2 := by
  have all : ∀ k : ℕ, k < 256 → (|(k / (512 + k) : ℚ)| < 1 ∧ |logSum (k / (512 + k)) 20| ≤ 2 ∧
      |((fulcrum.tables.exp.LOG2.val[k]!).val : ℚ) - logSum (k / (512 + k)) 20 / ln2Q * 2 ^ 62| +
        (2 * logRem (k / (512 + k)) 20 + 5 / 2 ^ 270) * 2 ^ 62 ≤ 1 / 2) := by decide +kernel
  have ⟨hx, hS, h⟩ := all k hk
  exact entry_near _ 62 _ _ _ (log2_near k 20 hx hS) h

end Fulcrum

end
