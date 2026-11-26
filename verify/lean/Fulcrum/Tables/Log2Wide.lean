module

public import Fulcrum.Kernel.Funs
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Fulcrum.Tables.Exp

/-!
# The table `LOG2_WIDE` of `src/tables/exp.rs`, within half a unit

Every entry `k < 256` is `log₂ (1 + k/256) · 2^126` correctly rounded: `log2_near` with 40 terms
of the series of `log (1 + x) - log (1 - x)`, the kernel checks all entries at once
(`decide +kernel`).
-/

@[expose] public section

open Aeneas Aeneas.Std

namespace Fulcrum

/-- `LOG2_WIDE` is `log₂ (1 + k/256) · 2^126` rounded to nearest at every `k < 256`. -/
theorem log2_wide_entry (k : ℕ) (hk : k < 256) :
    |((fulcrum.tables.exp.LOG2_WIDE.val[k]!).val : ℝ) - Real.logb 2 (1 + (k : ℝ) / 256) * 2 ^ 126| ≤
      1 / 2 := by
  have all : ∀ k : ℕ, k < 256 → (|(k / (512 + k) : ℚ)| < 1 ∧ |logSum (k / (512 + k)) 40| ≤ 2 ∧
      |((fulcrum.tables.exp.LOG2_WIDE.val[k]!).val : ℚ) - logSum (k / (512 + k)) 40 / ln2Q * 2 ^ 126| +
        (2 * logRem (k / (512 + k)) 40 + 5 / 2 ^ 270) * 2 ^ 126 ≤ 1 / 2) := by decide +kernel
  have ⟨hx, hS, h⟩ := all k hk
  exact entry_near _ 126 _ _ _ (log2_near k 40 hx hS) h

end Fulcrum

end
