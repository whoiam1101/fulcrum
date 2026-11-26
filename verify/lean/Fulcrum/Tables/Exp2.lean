module

public import Fulcrum.Kernel.Funs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Fulcrum.Tables.Exp

/-!
# The table `EXP2` of `src/tables/exp.rs`, within half a unit

Every entry `k < 256` is `2^(k/256) · 2^126` correctly rounded: `exp2_near` with 32 terms of the
series of `exp`, the kernel checks all entries at once (`decide +kernel`).
-/

@[expose] public section

open Aeneas Aeneas.Std

namespace Fulcrum

/-- `EXP2` is `2^(k/256) · 2^126` rounded to nearest at every `k < 256`. -/
theorem exp2_entry (k : ℕ) (hk : k < 256) :
    |((fulcrum.tables.exp.EXP2.val[k]!).val : ℝ) - (2 : ℝ) ^ ((k : ℝ) / 256) * 2 ^ 126| ≤ 1 / 2 := by
  have all : ∀ k : ℕ, k < 256 → (|(k * ln2Q / 256 : ℚ)| < 32 + 1 ∧
      expSum (k * ln2Q / 256) 32 + expRem (k * ln2Q / 256) 32 ≤ 3 ∧
      |((fulcrum.tables.exp.EXP2.val[k]!).val : ℚ) - expSum (k * ln2Q / 256) 32 * 2 ^ 126| +
        (expRem (k * ln2Q / 256) 32 + 6 / 2 ^ 270) * 2 ^ 126 ≤ 1 / 2) := by decide +kernel
  have ⟨hq, h3, h⟩ := all k hk
  exact entry_near _ 126 _ _ _ (exp2_near k (by omega) 32 (by exact_mod_cast hq) h3) h

end Fulcrum

end
