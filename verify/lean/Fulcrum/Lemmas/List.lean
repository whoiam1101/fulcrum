module

public import Mathlib.Data.Nat.Notation
import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.ToDual

/-!
# List facts used by the table proofs

The loops that build `SQRT_START` and `RSQRT_START` write one entry at a
time; reading the list after a write.
-/

@[expose] public section

namespace Fulcrum

/-- Reading a list after a write inside it. -/
theorem getElem!_set_of_lt {α} [Inhabited α] (l : List α) (i j : ℕ) (a : α) (h : i < l.length) :
    (l.set i a)[j]! = if i = j then a else l[j]! := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_set, List.getElem!_eq_getElem?_getD]
  split <;> rfl

end Fulcrum

end
