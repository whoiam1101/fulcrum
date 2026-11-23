module

public import Fulcrum.Math.Round
public import Fulcrum.Kernel.Funs

/-!
# L1: `kernel::magnitude_rounds_up`

The rounding rule of the crate on a sign and a magnitude, as Aeneas extracts
it: given the first dropped bit and whether a later one is set, it never fails
and says exactly when the magnitude goes up by one for rounding to nearest
with ties toward `+∞`. The math is `roundHalfUp_sign_magnitude` in
`Math/Round.lean`.
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace Fulcrum

/-- L1 on the code: `kernel::magnitude_rounds_up` of the sign, the first
dropped bit `2^k ≤ r` and the sticky bits `r mod 2^k ≠ 0` of a value
`±(m · 2^(k+1) + r)` with `r < 2^(k+1)`: the magnitude `m` plus the answer, with
the sign, is the value divided by `2^(k+1)` rounded to nearest, ties toward
`+∞`. -/
theorem magnitude_rounds_up_spec (negative : Bool) (m r : ℤ) (k : ℕ) (h0 : 0 ≤ r)
    (h1 : r < 2 ^ (k + 1)) :
    fulcrum.kernel.magnitude_rounds_up negative (decide (2 ^ k ≤ r)) (decide (r % 2 ^ k ≠ 0))
      ⦃ up => roundHalfUp (exact (k + 1) ((if negative then -1 else 1) * (m * 2 ^ (k + 1) + r))) =
        (if negative then -1 else 1) * (m + up.toInt) ⦄ := by
  have e : ∀ n h s, fulcrum.kernel.magnitude_rounds_up n h s = ok (h && (!n || s)) := by
    intro n h s; cases n <;> cases h <;> rfl
  rw [e, WP.spec_ok]
  exact roundHalfUp_sign_magnitude negative m r k h0 h1

end Fulcrum

end
