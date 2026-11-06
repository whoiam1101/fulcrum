/-!
# Specification of fulcrum (docs/ARCHITECTURE.md §6.1.1)

A fixed-point value with `n` fractional bits is an integer `raw`; its exact
value is `raw / 2^n`.
-/

namespace Fulcrum

/-- Fixed-point value with `n` fractional bits, stored as its raw integer. -/
structure Fixed (n : Nat) where
  raw : Int
  deriving DecidableEq, Repr

end Fulcrum
