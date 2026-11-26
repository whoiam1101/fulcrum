module

public import Fulcrum.Spec
public import Mathlib.Data.Nat.Log

/-!
# Dividing `hi · 2^128 + lo` by `d` in two digits

The math of `wide::div_rem_u256`, no code. For `0 < d < 2^128`, `s = 127 - ⌊log₂ d⌋` normalizes
`d`: `2^127 ≤ d · 2^s < 2^128` (`norm_bounds`). The dividend shifted by `s` has the words
`hi · 2^s + ⌊lo / 2^(128 - s)⌋` and `lo · 2^s mod 2^128` (`norm_join`), and the high one stays
below `d · 2^s` for `hi < d` (`norm_hi_lt`). Two digits of the quotient by `D` from
`X = ⌊N / 2^64⌋` and the last word `w` make the quotient of `X · 2^64 + w` (`two_steps_div`,
`two_steps_mod`), and shifting the dividend and the divisor by `s` keeps the quotient and scales
the remainder (`Nat.mul_div_mul_right`, `Nat.mul_mod_mul_right`).
-/

@[expose] public section

namespace Fulcrum

/-- The divisor shifted by `127 - ⌊log₂ d⌋` has its top bit set and fits 128 bits. -/
theorem norm_bounds (d : ℕ) (h0 : d ≠ 0) (hl : d < 2 ^ 128) :
    2 ^ 127 ≤ d * 2 ^ (128 - Nat.log 2 d - 1) ∧ d * 2 ^ (128 - Nat.log 2 d - 1) < 2 ^ 128 := by
  have lo := Nat.pow_log_le_self 2 h0
  have hi := Nat.lt_pow_succ_log_self Nat.one_lt_two d
  have L : Nat.log 2 d ≤ 127 :=
    Nat.le_of_lt_succ ((Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp (lo.trans_lt hl))
  have e1 : Nat.log 2 d + (128 - Nat.log 2 d - 1) = 127 := by omega
  have e2 : Nat.log 2 d + 1 + (128 - Nat.log 2 d - 1) = 128 := by omega
  constructor
  · calc 2 ^ 127 = 2 ^ Nat.log 2 d * 2 ^ (128 - Nat.log 2 d - 1) := by rw [← pow_add, e1]
      _ ≤ d * 2 ^ (128 - Nat.log 2 d - 1) := Nat.mul_le_mul_right _ lo
  · calc d * 2 ^ (128 - Nat.log 2 d - 1) < 2 ^ (Nat.log 2 d + 1) * 2 ^ (128 - Nat.log 2 d - 1) :=
          Nat.mul_lt_mul_of_pos_right hi (by positivity)
      _ = 2 ^ 128 := by rw [← pow_add, e2]

/-- The top word of `lo · 2^s` is `⌊lo / 2^(128 - s)⌋`. -/
theorem shl_top (lo s : ℕ) (hs : s ≤ 128) : lo * 2 ^ s / 2 ^ 128 = lo / 2 ^ (128 - s) := by
  rw [show (2 : ℕ) ^ 128 = 2 ^ (128 - s) * 2 ^ s by rw [← pow_add, Nat.sub_add_cancel hs],
    Nat.mul_div_mul_right _ _ (by positivity)]

/-- The words of the dividend shifted by `s`. -/
theorem norm_join (hi lo s : ℕ) (hs : s ≤ 128) :
    (hi * 2 ^ s + lo / 2 ^ (128 - s)) * 2 ^ 128 + lo * 2 ^ s % 2 ^ 128 = (hi * 2 ^ 128 + lo) * 2 ^ s := by
  have e := Nat.div_add_mod (lo * 2 ^ s) (2 ^ 128)
  rw [shl_top lo s hs] at e
  rw [Nat.add_mul, Nat.add_mul, Nat.add_assoc, Nat.mul_comm (lo / _), e, Nat.mul_right_comm]

/-- The high word stays below the shifted divisor. -/
theorem norm_hi_lt (hi lo d s : ℕ) (hs : s ≤ 128) (hl : lo < 2 ^ 128) (h : hi < d) :
    hi * 2 ^ s + lo / 2 ^ (128 - s) < d * 2 ^ s := by
  have t : lo / 2 ^ (128 - s) < 2 ^ s := by
    rw [← shl_top lo s hs, Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.add_comm]
    exact Nat.mul_lt_mul_of_pos_right hl (by positivity) |>.trans_le (by rw [pow_add])
  calc hi * 2 ^ s + lo / 2 ^ (128 - s) < hi * 2 ^ s + 2 ^ s := Nat.add_lt_add_left t _
    _ = (hi + 1) * 2 ^ s := by rw [Nat.succ_mul]
    _ ≤ d * 2 ^ s := Nat.mul_le_mul_right _ h

/-- The second step divides `(X mod D) · 2^64 + w`, the rest of the first. -/
theorem two_steps_eq (X w D : ℕ) : X * 2 ^ 64 + w = D * (X / D * 2 ^ 64) + (X % D * 2 ^ 64 + w) := by
  conv_lhs => rw [← Nat.div_add_mod X D]
  rw [Nat.add_mul, Nat.add_assoc, Nat.mul_assoc]

/-- Two digits of the quotient make the quotient of `X · 2^64 + w`. -/
theorem two_steps_div (X w D : ℕ) (hD : 0 < D) :
    X / D * 2 ^ 64 + (X % D * 2 ^ 64 + w) / D = (X * 2 ^ 64 + w) / D := by
  rw [two_steps_eq X w D, Nat.add_comm (D * _), Nat.add_mul_div_left _ _ hD, Nat.add_comm]

/-- The remainder of the second step is the remainder of `X · 2^64 + w`. -/
theorem two_steps_mod (X w D : ℕ) : (X % D * 2 ^ 64 + w) % D = (X * 2 ^ 64 + w) % D := by
  rw [two_steps_eq X w D, Nat.mul_add_mod]

/-- The high word and the top half of the low word make `X` with `X · 2^64 + w = hi · 2^128 + lo`. -/
theorem words_join (h l : ℕ) : (h * 2 ^ 64 + l / 2 ^ 64) * 2 ^ 64 + l % 2 ^ 64 = h * 2 ^ 128 + l := by
  omega

/-- Two steps on the dividend and the divisor shifted by `s` give the quotient of `N` by `d`, and
the remainder shifted back is `N mod d`. -/
theorem two_steps_norm (N d s X w : ℕ) (hd : 0 < d) (hX : X * 2 ^ 64 + w = N * 2 ^ s) :
    X / (d * 2 ^ s) * 2 ^ 64 + (X % (d * 2 ^ s) * 2 ^ 64 + w) / (d * 2 ^ s) = N / d ∧
      (X % (d * 2 ^ s) * 2 ^ 64 + w) % (d * 2 ^ s) / 2 ^ s = N % d := by
  have p : 0 < 2 ^ s := by positivity
  rw [two_steps_div _ _ _ (Nat.mul_pos hd p), two_steps_mod, hX, Nat.mul_div_mul_right _ _ p,
    Nat.mul_mod_mul_right, Nat.mul_div_cancel _ p]
  exact ⟨rfl, rfl⟩

end Fulcrum

end
