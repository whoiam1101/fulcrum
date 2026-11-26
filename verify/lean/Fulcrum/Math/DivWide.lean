module

public import Fulcrum.Spec

/-!
# One step of Knuth's algorithm D with a two-digit divisor

The math of `wide::div_rem_3by2`, no code. The dividend is `N = u · 2^64 + v` with `v < 2^64`,
the divisor `D = d₁ · 2^64 + d₀` with digits `d₀ < 2^64` and `0 < d₁ < 2^64`, and `u < D`, so the
quotient `Q = ⌊N / D⌋` is below `2^64` (`quot_lt`).

- The estimate `knuthEst u d₁`, `⌊u / d₁⌋` capped at `2^64 - 1`, is at least `Q`
  (`quot_le_est`), below `2^64` (`est_lt`), and `est · d₁ ≤ u` (`est_mul_le`).
- For `q · d₁ + r = u` the test `q · d₀ > r · 2^64 + v` is `q · D > N` (`test_iff`), so it holds
  exactly while `q > Q`; for `r ≥ 2^64` it fails, and then `q ≤ Q` (`wide_r_le`). The loop
  stops at `Q` without a bound on its steps: its measure is `q`.
- The remainder is `N - Q · D` taken modulo `2^128` from the low words (`wrap_rem`).
-/

@[expose] public section

namespace Fulcrum

/-- The estimate of the quotient digit: `⌊u / d₁⌋`, or `2^64 - 1` when `⌊u / 2^64⌋ ≥ d₁`. -/
def knuthEst (u d1 : ℕ) : ℕ := if d1 ≤ u / 2 ^ 64 then 2 ^ 64 - 1 else u / d1

/-- The quotient of `u · 2^64 + v` by `D > u` is below `2^64`. -/
theorem quot_lt (u v D : ℕ) (hu : u < D) (hv : v < 2 ^ 64) : (u * 2 ^ 64 + v) / D < 2 ^ 64 := by
  have h := Nat.mul_le_mul_right (2 ^ 64) (Nat.succ_le_of_lt hu)
  rw [Nat.div_lt_iff_lt_mul (Nat.zero_lt_of_lt hu), Nat.mul_comm (2 ^ 64)]
  omega

/-- The quotient by `D = d₁ · 2^64 + d₀` is at most `⌊u / d₁⌋`. -/
theorem quot_le_div (u v d1 d0 : ℕ) (hd1 : 0 < d1) (hv : v < 2 ^ 64) :
    (u * 2 ^ 64 + v) / (d1 * 2 ^ 64 + d0) ≤ u / d1 :=
  calc (u * 2 ^ 64 + v) / (d1 * 2 ^ 64 + d0)
      ≤ (u * 2 ^ 64 + v) / (d1 * 2 ^ 64) := Nat.div_le_div_left (Nat.le_add_right _ _) (by positivity)
    _ = (u * 2 ^ 64 + v) / 2 ^ 64 / d1 := by rw [Nat.div_div_eq_div_mul, Nat.mul_comm d1]
    _ = u / d1 := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hv, Nat.zero_add]

/-- The estimate is at least the quotient. -/
theorem quot_le_est (u v d1 d0 : ℕ) (hd1 : 0 < d1) (hu : u < d1 * 2 ^ 64 + d0) (hv : v < 2 ^ 64) :
    (u * 2 ^ 64 + v) / (d1 * 2 ^ 64 + d0) ≤ knuthEst u d1 := by
  unfold knuthEst
  split
  · exact Nat.le_pred_of_lt (quot_lt u v _ hu hv)
  · exact quot_le_div u v d1 d0 hd1 hv

/-- The estimate is below `2^64`. -/
theorem est_lt (u d1 : ℕ) : knuthEst u d1 < 2 ^ 64 := by
  unfold knuthEst
  split
  · exact Nat.pred_lt (Nat.two_pow_pos 64).ne'
  · rename_i h
    rcases Nat.eq_zero_or_pos d1 with h0 | h0
    · rw [h0, Nat.div_zero]; exact Nat.two_pow_pos 64
    · rw [Nat.div_lt_iff_lt_mul h0, Nat.mul_comm]
      exact (Nat.div_lt_iff_lt_mul (by positivity)).mp (Nat.lt_of_not_le h)

/-- The estimate times `d₁` does not exceed `u`. -/
theorem est_mul_le (u d1 : ℕ) : knuthEst u d1 * d1 ≤ u := by
  unfold knuthEst
  split
  · rename_i h
    have h' := (Nat.le_div_iff_mul_le (by positivity)).mp h
    exact (Nat.mul_le_mul_right d1 (Nat.pred_le _)).trans (Nat.mul_comm _ d1 ▸ h')
  · exact Nat.div_mul_le_self u d1

/-- The test of the loop: for `q · d₁ + r = u`, `q · d₀ > r · 2^64 + v` is `q · D > N`. -/
theorem test_iff (q d1 d0 r u v : ℕ) (h : q * d1 + r = u) :
    r * 2 ^ 64 + v < q * d0 ↔ u * 2 ^ 64 + v < q * (d1 * 2 ^ 64 + d0) := by
  subst h
  rw [Nat.mul_add, ← Nat.mul_assoc]
  generalize q * d1 = A
  generalize q * d0 = B
  omega

/-- With `r ≥ 2^64` the product `q · D` does not exceed `N`. -/
theorem wide_r_le (q d1 d0 r u v : ℕ) (h : q * d1 + r = u) (hq : q < 2 ^ 64) (hd0 : d0 < 2 ^ 64)
    (hr : 2 ^ 64 ≤ r) : q * (d1 * 2 ^ 64 + d0) ≤ u * 2 ^ 64 + v := by
  have p := Nat.mul_lt_mul'' hq hd0
  subst h
  rw [Nat.mul_add, ← Nat.mul_assoc]
  generalize q * d1 = A at p ⊢
  generalize q * d0 = B at p ⊢
  omega

/-- The remainder from the low words: `N mod 2^128` minus `Q · D mod 2^128`, wrapped, is
`N - Q · D` when that is below `2^128`. -/
theorem wrap_rem (u v P R : ℕ) (h : u * 2 ^ 64 + v = P + R) (hR : R < 2 ^ 128) :
    (u % 2 ^ 64 * 2 ^ 64 + v + (2 ^ 128 - P % 2 ^ 128)) % 2 ^ 128 = R := by
  omega

end Fulcrum

end
