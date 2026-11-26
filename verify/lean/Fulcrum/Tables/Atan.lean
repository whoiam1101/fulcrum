module

public import Fulcrum.Kernel.Funs
public import Fulcrum.Math.Const
public import Fulcrum.Math.Series

/-!
# The table `ATAN` of `src/tables/trig.rs`, within half a unit

Every entry `k ≤ 256` is `arctan (k/256) · 2^62` correctly rounded: 29 terms of the series of
`arctan` up to `½`, above it `π/4` minus 19 terms at `(1 - t)/(1 + t)`
(`arctan_add_complement`); the kernel checks all entries at once (`decide +kernel`).
-/

@[expose] public section

open Aeneas Aeneas.Std

namespace Fulcrum

/-- The rational `S` and the bound `R` of `arctan (k/256)`: its series below
`½`, `π/4` minus the series of `(256 - k)/(256 + k)` above. -/
def atanEntry (k : ℕ) : ℚ × ℚ :=
  if k ≤ 128 then (atanSum (k / 256) 29, atanRem (k / 256) 29)
  else (piQ / 4 - atanSum ((256 - k) / (256 + k)) 19, 1 / 2 ^ 272 + atanRem ((256 - k) / (256 + k)) 19)

/-- `arctan t + arctan ((1 - t)/(1 + t)) = π/4` for `0 ≤ t`. -/
theorem arctan_add_complement (t : ℝ) (ht : 0 ≤ t) :
    Real.arctan t + Real.arctan ((1 - t) / (1 + t)) = Real.pi / 4 := by
  have p : 0 < 1 + t := by positivity
  have q : (0 : ℝ) < (1 + t ^ 2) / (1 + t) := by positivity
  have lt : t * ((1 - t) / (1 + t)) < 1 := by
    rw [mul_div_assoc', div_lt_one p, show t * (1 - t) = t - t ^ 2 by ring]
    exact (sub_le_self t (sq_nonneg t)).trans_lt (lt_add_of_pos_left t one_pos)
  have hn : t + (1 - t) / (1 + t) = (1 + t ^ 2) / (1 + t) := by field_simp; ring
  have hd : 1 - t * ((1 - t) / (1 + t)) = (1 + t ^ 2) / (1 + t) := by field_simp; ring
  rw [Real.arctan_add lt, hn, hd, div_self q.ne', Real.arctan_one]

/-- `arctan (k/256)` is within `(atanEntry k).2` of `(atanEntry k).1` for `k ≤ 256`. -/
theorem atanEntry_near (k : ℕ) (hk : k ≤ 256) :
    |Real.arctan ((k : ℝ) / 256) - (atanEntry k).1| ≤ (atanEntry k).2 := by
  unfold atanEntry
  split
  · next h =>
    have q : |(k : ℚ) / 256| < 1 := by
      rw [abs_of_nonneg (by positivity), div_lt_one (by norm_num)]
      exact_mod_cast (by omega : k < 256)
    have b := arctan_near ((k : ℚ) / 256) 29 q
    push_cast at b ⊢
    exact b
  · next h =>
    have kp : (0 : ℚ) < k := by exact_mod_cast (by omega : 0 < k)
    have k256 : (k : ℚ) ≤ 256 := by exact_mod_cast hk
    have q : |((256 : ℚ) - k) / (256 + k)| < 1 := by
      rw [abs_of_nonneg (div_nonneg (sub_nonneg.mpr k256) (by positivity)), div_lt_one (by positivity)]
      exact (sub_lt_self 256 kp).trans (lt_add_of_pos_right 256 kp)
    have b := arctan_near (((256 : ℚ) - k) / (256 + k)) 19 q
    have c := arctan_add_complement ((k : ℝ) / 256) (by positivity)
    have e : (1 - (k : ℝ) / 256) / (1 + k / 256) = (256 - k) / (256 + k) := by field_simp
    rw [e] at c
    have v : Real.arctan ((k : ℝ) / 256) = Real.pi / 4 - Real.arctan ((256 - k) / (256 + k)) := by
      rw [← c]; ring
    push_cast at b ⊢
    rw [v, show Real.pi / 4 - Real.arctan ((256 - k) / (256 + k)) -
        ((piQ : ℝ) / 4 - atanSum ((256 - k) / (256 + k)) 19) =
        (Real.pi - piQ) / 4 - (Real.arctan ((256 - k) / (256 + k)) - atanSum ((256 - k) / (256 + k)) 19) by
      ring]
    refine (abs_sub _ _).trans (add_le_add ?_ b)
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4), div_le_iff₀ (by norm_num)]
    exact pi_near.trans_eq (by
      rw [show 272 = 270 + 2 from rfl, pow_add, one_div, one_div, mul_inv, mul_assoc]
      norm_num)

/-- `ATAN` is `arctan (k/256) · 2^62` rounded to nearest at every `k ≤ 256`. -/
theorem atan_entry (k : ℕ) (hk : k < 257) :
    |((fulcrum.tables.trig.ATAN.val[k]!).val : ℝ) - Real.arctan (k / 256) * 2 ^ 62| ≤ 1 / 2 := by
  have all : ∀ k : ℕ, k < 257 →
      |((fulcrum.tables.trig.ATAN.val[k]!).val : ℚ) - (atanEntry k).1 * 2 ^ 62| +
        (atanEntry k).2 * 2 ^ 62 ≤ 1 / 2 := by decide +kernel
  exact entry_near _ 62 _ _ _ (atanEntry_near k (by omega)) (all k hk)

end Fulcrum

end
