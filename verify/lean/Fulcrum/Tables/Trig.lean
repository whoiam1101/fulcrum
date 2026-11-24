module

public import Fulcrum.Math.Const
public import Fulcrum.Kernel.Funs

/-!
# The tables of `src/tables/trig.rs`, within half a unit

Every constant and every entry of `SIN_QUARTER` and `ATAN`, as Aeneas extracts
them, is within `½` of the true value times `2^62` (`2^126`, `2^192` for
`PI_126`, `FRAC_2_PI`): correctly rounded. The true value is near a rational
`S` within `R` (`entry_near`): `π` by `pi_near`, `sin` by its series at
`k · piQ / 512` and the `1`-Lipschitz bound, `arctan (k/256)` by its series,
above `½` through `arctan t = π/4 - arctan ((1 - t)/(1 + t))`. The kernel
checks `|T - S · 2^N| + R · 2^N ≤ ½` for all entries at once (`decide +kernel`).
-/

@[expose] public section

open Aeneas Aeneas.Std

namespace Fulcrum

/-- A natural `T` is within `½` of `v · 2^N` when `v` is within `R` of a rational
`S` and `|T - S · 2^N| + R · 2^N ≤ ½`. -/
theorem entry_near (T N : ℕ) (v : ℝ) (S R : ℚ) (hv : |v - S| ≤ R)
    (h : |(T : ℚ) - S * 2 ^ N| + R * 2 ^ N ≤ 1 / 2) : |(T : ℝ) - v * 2 ^ N| ≤ 1 / 2 := by
  have h' := (Rat.cast_le (K := ℝ)).mpr h
  push_cast at h'
  have p : (0 : ℝ) < 2 ^ N := pow_pos two_pos N
  have e : (T : ℝ) - v * 2 ^ N = ((T : ℝ) - S * 2 ^ N) + (S - v) * 2 ^ N := by ring
  rw [e]
  refine (abs_add_le _ _).trans ((add_le_add le_rfl ?_).trans h')
  rw [abs_mul, abs_of_pos p, abs_sub_comm]
  exact mul_le_mul_of_nonneg_right hv p.le

/-- `PI` is `π · 2^62` rounded to nearest. -/
theorem pi_entry : |(fulcrum.tables.trig.PI.val : ℝ) - Real.pi * 2 ^ 62| ≤ 1 / 2 :=
  entry_near _ 62 _ piQ (1 / 2 ^ 270) (by push_cast; exact pi_near) (by decide +kernel)

/-- `FRAC_PI_2` is `π/2 · 2^62` rounded to nearest. -/
theorem frac_pi_2_entry :
    |(fulcrum.tables.trig.FRAC_PI_2.val : ℝ) - Real.pi / 2 * 2 ^ 62| ≤ 1 / 2 := by
  refine entry_near _ 62 _ (piQ / 2) (1 / 2 ^ 271) ?_ (by decide +kernel)
  have e : Real.pi / 2 - ((piQ / 2 : ℚ) : ℝ) = (Real.pi - piQ) / 2 := by push_cast; ring
  rw [e, abs_div, abs_two]
  push_cast
  rw [pow_succ, ← div_div]
  exact div_le_div_of_nonneg_right pi_near zero_le_two

/-- `PI_126` is `π · 2^126` rounded to nearest. -/
theorem pi_126_entry : |(fulcrum.tables.trig.PI_126.val : ℝ) - Real.pi * 2 ^ 126| ≤ 1 / 2 :=
  entry_near _ 126 _ piQ (1 / 2 ^ 270) (by push_cast; exact pi_near) (by decide +kernel)

/-- `FRAC_2_PI`, three words from the most significant, is `2/π · 2^192` rounded
to nearest. -/
theorem frac_2_pi_entry :
    |(((fulcrum.tables.trig.FRAC_2_PI.val[0]!).val * 2 ^ 128 +
        (fulcrum.tables.trig.FRAC_2_PI.val[1]!).val * 2 ^ 64 +
        (fulcrum.tables.trig.FRAC_2_PI.val[2]!).val : ℕ) : ℝ) - 2 / Real.pi * 2 ^ 192| ≤ 1 / 2 := by
  have q3 : (3 : ℝ) ≤ (piQ : ℝ) := by exact_mod_cast (by decide +kernel : (3 : ℚ) ≤ piQ)
  have hv : |2 / Real.pi - ((2 / piQ : ℚ) : ℝ)| ≤ ((1 / 2 ^ 270 : ℚ) : ℝ) := by
    have p3 : (3 : ℝ) ≤ Real.pi := by
      have c := (Rat.cast_le (K := ℝ)).mpr (by decide +kernel : (3 : ℚ) ≤ piQ - 1 / 2 ^ 270)
      push_cast at c
      exact c.trans (sub_le_iff_le_add.mpr (neg_le_sub_iff_le_add.mp (abs_le.mp pi_near).1))
    have pp : (0 : ℝ) < Real.pi := Real.pi_pos
    have qp : (0 : ℝ) < piQ := three_pos.trans_le q3
    have e : 2 / Real.pi - ((2 / piQ : ℚ) : ℝ) = (piQ - Real.pi) * (2 / (Real.pi * piQ)) := by
      push_cast; field_simp
    rw [e, abs_mul, abs_sub_comm, abs_of_pos (by positivity : (0 : ℝ) < 2 / (Real.pi * piQ))]
    refine (mul_le_of_le_one_right (abs_nonneg _) ?_).trans (by push_cast; exact pi_near)
    rw [div_le_one (by positivity)]
    exact (by norm_num : (2 : ℝ) ≤ 3 * 3).trans (mul_le_mul p3 q3 (by norm_num) pp.le)
  have h := entry_near ((fulcrum.tables.trig.FRAC_2_PI.val[0]!).val * 2 ^ 128 +
    (fulcrum.tables.trig.FRAC_2_PI.val[1]!).val * 2 ^ 64 +
    (fulcrum.tables.trig.FRAC_2_PI.val[2]!).val) 192 (2 / Real.pi) (2 / piQ) (1 / 2 ^ 270)
    (by push_cast at hv ⊢; exact hv) (by decide +kernel)
  exact h

/-- `|k/512 · π - k · piQ/512| ≤ 2^-270` for `k ≤ 512`. -/
theorem table_angle_near (k : ℕ) (hk : k ≤ 512) :
    |(k : ℝ) / 256 * (Real.pi / 2) - ((k * piQ / 512 : ℚ) : ℝ)| ≤ 1 / 2 ^ 270 := by
  have e : (k : ℝ) / 256 * (Real.pi / 2) - ((k * piQ / 512 : ℚ) : ℝ) = k / 512 * (Real.pi - piQ) := by
    push_cast; ring
  rw [e, abs_mul, abs_of_nonneg (by positivity)]
  exact (mul_le_of_le_one_left (abs_nonneg _) ((div_le_one (by norm_num)).mpr
    (by exact_mod_cast hk))).trans pi_near

/-- `SIN_QUARTER` is `sin(k/256 · π/2) · 2^62` rounded to nearest at every `k ≤ 256`. -/
theorem sin_quarter_entry (k : ℕ) (hk : k < 257) :
    |((fulcrum.tables.trig.SIN_QUARTER.val[k]!).val : ℝ) - Real.sin (k / 256 * (Real.pi / 2)) * 2 ^ 62| ≤
      1 / 2 := by
  have all : ∀ k : ℕ, k < 257 → ((k * piQ / 512) ^ 2 < (2 * 15 + 2) ^ 2 ∧
      |((fulcrum.tables.trig.SIN_QUARTER.val[k]!).val : ℚ) - sinSum (k * piQ / 512) 15 * 2 ^ 62| +
        (sinRem (k * piQ / 512) 15 + 1 / 2 ^ 270) * 2 ^ 62 ≤ 1 / 2) := by decide +kernel
  have ⟨hq, h⟩ := all k hk
  refine entry_near _ 62 _ _ _ ?_ h
  have s := sin_near (k * piQ / 512) 15 (by exact_mod_cast hq)
  have l := (Real.abs_sin_sub_sin_le ((k : ℝ) / 256 * (Real.pi / 2)) ((k * piQ / 512 : ℚ) : ℝ)).trans
    (table_angle_near k (by omega))
  push_cast at s l ⊢
  exact (abs_sub_le _ _ _).trans ((add_le_add l s).trans_eq (add_comm _ _))

/-- The rational `S` and the bound `R` of `arctan (k/256)`: its series below
`½`, `π/4` minus the series of `(256 - k)/(256 + k)` above. -/
def atanEntry (k : ℕ) : ℚ × ℚ :=
  if k ≤ 128 then (atanSum (k / 256) 42, atanRem (k / 256) 42)
  else (piQ / 4 - atanSum ((256 - k) / (256 + k)) 28, 1 / 2 ^ 272 + atanRem ((256 - k) / (256 + k)) 28)

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
    have b := arctan_near ((k : ℚ) / 256) 42 q
    push_cast at b ⊢
    exact b
  · next h =>
    have kp : (0 : ℚ) < k := by exact_mod_cast (by omega : 0 < k)
    have k256 : (k : ℚ) ≤ 256 := by exact_mod_cast hk
    have q : |((256 : ℚ) - k) / (256 + k)| < 1 := by
      rw [abs_of_nonneg (div_nonneg (sub_nonneg.mpr k256) (by positivity)), div_lt_one (by positivity)]
      exact (sub_lt_self 256 kp).trans (lt_add_of_pos_right 256 kp)
    have b := arctan_near (((256 : ℚ) - k) / (256 + k)) 28 q
    have c := arctan_add_complement ((k : ℝ) / 256) (by positivity)
    have e : (1 - (k : ℝ) / 256) / (1 + k / 256) = (256 - k) / (256 + k) := by field_simp
    rw [e] at c
    have v : Real.arctan ((k : ℝ) / 256) = Real.pi / 4 - Real.arctan ((256 - k) / (256 + k)) := by
      rw [← c]; ring
    push_cast at b ⊢
    rw [v, show Real.pi / 4 - Real.arctan ((256 - k) / (256 + k)) -
        ((piQ : ℝ) / 4 - atanSum ((256 - k) / (256 + k)) 28) =
        (Real.pi - piQ) / 4 - (Real.arctan ((256 - k) / (256 + k)) - atanSum ((256 - k) / (256 + k)) 28) by
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
