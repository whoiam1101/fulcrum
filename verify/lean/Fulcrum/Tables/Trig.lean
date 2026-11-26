module

public import Fulcrum.Math.Const
public import Fulcrum.Kernel.Funs

/-!
# The constants of `src/tables/trig.rs`, within half a unit

Every constant, as Aeneas extracts it, is within `½` of the true value times `2^62` (`2^126`,
`2^192` for `PI_126`, `FRAC_2_PI`): correctly rounded, `π` by `pi_near` and `entry_near`.
`table_angle_near` bounds the angles `k · piQ / 512` at which the series of `SIN_QUARTER`
(`SinQuarter.lean`) is evaluated; `ATAN` is in `Atan.lean`.
-/

@[expose] public section

open Aeneas Aeneas.Std

namespace Fulcrum

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

end Fulcrum

end
