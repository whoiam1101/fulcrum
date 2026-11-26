module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Fulcrum.Math.Log

/-!
# The reduction of `exp` (INTERNALS §3.16)

The math of `exp::exp` in L4, no code here. `L` stands for `tables::exp::LN_2`, within
`½` of `ln 2 · 2^104`, and `TWO_LOG2_E · L = 2^167 + δ` with a small `δ`.

- `exp_mark_of_ge`, `exp_half_of_le`: the two ends, `x ≥ f` gives `e^x · 2^f ≥ 2^(2f - 1)`
  and `x ≤ -2f` gives `e^x · 2^f ≤ ½`.
- `exp_reduce_bounds`: `j = ⌊raw · TWO_LOG2_E / 2^(f + 55)⌋` is within `2^15` and leaves
  `y = raw · 2^(112 - f) - j · L` in `(-L, 2L)`, so one correction of `j` puts it in `[0, L)`.
- `exp_mark_of_j`: `j ≥ 256 (f - 1)` gives the mark condition `e^x · 2^f ≥ 2^(2f - 1)`.
- `exp_reduced_near`: `Y = x - j · ln 2 / 256` is within `2^-72 + 2^-97` of the truncated
  `⌊y / 2^40⌋ / 2^72`, and `2^(k/256) · e^Y ≤ 2 + 2^-80`.
- `exp_tail_near`: an entry within `0.81 · 2^56` of `T · e^A · 2^126` is within `1.4 · 2^56` of
  `T · e^Y · 2^126`, at most `2^128`.
-/

@[expose] public section

namespace Fulcrum

/-- `2^n = e^(n ln 2)`. -/
theorem two_pow_eq_exp (n : ℕ) : (2 : ℝ) ^ n = Real.exp (n * Real.log 2) := by
  rw [Real.exp_nat_mul, Real.exp_log two_pos]

/-- `e^x · 2^f · 2^s = 2^(k/256) · e^Y · 2^126` for `j = 256 n + k`, `Y = x - j · ln 2 / 256`
and `s = 126 - f - n`. -/
theorem exp_scale (x : ℝ) (j n k : ℤ) (f s : ℕ) (hj : j = 256 * n + k) (hs : (s : ℤ) = 126 - f - n) :
    Real.exp x * 2 ^ f * 2 ^ s =
      (2 : ℝ) ^ ((k : ℝ) / 256) * Real.exp (x - j * Real.log 2 / 256) * 2 ^ 126 := by
  have p : (2 : ℝ) ^ n * 2 ^ f * 2 ^ s = 2 ^ 126 := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ two_ne_zero, ← zpow_add₀ two_ne_zero]
    congr 1
    omega
  have en : Real.exp (n * Real.log 2) = (2 : ℝ) ^ n := by
    rw [← Real.rpow_intCast, Real.rpow_def_of_pos two_pos, mul_comm]
  have ek : (2 : ℝ) ^ ((k : ℝ) / 256) = Real.exp (k / 256 * Real.log 2) := by
    rw [Real.rpow_def_of_pos two_pos, mul_comm]
  have ex : Real.exp x = Real.exp (n * Real.log 2) * Real.exp (k / 256 * Real.log 2) *
      Real.exp (x - j * Real.log 2 / 256) := by
    rw [← Real.exp_add, ← Real.exp_add, hj]; congr 1; push_cast; ring
  rw [ex, en, ek, ← p]
  ring

/-- `e^A` against `e^B` for `|A - B| ≤ d ≤ c ≤ 1`: within `(1 + c) · d · e^B`. -/
theorem exp_shift_near (A B d c : ℝ) (h : |A - B| ≤ d) (hd : d ≤ c) (hc : c ≤ 1) :
    |Real.exp A - Real.exp B| ≤ Real.exp B * ((1 + c) * d) := by
  have d0 : 0 ≤ d := (abs_nonneg _).trans h
  have h1 : |A - B| ≤ 1 := h.trans (hd.trans hc)
  have q := Real.abs_exp_sub_one_sub_id_le h1
  rw [show Real.exp A - Real.exp B = Real.exp B * (Real.exp (A - B) - 1) by
    rw [mul_sub, ← Real.exp_add, add_sub_cancel, mul_one], abs_mul, abs_of_pos (Real.exp_pos _)]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  have sq : (A - B) ^ 2 ≤ d * c := by
    rw [← sq_abs, sq]; exact mul_le_mul h (h.trans hd) (abs_nonneg _) d0
  calc |Real.exp (A - B) - 1| ≤ |Real.exp (A - B) - 1 - (A - B)| + |A - B| := by
        have := abs_add_le (Real.exp (A - B) - 1 - (A - B)) (A - B)
        rwa [sub_add_cancel] at this
    _ ≤ (A - B) ^ 2 + d := add_le_add q h
    _ ≤ (1 + c) * d := by nlinarith only [sq]

/-- `x ≥ f` gives `e^x · 2^f ≥ 2^(2f - 1)`. -/
theorem exp_mark_of_ge (x : ℝ) (f : ℕ) (h : (f : ℝ) ≤ x) :
    (2 : ℝ) ^ (2 * f - 1) ≤ Real.exp x * 2 ^ f := by
  have e : (2 : ℝ) ^ f ≤ Real.exp x := by
    rw [two_pow_eq_exp]
    exact Real.exp_le_exp.mpr (by nlinarith only [(Nat.cast_nonneg f : (0 : ℝ) ≤ f), log_two_le', h])
  calc (2 : ℝ) ^ (2 * f - 1) ≤ 2 ^ (2 * f) := pow_le_pow_right₀ one_le_two (by omega)
    _ = 2 ^ f * 2 ^ f := by rw [← pow_add, two_mul]
    _ ≤ Real.exp x * 2 ^ f := mul_le_mul_of_nonneg_right e (by positivity)

/-- `x ≤ -2f` with `f ≥ 1` gives `e^x · 2^f ≤ ½`. -/
theorem exp_half_of_le (x : ℝ) (f : ℕ) (hf1 : 1 ≤ f) (h : x ≤ -(2 * f)) :
    Real.exp x * 2 ^ f ≤ 1 / 2 := by
  rw [two_pow_eq_exp, ← Real.exp_add]
  have fr : (1 : ℝ) ≤ f := by exact_mod_cast hf1
  calc Real.exp (x + f * Real.log 2) ≤ Real.exp (-Real.log 2) :=
        Real.exp_le_exp.mpr (by nlinarith only [log_two_le', h, fr])
    _ = 1 / 2 := by rw [Real.exp_neg, Real.exp_log two_pos, one_div]

/-- `j = ⌊raw · TWO_LOG2_E / 2^(f + 55)⌋` for `-2f · 2^f < raw < f · 2^f`: `|j| ≤ 2^15`,
`P = raw · 2^(112 - f)` within `2^118`, and `P - j · L ∈ (-L, 2L)`. -/
theorem exp_reduce_bounds (raw j L : ℤ) (f : ℕ) (hf : f ≤ 32) (r1 : raw < f * 2 ^ f)
    (r2 : -(2 * f * 2 ^ f) < raw) (hj : j = raw * 13306513097844322492 / 2 ^ (f + 55))
    (Lv : L = 14058695031733113177892216608772) :
    -2 ^ 15 ≤ j ∧ j ≤ 2 ^ 15 ∧ -(2 ^ 118) ≤ raw * 2 ^ (112 - f) ∧ raw * 2 ^ (112 - f) ≤ 2 ^ 118 ∧
      -L < raw * 2 ^ (112 - f) - j * L ∧ raw * 2 ^ (112 - f) - j * L < 2 * L := by
  have pp : (0 : ℤ) < 2 ^ f := by positivity
  have fr : (f : ℤ) ≤ 32 := by exact_mod_cast hf
  have f2 : (f : ℤ) * 2 ^ f ≤ 32 * 2 ^ f := mul_le_mul_of_nonneg_right fr pp.le
  have rlo : -(64 * 2 ^ f) ≤ raw := by linarith only [r2, f2]
  have rhi : raw ≤ 64 * 2 ^ f := by linarith only [pp, r1, f2]
  have Qb : -(2 ^ 15 * (2 ^ f * 2 ^ 55)) ≤ raw * 13306513097844322492 ∧
      raw * 13306513097844322492 ≤ 2 ^ 15 * (2 ^ f * 2 ^ 55) :=
    ⟨by linarith only [pp, r2, f2], by linarith only [pp, r1, f2]⟩
  set D : ℤ := 2 ^ (f + 55) with hD
  have D' : D = 2 ^ f * 2 ^ 55 := by rw [hD, pow_add]
  have Dp : 0 < D := by positivity
  have jlo : -2 ^ 15 ≤ j := by
    rw [hj, Int.le_ediv_iff_mul_le Dp, D']; linarith only [Qb.1]
  have jhi : j ≤ 2 ^ 15 := by
    have : j < 2 ^ 15 + 1 := by
      rw [hj, Int.ediv_lt_iff_lt_mul Dp, D']; linarith only [Qb.2, pp]
    omega
  have jD1 : j * D ≤ raw * 13306513097844322492 := hj ▸ Int.ediv_mul_le _ Dp.ne'
  have jD2 : raw * 13306513097844322492 < (j + 1) * D := hj ▸ Int.lt_ediv_add_one_mul_self _ Dp
  have p112 : (2 : ℤ) ^ (112 - f) * 2 ^ f = 2 ^ 112 := by rw [← pow_add]; congr 1; omega
  have q : (0 : ℤ) < 2 ^ (112 - f) := by positivity
  have u := mul_le_mul_of_nonneg_right rhi q.le
  have l := mul_le_mul_of_nonneg_right rlo q.le
  rw [mul_assoc, mul_comm (2 ^ f), p112] at u
  rw [neg_mul, mul_assoc, mul_comm (2 ^ f), p112] at l
  set P : ℤ := raw * 2 ^ (112 - f) with hP
  have PD : P * D = raw * 2 ^ 167 := by
    rw [hP, D', mul_assoc, ← mul_assoc (2 ^ (112 - f)), p112]; ring
  have dd : (13306513097844322492 : ℤ) * L = 2 ^ 167 + 3595333768577312205446798598896 := by rw [Lv]; norm_num
  have rd : -(D * L) ≤ 2 * (raw * 3595333768577312205446798598896) ∧
      2 * (raw * 3595333768577312205446798598896) ≤ D * L := by
    have c : (128 : ℤ) * 3595333768577312205446798598896 ≤ 2 ^ 55 * L := by rw [Lv]; norm_num
    have c' := mul_le_mul_of_nonneg_right c pp.le
    rw [D']; constructor <;> linarith only [r2, f2, c', pp, r1]
  have yD : (P - j * L) * D = raw * 2 ^ 167 - j * D * L := by rw [sub_mul, PD]; ring
  have L0 : 0 < L := by rw [Lv]; norm_num
  have a1 : j * D * L ≤ raw * 13306513097844322492 * L := mul_le_mul_of_nonneg_right jD1 L0.le
  have a2 : raw * 13306513097844322492 * L < (j + 1) * D * L := mul_lt_mul_of_pos_right jD2 L0
  have QL : raw * 13306513097844322492 * L = raw * 2 ^ 167 + raw * 3595333768577312205446798598896 := by
    rw [mul_assoc, dd]; ring
  refine ⟨jlo, jhi, by linarith only [l], by linarith only [u], ?_, ?_⟩
  · have : -L * D < (P - j * L) * D := by linarith only [rd, yD, a1, a2, QL]
    exact lt_of_mul_lt_mul_right this Dp.le
  · have : (P - j * L) * D < 2 * L * D := by linarith only [rd, yD, a1, a2, QL]
    exact lt_of_mul_lt_mul_right this Dp.le

/-- `x · 2^112 = j · L + y` with `y ≥ 0`, `L ≥ ln 2 · 2^104` and `j ≥ 256 (f - 1)` give
`e^x · 2^f ≥ 2^(2f - 1)`. -/
theorem exp_mark_of_j (x : ℝ) (j y L : ℤ) (f : ℕ) (hf1 : 1 ≤ f) (xP : x * 2 ^ 112 = j * L + y)
    (y0 : 0 ≤ y) (jb : ((f : ℤ) - 1) * 256 ≤ j) (Lg : Real.log 2 * 2 ^ 104 ≤ L) :
    (2 : ℝ) ^ (2 * f - 1) ≤ Real.exp x * 2 ^ f := by
  have jb' : (((f : ℤ) - 1) * 256 : ℝ) ≤ j := by exact_mod_cast jb
  have f1 : (0 : ℝ) ≤ (f : ℝ) - 1 := sub_nonneg.mpr (by exact_mod_cast hf1)
  have y0' : (0 : ℝ) ≤ y := by exact_mod_cast y0
  have Lp : (0 : ℝ) ≤ L := le_trans (by positivity) Lg
  have xlo : ((f : ℝ) - 1) * Real.log 2 ≤ x := by
    have h1 : ((f : ℝ) - 1) * 256 * (Real.log 2 * 2 ^ 104) ≤ ((f : ℝ) - 1) * 256 * L :=
      mul_le_mul_of_nonneg_left Lg (by positivity)
    have h2 : ((f : ℝ) - 1) * 256 * L ≤ (j : ℝ) * L := mul_le_mul_of_nonneg_right jb' Lp
    have : ((f : ℝ) - 1) * Real.log 2 * 2 ^ 112 ≤ x * 2 ^ 112 := by
      rw [xP]; linarith only [h1, h2, y0']
    exact le_of_mul_le_mul_right this (by positivity)
  have e : (2 : ℝ) ^ (2 * f - 1) = 2 ^ (f - 1) * 2 ^ f := by rw [← pow_add]; congr 1; omega
  rw [e]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  rw [two_pow_eq_exp, Nat.cast_sub hf1, Nat.cast_one]
  exact Real.exp_le_exp.mpr xlo

/-- `x · 2^112 = j · L + y` with `0 ≤ y < L`, `|j| ≤ 2^15 + 1`, `L` within `½` of
`ln 2 · 2^104`, `a = ⌊y / 2^40⌋` and `k < 256`: `Y = x - j · ln 2 / 256` is within
`2^-72 + 2^-97` of `a / 2^72`, and `2^(k/256) · e^Y ≤ 2 + 2^-80`. -/
theorem exp_reduced_near (x : ℝ) (j y L : ℤ) (a k : ℕ) (xP : x * 2 ^ 112 = j * L + y) (y0 : 0 ≤ y)
    (yL : y < L) (jlo : -2 ^ 15 - 1 ≤ j) (jhi : j ≤ 2 ^ 15 + 1)
    (eL : |(L : ℝ) - Real.log 2 * 2 ^ 104| ≤ 1 / 2) (ha : (a : ℝ) = ((y / 2 ^ 40 : ℤ) : ℝ)) (hk : k < 256) :
    |(a : ℝ) / 2 ^ 72 - (x - j * Real.log 2 / 256)| ≤ 1 / 2 ^ 72 + 1 / 2 ^ 97 ∧
      (2 : ℝ) ^ ((k : ℝ) / 256) * Real.exp (x - j * Real.log 2 / 256) ≤ 2 + 1 / 2 ^ 80 := by
  set Y : ℝ := x - j * Real.log 2 / 256 with hY
  have Yr : Y = ((y : ℝ) + j * ((L : ℝ) - Real.log 2 * 2 ^ 104)) / 2 ^ 112 := by
    rw [hY, eq_div_iff (by positivity), sub_mul, xP]; ring
  have jR : |(j : ℝ)| ≤ 2 ^ 15 + 1 := by
    rw [abs_le]; constructor
    · have : ((-2 ^ 15 - 1 : ℤ) : ℝ) ≤ j := by exact_mod_cast jlo
      push_cast at this; linarith only [this]
    · have : (j : ℝ) ≤ ((2 ^ 15 + 1 : ℤ) : ℝ) := by exact_mod_cast jhi
      push_cast at this; linarith only [this]
  have jL : |(j : ℝ) * ((L : ℝ) - Real.log 2 * 2 ^ 104)| ≤ (2 ^ 15 + 1) * (1 / 2) := by
    rw [abs_mul]; exact mul_le_mul jR eL (abs_nonneg _) (by positivity)
  have dAY : |(a : ℝ) / 2 ^ 72 - Y| ≤ 1 / 2 ^ 72 + 1 / 2 ^ 97 := by
    have ⟨fl1, fl2⟩ : ((y / 2 ^ 40 : ℤ) : ℝ) ≤ (y : ℝ) / 2 ^ 40 ∧
        (y : ℝ) / 2 ^ 40 < ((y / 2 ^ 40 : ℤ) : ℝ) + 1 := by
      have a := Int.ediv_mul_le y (by norm_num : (2 : ℤ) ^ 40 ≠ 0)
      have b := Int.lt_ediv_add_one_mul_self y (by norm_num : (0 : ℤ) < 2 ^ 40)
      constructor
      · rw [le_div_iff₀ (by positivity)]; exact_mod_cast a
      · rw [div_lt_iff₀ (by positivity)]; exact_mod_cast b
    rw [ha, Yr]
    have : ((y / 2 ^ 40 : ℤ) : ℝ) / 2 ^ 72 - ((y : ℝ) + j * ((L : ℝ) - Real.log 2 * 2 ^ 104)) / 2 ^ 112 =
        (((y / 2 ^ 40 : ℤ) : ℝ) - (y : ℝ) / 2 ^ 40) / 2 ^ 72 -
          (j * ((L : ℝ) - Real.log 2 * 2 ^ 104)) / 2 ^ 112 := by ring
    rw [this]
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 72)]
      exact div_le_div_of_nonneg_right (abs_le.mpr ⟨by linarith only [fl2], by linarith only [fl1]⟩) (by positivity)
    · rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 112), div_le_iff₀ (by positivity)]
      exact jL.trans (by norm_num)
  have Ytop : (k : ℝ) / 256 * Real.log 2 + Y ≤ Real.log 2 + 1 / 2 ^ 90 := by
    have kk : (k : ℝ) ≤ 255 := by exact_mod_cast Nat.le_of_lt_succ hk
    have y1R : (y : ℝ) < L := by exact_mod_cast yL
    have Lu : (L : ℝ) ≤ Real.log 2 * 2 ^ 104 + 1 / 2 := by linarith only [(abs_le.mp eL).2]
    have jj := (abs_le.mp jL).2
    have a1 : Y ≤ (L + (2 ^ 15 + 1) * (1 / 2)) / 2 ^ 112 := by
      rw [Yr]; exact div_le_div_of_nonneg_right (by linarith only [y1R, jj]) (by positivity)
    have a2 : (k : ℝ) / 256 * Real.log 2 ≤ 255 / 256 * Real.log 2 :=
      mul_le_mul_of_nonneg_right (by linarith only [kk]) (by linarith only [log_two_ge'])
    have a3 : (L + (2 ^ 15 + 1) * (1 / 2) : ℝ) / 2 ^ 112 ≤ Real.log 2 / 256 + 1 / 2 ^ 90 := by
      rw [div_le_iff₀ (by positivity)]; linarith only [Lu]
    linarith only [a1, a2, a3]
  refine ⟨dAY, ?_⟩
  rw [Real.rpow_def_of_pos two_pos, ← Real.exp_add]
  have z0 : |(1 : ℝ) / 2 ^ 90| ≤ 1 := by norm_num
  have := (abs_le.mp (Real.abs_exp_sub_one_le z0)).2
  calc Real.exp (Real.log 2 * ((k : ℝ) / 256) + Y) ≤ Real.exp (Real.log 2 + 1 / 2 ^ 90) :=
        Real.exp_le_exp.mpr (by linarith only [Ytop])
    _ = 2 * Real.exp (1 / 2 ^ 90) := by rw [Real.exp_add, Real.exp_log two_pos]
    _ ≤ 2 * (1 + 2 * |(1 : ℝ) / 2 ^ 90|) := by linarith only [this]
    _ ≤ 2 + 1 / 2 ^ 80 := by norm_num

/-- `m` within `0.81 · 2^56` of `T · e^A · 2^126`, `0 ≤ T`, `T · e^Y ≤ 2 + 2^-80` and
`|A - Y| ≤ 2^-72 + 2^-97`: `T · e^Y · 2^126 ≤ 2^128`, and `m` is within `1.4 · 2^56` of it. -/
theorem exp_tail_near (m : ℕ) (T A Y : ℝ) (T0 : 0 ≤ T) (T2 : T * Real.exp Y ≤ 2 + 1 / 2 ^ 80)
    (dAY : |A - Y| ≤ 1 / 2 ^ 72 + 1 / 2 ^ 97) (hm : |(m : ℝ) - T * Real.exp A * 2 ^ 126| ≤ 81 / 100 * 2 ^ 56) :
    T * Real.exp Y * 2 ^ 126 ≤ 2 ^ 128 ∧ |(m : ℝ) - T * Real.exp Y * 2 ^ 126| ≤ 14 / 10 * 2 ^ 56 := by
  have es := exp_shift_near A Y _ (1 / 2 ^ 60) dAY (by norm_num) (by norm_num)
  refine ⟨(mul_le_mul_of_nonneg_right T2 (by positivity)).trans (by norm_num), ?_⟩
  calc |(m : ℝ) - T * Real.exp Y * 2 ^ 126|
      ≤ |(m : ℝ) - T * Real.exp A * 2 ^ 126| + |T * 2 ^ 126 * (Real.exp A - Real.exp Y)| := by
        rw [show (m : ℝ) - T * Real.exp Y * 2 ^ 126 =
          ((m : ℝ) - T * Real.exp A * 2 ^ 126) + T * 2 ^ 126 * (Real.exp A - Real.exp Y) by ring]
        exact abs_add_le _ _
    _ ≤ 81 / 100 * 2 ^ 56 + 2 ^ 126 * ((2 + 1 / 2 ^ 80) * ((1 + 1 / 2 ^ 60) * (1 / 2 ^ 72 + 1 / 2 ^ 97))) := by
        refine add_le_add hm ?_
        rw [abs_mul, abs_of_nonneg (by positivity),
          show T * 2 ^ 126 * |Real.exp A - Real.exp Y| = 2 ^ 126 * (T * |Real.exp A - Real.exp Y|) by ring]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc T * |Real.exp A - Real.exp Y|
            ≤ T * (Real.exp Y * ((1 + 1 / 2 ^ 60) * (1 / 2 ^ 72 + 1 / 2 ^ 97))) :=
              mul_le_mul_of_nonneg_left es T0
          _ = T * Real.exp Y * ((1 + 1 / 2 ^ 60) * (1 / 2 ^ 72 + 1 / 2 ^ 97)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right T2 (by positivity)
    _ ≤ 14 / 10 * 2 ^ 56 := by norm_num

end Fulcrum

end
