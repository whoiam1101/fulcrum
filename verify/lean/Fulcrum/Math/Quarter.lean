module

public import Fulcrum.Math.Fixed

/-!
# `sin (a + θ)` of the quarter table (INTERNALS §3.11)

`quarterN` is `sin_quarter` off the table points on naturals: from the entries
`s ≈ sin a` and `c ≈ cos a` of `SIN_QUARTER` and the remainder `θ` it adds
`cos a · sin θ - sin a · (1 - cos θ)` to `s`, both short series in `z = θ²`, every
product truncated to 62 bits. `quarter_near`: the result is within `6.1` units
of `sin (a + θ) · 2^62`. The steps follow the error budget of §3.11: `θ` within
`1.002`, `z` within `1.013`, `sin θ` within `2.016` and `1 - cos θ` within `2.508`
of their ideal values, the dropped terms of the series `0.31` and `0.001`, and
`2.509 sin a + 2.326 cos a ≤ 3.43` by Cauchy–Schwarz.
-/

@[expose] public section

open Finset

namespace Fulcrum

/-- `sin (a + θ)` of `sin_quarter` from `s ≈ sin a`, `c ≈ cos a`, `B = θ · 2^62 / (π/2)`. -/
def quarterN (s c B P : ℕ) : ℕ :=
  let θ := mul62 B P
  let z := mul62 θ θ
  let sb := mul62 θ (2 ^ 62 - mul62 (z / 6) (2 ^ 62 - z / 20))
  let omc := mul62 (z / 2) (2 ^ 62 - mul62 (z / 12) (2 ^ 62 - z / 30))
  s - mul62 s omc + mul62 c sb

/-- `⌊a · b / 2^62⌋ ≤ a` for `b ≤ 2^62`. -/
theorem mul62_le_left (a b : ℕ) (hb : b ≤ 2 ^ 62) : mul62 a b ≤ a :=
  Nat.div_le_of_le_mul (by rw [mul_comm]; exact Nat.mul_le_mul_right a hb)

/-- `⌊a · b / 2^62⌋ ≤ a · b / 2^62` over the reals. -/
theorem mul62_real_le (a b : ℕ) : (mul62 a b : ℝ) ≤ a * b / 2 ^ 62 := by
  have h := (floor_div_near (a * b) (2 ^ 62) (by positivity)).1
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at h
  exact h

/-- `mul_near` stated for `mul62`. -/
theorem mul62_near (a b : ℕ) (A B ea eb MA Mb : ℝ) (ha : |(a : ℝ) - A| ≤ ea)
    (hb : |(b : ℝ) - B| ≤ eb) (hA0 : 0 ≤ A) (hA : A ≤ MA) (hbM : (b : ℝ) ≤ Mb) :
    |(mul62 a b : ℝ) - A * B / 2 ^ 62| ≤ (ea * Mb + MA * eb) / 2 ^ 62 + 1 :=
  mul_near a b A B ea eb MA Mb ha hb hA0 hA hbM



/-- The triangle inequality for five terms. -/
theorem abs_five_le (a b c d e : ℝ) : |a - b + c + d + e| ≤ |a| + |b| + |c| + |d| + |e| :=
  (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
    (add_le_add (abs_sub _ _) le_rfl)) le_rfl)) le_rfl)

/-- A floor division of `z ≤ 2^62` is at most `2^62`. -/
theorem div_le_U (z d : ℕ) (hz : z ≤ 2 ^ 62) : z / d ≤ 2 ^ 62 := (Nat.div_le_self z d).trans hz

set_option maxRecDepth 10000 in
/-- `sin_quarter` off the table points: `sin (a + θ)` from table values `s`, `c`
within `½` of `sin a · 2^62`, `cos a · 2^62`, and `θ = B · (π/2) / 2^62` with
`B < 2^54`, through `π/2` within `½` (`P`), is within `6.1` units of
`sin (a + θ) · 2^62`. -/
theorem quarter_near (s c B P : ℕ) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ Real.pi / 2)
    (hs : |(s : ℝ) - 2 ^ 62 * Real.sin a| ≤ 1 / 2) (hc : |(c : ℝ) - 2 ^ 62 * Real.cos a| ≤ 1 / 2)
    (hB : B ≤ 2 ^ 54) (hP : |(P : ℝ) - 2 ^ 62 * (Real.pi / 2)| ≤ 1 / 2) :
    |(quarterN s c B P : ℝ) - 2 ^ 62 * Real.sin (a + B * (Real.pi / 2) / 2 ^ 62)| ≤ 61 / 10 := by
  have pi2 : Real.pi / 2 ≤ 63 / 40 :=
    (div_le_div_of_nonneg_right Real.pi_lt_d2.le zero_le_two).trans (by norm_num)
  have pi0 : 0 ≤ Real.pi / 2 := by positivity
  have hB' : (B : ℝ) ≤ 2 ^ 54 := by exact_mod_cast hB
  have hP' : (P : ℝ) ≤ 2 ^ 62 * (63 / 40) + 1 / 2 :=
    (sub_le_iff_le_add'.mp (abs_le.mp hP).2).trans
      (add_le_add (mul_le_mul_of_nonneg_left pi2 (by positivity)) le_rfl)
  unfold quarterN
  dsimp only
  set Θ : ℝ := B * (Real.pi / 2) with hΘ
  have Θ0 : 0 ≤ Θ := by positivity
  have ΘM : Θ ≤ 2 ^ 54 * (63 / 40) := mul_le_mul hB' pi2 pi0 (by positivity)
  generalize ht : mul62 B P = t
  have et : |(t : ℝ) - Θ| ≤ 1002 / 1000 := by
    have h := mul62_near B P B (2 ^ 62 * (Real.pi / 2)) 0 (1 / 2) (2 ^ 54) _
      (by rw [sub_self, abs_zero]) hP (Nat.cast_nonneg B) hB' hP'
    rw [ht, show (B : ℝ) * (2 ^ 62 * (Real.pi / 2)) / 2 ^ 62 = Θ by rw [hΘ]; field_simp] at h
    exact h.trans (by norm_num)
  have tM : (t : ℝ) ≤ 2 ^ 54 * (63 / 40) + 1 := by
    rw [← ht]
    refine (mul62_real_le B P).trans ((div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ 62)).mpr ?_)
    calc (B : ℝ) * P ≤ 2 ^ 54 * (2 ^ 62 * (63 / 40) + 1 / 2) :=
          mul_le_mul hB' hP' (Nat.cast_nonneg P) (by positivity)
      _ ≤ (2 ^ 54 * (63 / 40) + 1) * 2 ^ 62 := by norm_num
  set Z : ℝ := Θ * Θ / 2 ^ 62 with hZ
  have Z0 : 0 ≤ Z := by positivity
  have ZM : Z ≤ 2 ^ 46 * (5 / 2) := by
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ 62)).mpr ((mul_le_mul ΘM ΘM Θ0 (by positivity)).trans (by norm_num))
  generalize hz : mul62 t t = z
  have ez : |(z : ℝ) - Z| ≤ 1013 / 1000 := by
    have h := mul62_near t t Θ Θ _ _ _ _ et et Θ0 ΘM tM
    rw [hz] at h
    exact h.trans (by norm_num)
  have zM : (z : ℝ) ≤ 2 ^ 46 * (5 / 2) := by
    rw [← hz]
    exact (mul62_real_le t t).trans ((div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ 62)).mpr
      ((mul_le_mul tM tM (Nat.cast_nonneg t) (by positivity)).trans (by norm_num)))
  have zU : z ≤ 2 ^ 62 := by
    have h : (z : ℝ) ≤ 2 ^ 62 := zM.trans (by norm_num)
    exact_mod_cast h
  have Z6 : Z / 6 ≤ 2 ^ 46 * (5 / 2) / 6 := div_le_div_of_nonneg_right ZM (by norm_num)
  have Z12 : Z / 12 ≤ 2 ^ 46 * (5 / 2) / 12 := div_le_div_of_nonneg_right ZM (by norm_num)
  have Z2 : Z / 2 ≤ 2 ^ 46 * (5 / 2) / 2 := div_le_div_of_nonneg_right ZM (by norm_num)
  have e9 := div_near z 20 Z _ (by norm_num) ez
  have e8 := div_near z 6 Z _ (by norm_num) ez
  push_cast at e9 e8
  have e11 := sub_near (z / 20) (Z / 20) _ e9 (div_le_U z 20 zU)
  have i11U : ((2 ^ 62 - z / 20 : ℕ) : ℝ) ≤ 2 ^ 62 := by exact_mod_cast Nat.sub_le _ _
  have e12 := mul62_near (z / 6) (2 ^ 62 - z / 20) (Z / 6) (2 ^ 62 - Z / 20) _ _ _ _ e8 e11
    (by positivity) Z6 i11U
  have i12U : mul62 (z / 6) (2 ^ 62 - z / 20) ≤ 2 ^ 62 :=
    (mul62_le_left _ _ (Nat.sub_le _ _)).trans (div_le_U z 6 zU)
  have e13 := sub_near _ _ _ e12 i12U
  have i13U : ((2 ^ 62 - mul62 (z / 6) (2 ^ 62 - z / 20) : ℕ) : ℝ) ≤ 2 ^ 62 := by
    exact_mod_cast Nat.sub_le _ _
  have esb := mul62_near t _ Θ _ _ _ _ _ et e13 Θ0 ΘM i13U
  have e14 := div_near z 2 Z _ (by norm_num) ez
  have e15 := div_near z 12 Z _ (by norm_num) ez
  have e16 := div_near z 30 Z _ (by norm_num) ez
  push_cast at e14 e15 e16
  have e17 := sub_near (z / 30) (Z / 30) _ e16 (div_le_U z 30 zU)
  have i17U : ((2 ^ 62 - z / 30 : ℕ) : ℝ) ≤ 2 ^ 62 := by exact_mod_cast Nat.sub_le _ _
  have e18 := mul62_near (z / 12) (2 ^ 62 - z / 30) (Z / 12) (2 ^ 62 - Z / 30) _ _ _ _ e15 e17
    (by positivity) Z12 i17U
  have i18U : mul62 (z / 12) (2 ^ 62 - z / 30) ≤ 2 ^ 62 :=
    (mul62_le_left _ _ (Nat.sub_le _ _)).trans (div_le_U z 12 zU)
  have e19 := sub_near _ _ _ e18 i18U
  have i19U : ((2 ^ 62 - mul62 (z / 12) (2 ^ 62 - z / 30) : ℕ) : ℝ) ≤ 2 ^ 62 := by
    exact_mod_cast Nat.sub_le _ _
  have eomc := mul62_near (z / 2) _ (Z / 2) _ _ _ _ _ e14 e19 (by positivity) Z2 i19U
  have esb' := esb.trans (show _ ≤ (2016 / 1000 : ℝ) by norm_num)
  have eomc' := eomc.trans (show _ ≤ (2508 / 1000 : ℝ) by norm_num)
  have θ0 : 0 ≤ Θ / 2 ^ 62 := by positivity
  have θM : Θ / 2 ^ 62 ≤ 63 / 10240 :=
    (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ 62)).mpr (ΘM.trans (by norm_num))
  generalize hθ : Θ / 2 ^ 62 = θ at θ0 θM ⊢
  have hΘθ : Θ = θ * 2 ^ 62 := by rw [← hθ]; field_simp
  have θ2 : θ ^ 2 ≤ (63 / 10240) ^ 2 := pow_le_pow_left₀ θ0 θM 2
  have rs : |2 ^ 62 * Real.sin θ - Θ * (2 ^ 62 - Z / 6 * (2 ^ 62 - Z / 20) / 2 ^ 62) / 2 ^ 62| ≤
      31 / 100 := by
    have h := sin_sub_sum_le θ 3 (by
      refine (pow_le_pow_left₀ θ0 θM 2).trans_lt (by norm_num))
    norm_num [sum_range_succ, Nat.factorial, abs_of_nonneg θ0] at h
    have poly : Θ * (2 ^ 62 - Z / 6 * (2 ^ 62 - Z / 20) / 2 ^ 62) / 2 ^ 62 =
        2 ^ 62 * (θ + -θ ^ 3 / 6 + θ ^ 5 / 120) := by
      rw [hZ, hΘθ]; field_simp; ring
    rw [poly, ← mul_sub (2 ^ 62 : ℝ) (Real.sin θ) (θ + -θ ^ 3 / 6 + θ ^ 5 / 120),
      abs_mul (2 ^ 62 : ℝ), abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 62)]
    refine (mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 2 ^ 62)).trans ?_
    have d : (99 / 100 : ℝ) ≤ 1 - θ ^ 2 / 64 := by
      have : θ ^ 2 / 64 ≤ (63 / 10240) ^ 2 / 64 := div_le_div_of_nonneg_right θ2 (by norm_num)
      have c : (63 / 10240 : ℝ) ^ 2 / 64 ≤ 1 / 100 := by norm_num
      exact (sub_le_sub_left (this.trans c) 1).trans_eq' (by norm_num)
    have n7 : θ ^ 7 ≤ (63 / 10240) ^ 7 := pow_le_pow_left₀ θ0 θM 7
    calc (2 : ℝ) ^ 62 * (θ ^ 7 / 5040 / (1 - θ ^ 2 / 64))
        ≤ 2 ^ 62 * ((63 / 10240) ^ 7 / 5040 / (99 / 100)) :=
          mul_le_mul_of_nonneg_left (div_le_div₀ (by positivity)
            (div_le_div_of_nonneg_right n7 (by norm_num)) (by norm_num) d) (by positivity)
      _ ≤ 31 / 100 := by norm_num
  have rc : |2 ^ 62 * (1 - Real.cos θ) - Z / 2 * (2 ^ 62 - Z / 12 * (2 ^ 62 - Z / 30) / 2 ^ 62) / 2 ^ 62| ≤
      1 / 1000 := by
    have h := cos_sub_sum_le θ 4 (by
      refine (pow_le_pow_left₀ θ0 θM 2).trans_lt (by norm_num))
    norm_num [sum_range_succ, Nat.factorial, abs_of_nonneg θ0] at h
    have poly : Z / 2 * (2 ^ 62 - Z / 12 * (2 ^ 62 - Z / 30) / 2 ^ 62) / 2 ^ 62 =
        2 ^ 62 * (1 - (1 + -θ ^ 2 / 2 + θ ^ 4 / 24 + -θ ^ 6 / 720)) := by
      rw [hZ, hΘθ]; field_simp; ring
    have e : (2 : ℝ) ^ 62 * (1 - Real.cos θ) - 2 ^ 62 * (1 - (1 + -θ ^ 2 / 2 + θ ^ 4 / 24 + -θ ^ 6 / 720)) =
        -(2 ^ 62 * (Real.cos θ - (1 + -θ ^ 2 / 2 + θ ^ 4 / 24 + -θ ^ 6 / 720))) := by ring
    rw [poly, e, abs_neg, abs_mul (2 ^ 62 : ℝ), abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 62)]
    refine (mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 2 ^ 62)).trans ?_
    have d : (99 / 100 : ℝ) ≤ 1 - θ ^ 2 / 81 := by
      have : θ ^ 2 / 81 ≤ (63 / 10240) ^ 2 / 81 := div_le_div_of_nonneg_right θ2 (by norm_num)
      have c : (63 / 10240 : ℝ) ^ 2 / 81 ≤ 1 / 100 := by norm_num
      exact (sub_le_sub_left (this.trans c) 1).trans_eq' (by norm_num)
    have n8 : θ ^ 8 ≤ (63 / 10240) ^ 8 := pow_le_pow_left₀ θ0 θM 8
    calc (2 : ℝ) ^ 62 * (θ ^ 8 / 40320 / (1 - θ ^ 2 / 81))
        ≤ 2 ^ 62 * ((63 / 10240) ^ 8 / 40320 / (99 / 100)) :=
          mul_le_mul_of_nonneg_left (div_le_div₀ (by positivity)
            (div_le_div_of_nonneg_right n8 (by norm_num)) (by norm_num) d) (by positivity)
      _ ≤ 1 / 1000 := by norm_num
  have omcU : mul62 (z / 2) (2 ^ 62 - mul62 (z / 12) (2 ^ 62 - z / 30)) ≤ 2 ^ 62 :=
    (mul62_le_left _ _ (Nat.sub_le _ _)).trans (div_le_U z 2 zU)
  have omcM : (mul62 (z / 2) (2 ^ 62 - mul62 (z / 12) (2 ^ 62 - z / 30)) : ℝ) ≤ 2 ^ 46 * (5 / 2) / 2 := by
    have h1 : mul62 (z / 2) (2 ^ 62 - mul62 (z / 12) (2 ^ 62 - z / 30)) ≤ z / 2 :=
      mul62_le_left _ _ (Nat.sub_le _ _)
    have h2 : ((z / 2 : ℕ) : ℝ) ≤ (z : ℝ) / 2 := by
      have := Nat.cast_div_le (α := ℝ) (m := z) (n := 2); push_cast at this; exact this
    exact (Nat.cast_le.mpr h1).trans (h2.trans (div_le_div_of_nonneg_right zM zero_le_two))
  have sbM : (mul62 t (2 ^ 62 - mul62 (z / 6) (2 ^ 62 - z / 20)) : ℝ) ≤ 2 ^ 54 * (63 / 40) + 1 :=
    (Nat.cast_le.mpr (mul62_le_left _ _ (Nat.sub_le _ _))).trans tM
  generalize mul62 t (2 ^ 62 - mul62 (z / 6) (2 ^ 62 - z / 20)) = sb at esb' sbM ⊢
  generalize mul62 (z / 2) (2 ^ 62 - mul62 (z / 12) (2 ^ 62 - z / 30)) = omc at eomc' omcU omcM ⊢
  have S0 : 0 ≤ 2 ^ 62 * Real.sin a :=
    mul_nonneg (by positivity) (Real.sin_nonneg_of_nonneg_of_le_pi ha0 (ha1.trans (half_le_self Real.pi_pos.le)))
  have C0 : 0 ≤ 2 ^ 62 * Real.cos a :=
    mul_nonneg (by positivity) (Real.cos_nonneg_of_mem_Icc ⟨(neg_nonpos.mpr pi0).trans ha0, ha1⟩)
  have e20 := mul62_near s omc _ _ _ _ _ _ hs eomc' S0 le_rfl omcM
  have e22 := mul62_near c sb _ _ _ _ _ _ hc esb' C0 le_rfl sbM
  have sub : mul62 s omc ≤ s := mul62_le_left s omc omcU
  have cs : (2509 / 1000) * (2 ^ 62 * Real.sin a) + (2326 / 1000) * (2 ^ 62 * Real.cos a) ≤
      (343 / 100) * 2 ^ 62 :=
    two_term_le _ _ _ _ _ _ (by rw [mul_pow, mul_pow, ← mul_add, Real.sin_sq_add_cos_sq, mul_one])
      (by norm_num) (by norm_num) (by positivity)
  rw [Nat.cast_add, Nat.cast_sub sub, Real.sin_add]
  set Sv := 2 ^ 62 * Real.sin a
  set Cv := 2 ^ 62 * Real.cos a
  set OMC := Z / 2 * (2 ^ 62 - Z / 12 * (2 ^ 62 - Z / 30) / 2 ^ 62) / 2 ^ 62
  set SB := Θ * (2 ^ 62 - Z / 6 * (2 ^ 62 - Z / 20) / 2 ^ 62) / 2 ^ 62
  have key : (s : ℝ) - mul62 s omc + mul62 c sb -
      2 ^ 62 * (Real.sin a * Real.cos θ + Real.cos a * Real.sin θ) =
      ((s : ℝ) - Sv) - ((mul62 s omc : ℝ) - Sv * OMC / 2 ^ 62) +
        Sv * (2 ^ 62 * (1 - Real.cos θ) - OMC) / 2 ^ 62 + ((mul62 c sb : ℝ) - Cv * SB / 2 ^ 62) +
        Cv * (SB - 2 ^ 62 * Real.sin θ) / 2 ^ 62 := by
    simp only [Sv, Cv]; field_simp; ring
  rw [key]
  refine (abs_five_le _ _ _ _ _).trans ?_
  have t3 : |Sv * (2 ^ 62 * (1 - Real.cos θ) - OMC) / 2 ^ 62| ≤ Sv * (1 / 1000) / 2 ^ 62 := by
    rw [abs_div, abs_mul, abs_of_nonneg S0, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 62)]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left rc S0) (by positivity)
  have t5 : |Cv * (SB - 2 ^ 62 * Real.sin θ) / 2 ^ 62| ≤ Cv * (31 / 100) / 2 ^ 62 := by
    rw [abs_div, abs_mul, abs_of_nonneg C0, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 62), abs_sub_comm]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left rs C0) (by positivity)
  have cs' : ((2509 / 1000) * Sv + (2326 / 1000) * Cv) / 2 ^ 62 ≤ 343 / 100 :=
    (div_le_iff₀ (by positivity : (0 : ℝ) < 2 ^ 62)).mpr cs
  calc |(s : ℝ) - Sv| + |(mul62 s omc : ℝ) - Sv * OMC / 2 ^ 62| +
        |Sv * (2 ^ 62 * (1 - Real.cos θ) - OMC) / 2 ^ 62| + |(mul62 c sb : ℝ) - Cv * SB / 2 ^ 62| +
        |Cv * (SB - 2 ^ 62 * Real.sin θ) / 2 ^ 62|
      ≤ 1 / 2 + (((1 / 2) * (2 ^ 46 * (5 / 2) / 2) + Sv * (2508 / 1000)) / 2 ^ 62 + 1) +
          Sv * (1 / 1000) / 2 ^ 62 + (((1 / 2) * (2 ^ 54 * (63 / 40) + 1) + Cv * (2016 / 1000)) / 2 ^ 62 + 1) +
          Cv * (31 / 100) / 2 ^ 62 := add_le_add (add_le_add (add_le_add (add_le_add hs e20) t3) e22) t5
    _ = 5 / 2 + ((1 / 2) * (2 ^ 46 * (5 / 2) / 2) + (1 / 2) * (2 ^ 54 * (63 / 40) + 1)) / 2 ^ 62 +
          ((2509 / 1000) * Sv + (2326 / 1000) * Cv) / 2 ^ 62 := by ring
    _ ≤ 5 / 2 + ((1 / 2) * (2 ^ 46 * (5 / 2) / 2) + (1 / 2) * (2 ^ 54 * (63 / 40) + 1)) / 2 ^ 62 +
          343 / 100 := add_le_add le_rfl cs'
    _ ≤ 61 / 10 := by norm_num

end Fulcrum

end
