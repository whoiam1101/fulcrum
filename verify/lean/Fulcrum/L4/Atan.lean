module

public import Fulcrum.L4.Radians
public import Fulcrum.Math.Atan
public import Fulcrum.L3.Sqrt.K64

/-!
# L4: `trig::atan_unit`, `atan_ratio`, `round_angle`, `atan2`, `atan`, `cathetus`, `asin`, `acos` (INTERNALS §3.13)

On the code extracted by Aeneas, with `f ≤ 32`.

- `atan_unit(n, d)` with `n ≤ d`, `0 < d ≤ 2^64` takes `k = ⌊256 n / d⌋`, the exact
  remainder `256 n mod d` and the entry `k` of `ATAN`; the result is `atanN` of
  `Math/Atan.lean`, within `2.9` units of `atan (n/d) · 2^62` (`atan_unit_near`).
- `atan_ratio(n, d)` is within `3.4` units of `arg (d + n i) · 2^62`: above the
  diagonal `π/2 - atan_unit(d, n)`, with `½` of `FRAC_PI_2`.
- `round_angle` takes `π - A` for `x < 0` (`½` of `PI`), rounds once by `shr_round`
  and sets the sign: `roundTarget`.
- `atan2(y, x)` is within `½ + 4 / 2^(62 - f)` of `arg (x + y i) · 2^f`, the angle in
  `(-π, π]` (`arg_target`, `arg_signs`); `atan` is `atan2(raw, 2^f)`.
- `cathetus` gives `X = |raw| · 2^(62 - f)` and `⌊√(2^124 - X²)⌋` through `k64::isqrt`;
  the floor of the root moves the angle by below `1.01` units (`root_angles_near`),
  so `asin` and `acos` are within `½ + 5 / 2^(62 - f)` of `asin`, `acos (raw / 2^f) · 2^f`.
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace Fulcrum

set_option maxRecDepth 10000

/-- An entry `k ≤ 256` of `ATAN`, read by `index_usize`: within `½` of
`atan (k/256) · 2^62`, and below `2^63`. -/
theorem atan_table_spec (i : Std.Usize) (hi : i.val ≤ 256) :
    Array.index_usize fulcrum.tables.trig.ATAN i ⦃ x =>
      |(x.val : ℝ) - Real.arctan (i.val / 256) * 2 ^ 62| ≤ 1 / 2 ∧ x.val < 2 ^ 63 ⦄ := by
  have hl : i.val < fulcrum.tables.trig.ATAN.length := by
    rw [Array.length, fulcrum.tables.trig.ATAN.property]; exact Nat.lt_succ_of_le hi
  refine WP.spec_mono (Array.index_usize_spec _ i hl) fun x hx => ?_
  have e := atan_entry i.val (Nat.lt_succ_of_le hi)
  rw [getElem!_pos fulcrum.tables.trig.ATAN.val i.val
    (show i.val < fulcrum.tables.trig.ATAN.val.length from hl), ← hx] at e
  refine ⟨e, ?_⟩
  have a : Real.arctan (i.val / 256) * 2 ^ 62 ≤ 2 ^ 62 * (63 / 40) :=
    (mul_le_mul_of_nonneg_right ((Real.arctan_lt_pi_div_two _).le.trans
      ((div_le_div_of_nonneg_right Real.pi_lt_d2.le zero_le_two).trans (by norm_num))) (by positivity)).trans_eq
      (mul_comm _ _)
  have u : (x.val : ℝ) < 2 ^ 63 := by
    linarith [(abs_le.mp e).2]
  exact_mod_cast u

/-- L4 on the code: `trig::atan_unit` of `n ≤ d`, `0 < d ≤ 2^64`, never fails and
is within `2.9` units of `atan (n/d) · 2^62`. -/
theorem atan_unit_spec (n d : Std.U128) (hd : 0 < d.val) (hnd : n.val ≤ d.val) (hd64 : d.val ≤ 2 ^ 64) :
    fulcrum.trig.atan_unit n d ⦃ r =>
      |(r.val : ℝ) - Real.arctan ((n.val : ℝ) / d.val) * 2 ^ 62| ≤ 29 / 10 ⦄ := by
  have n128 : UScalarTy.U128.numBits = 128 := rfl
  have u128 : UScalar.max .U128 = 2 ^ 128 - 1 := U128_max_val
  unfold fulcrum.trig.atan_unit
  refine WP.spec_bind (UScalar.ShiftLeft_spec n fulcrum.tables.trig.STEPS _
    (by rw [trig_steps_val, n128]; omega) rfl) fun i ⟨hi, _⟩ => ?_
  rw [trig_steps_val, Nat.shiftLeft_eq, UScalar.size_def, n128,
    Nat.mod_eq_of_lt (by omega), show n.val * 2 ^ 8 = 256 * n.val by ring] at hi
  obtain ⟨k, ek, hk⟩ := UScalar.div_spec i (y := d) hd.ne'
  rw [ek, bind_ok]
  rw [hi] at hk
  obtain ⟨k256, rl, hδ, -⟩ := atan_rest n.val d.val hd hnd
  have e := Nat.mod_add_div (256 * n.val) d.val
  have kd : k.val * d.val ≤ 256 * n.val := by rw [hk]; exact Nat.div_mul_le_self _ _
  refine WP.spec_bind (UScalar.mul_spec (x := k) (y := d) (by rw [u128]; omega)) fun i1 hi1 => ?_
  refine WP.spec_bind (UScalar.sub_spec (x := i) (y := i1) (by rw [hi, hi1]; exact kd)) fun rest ⟨hr, _⟩ => ?_
  have rv : rest.val = 256 * n.val % d.val := by
    rw [hr, hi, hi1, hk]
    exact Nat.sub_eq_of_eq_add (by rw [mul_comm (256 * n.val / d.val)]; exact e.symm)
  have ck := usize_cast_val k (by rw [hk]; omega)
  have fin : ∀ T : ℕ, |(T : ℝ) - Real.arctan (((256 * n.val / d.val : ℕ) : ℝ) / 256) * 2 ^ 62| ≤ 1 / 2 →
      |(atanN T (256 * n.val % d.val * 2 ^ 62 / (256 * d.val + 256 * n.val / d.val * n.val)) : ℝ) -
        Real.arctan ((n.val : ℝ) / d.val) * 2 ^ 62| ≤ 29 / 10 :=
    fun T hT => atan_unit_near n.val d.val T hd hnd hT
  by_cases h0 : rest = 0#u128
  · rw [ite_eq_left h0, lift, bind_ok]
    have r0 : 256 * n.val % d.val = 0 := by rw [← rv, h0]; rfl
    refine WP.spec_mono (atan_table_spec _ (by rw [ck, hk]; exact k256)) fun x ⟨hx, _⟩ => ?_
    rw [ck, hk] at hx
    have := fin x.val hx
    rwa [r0, zero_mul, Nat.zero_div, atanN_zero] at this
  rw [ite_eq_right h0]
  refine WP.spec_bind (UScalar.ShiftLeft_spec rest fulcrum.tables.trig.FRAC _
    (by rw [trig_frac_val, n128]; omega) rfl) fun i2 ⟨hi2, _⟩ => ?_
  rw [trig_frac_val, Nat.shiftLeft_eq, UScalar.size_def, n128, Nat.mod_eq_of_lt (by
    rw [rv]; calc 256 * n.val % d.val * 2 ^ 62 < 2 ^ 64 * 2 ^ 62 :=
        Nat.mul_lt_mul_of_pos_right (rl.trans_le hd64) (by positivity)
      _ < 2 ^ 128 := by norm_num)] at hi2
  refine WP.spec_bind (UScalar.ShiftLeft_spec d fulcrum.tables.trig.STEPS _
    (by rw [trig_steps_val, n128]; omega) rfl) fun i3 ⟨hi3, _⟩ => ?_
  rw [trig_steps_val, Nat.shiftLeft_eq, UScalar.size_def, n128,
    Nat.mod_eq_of_lt (by omega), show d.val * 2 ^ 8 = 256 * d.val by ring] at hi3
  have kn : k.val * n.val ≤ 256 * 2 ^ 64 := Nat.mul_le_mul (by omega) (hnd.trans hd64)
  refine WP.spec_bind (UScalar.mul_spec (x := k) (y := n) (by rw [u128]; omega)) fun i4 hi4 => ?_
  refine WP.spec_bind (UScalar.add_spec (x := i3) (y := i4) (by rw [u128, hi3, hi4]; omega)) fun i5 hi5 => ?_
  have i5p : 0 < i5.val := by rw [hi5, hi3]; omega
  obtain ⟨i6, e6, h6⟩ := UScalar.div_spec i2 (y := i5) i5p.ne'
  rw [e6, bind_ok, lift, bind_ok]
  have i6v : i6.val = 256 * n.val % d.val * 2 ^ 62 / (256 * d.val + 256 * n.val / d.val * n.val) := by
    rw [h6, hi2, hi5, hi3, hi4, rv, hk]
  have cd : (UScalar.cast .U64 i6).val = i6.val := by
    rw [cast_u64_val, Nat.mod_eq_of_lt (by rw [i6v]; exact hδ.trans_lt (by norm_num))]
  generalize UScalar.cast .U64 i6 = δ at cd ⊢
  rw [i6v] at cd
  have δ54 : δ.val ≤ 2 ^ 54 := cd ▸ hδ
  have zl : mul62 δ.val δ.val ≤ 2 ^ 46 :=
    Nat.div_le_of_le_mul ((Nat.mul_le_mul δ54 δ54).trans (by norm_num))
  refine WP.spec_bind (trig_mul_le_spec δ δ _ _ δ54 δ54 (by norm_num)) fun z hz => ?_
  refine WP.spec_bind trig_one_spec fun i7 h7 => ?_
  refine WP.spec_bind (u64_div_spec i7 3#u64 3 (lit_val _ (by decide)) (by norm_num)) fun i8 h8 => ?_
  refine WP.spec_bind (u64_div_spec i7 5#u64 5 (lit_val _ (by decide)) (by norm_num)) fun i9 h9 => ?_
  refine WP.spec_bind (u64_div_spec z 7#u64 7 (lit_val _ (by decide)) (by norm_num)) fun i10 h10 => ?_
  rw [h7] at h8 h9
  rw [hz] at h10
  refine WP.spec_bind (UScalar.sub_spec (x := i9) (y := i10) (by
    rw [h9, h10]; exact (Nat.div_le_self _ _).trans (zl.trans (by norm_num)))) fun i11 ⟨h11, _⟩ => ?_
  rw [h9, h10] at h11
  refine WP.spec_bind (trig_mul_le_spec z i11 (2 ^ 46) (2 ^ 62) (hz ▸ zl)
    (by rw [h11]; exact (Nat.sub_le _ _).trans (by norm_num)) (by norm_num)) fun i12 h12 => ?_
  rw [hz, h11] at h12
  have l12 : mul62 (mul62 δ.val δ.val) (2 ^ 62 / 5 - mul62 δ.val δ.val / 7) ≤ 2 ^ 62 / 3 :=
    (mul62_le_left _ _ ((Nat.sub_le _ _).trans (by norm_num))).trans (zl.trans (by norm_num))
  refine WP.spec_bind (UScalar.sub_spec (x := i8) (y := i12) (by rw [h8, h12]; exact l12))
    fun p ⟨hp, _⟩ => ?_
  rw [h8, h12] at hp
  rw [lift, bind_ok]
  refine WP.spec_bind (atan_table_spec _ (by rw [ck, hk]; exact k256)) fun T ⟨hT, T63⟩ => ?_
  rw [ck, hk] at hT
  refine WP.spec_bind (UScalar.add_spec (x := T) (y := δ) (by
    rw [UScalar.max_def, UScalarTy.U64_numBits_eq]; omega)) fun i15 h15 => ?_
  refine WP.spec_bind (trig_mul_le_spec δ z (2 ^ 54) (2 ^ 46) δ54 (hz ▸ zl) (by norm_num)) fun i16 h16 => ?_
  rw [hz] at h16
  have i16l : i16.val ≤ 2 ^ 54 := h16 ▸ (mul62_le_left _ _ (zl.trans (by norm_num))).trans δ54
  refine WP.spec_bind (trig_mul_le_spec i16 p (2 ^ 54) (2 ^ 62) i16l
    (by rw [hp]; exact (Nat.sub_le _ _).trans (by norm_num)) (by norm_num)) fun i17 h17 => ?_
  rw [h16, hp] at h17
  have sub := (atan_series_near T.val δ.val _ hT δ54).2
  refine WP.spec_mono (UScalar.sub_spec (x := i15) (y := i17) (by rw [h15, h17]; omega)) fun r ⟨hr, _⟩ => ?_
  have rv' : r.val = atanN T.val δ.val := by
    rw [hr, h15, h17]; rfl
  rw [rv', cd]
  exact fin T.val hT

/-- `arg (d + n i) ∈ [0, π/2]` for `0 ≤ d`, `0 ≤ n`. -/
theorem arg_quadrant (d n : ℝ) (hd : 0 ≤ d) (hn : 0 ≤ n) :
    0 ≤ Complex.arg ⟨d, n⟩ ∧ Complex.arg ⟨d, n⟩ ≤ Real.pi / 2 :=
  ⟨Complex.arg_nonneg_iff.mpr hn, Complex.arg_le_pi_div_two_iff.mpr (Or.inl hd)⟩

/-- `atan (a/b) · 2^62 ≤ 2^62 · 4/5` for `0 ≤ a ≤ b`: at most `π/4`. -/
theorem arctan_le_quarter (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    Real.arctan (a / b) * 2 ^ 62 ≤ 2 ^ 62 * (4 / 5) := by
  have q : a / b ≤ 1 := div_le_one_of_le₀ hab (ha.trans hab)
  have : Real.arctan (a / b) ≤ 4 / 5 :=
    (Real.arctan_mono q).trans (by rw [Real.arctan_one]; linarith [Real.pi_lt_d2])
  nlinarith

/-- L4 on the code: `trig::atan_ratio` of `n, d ≤ 2^64`, not both `0`, never fails
and is within `3.4` units of `arg (d + n i) · 2^62 = atan (n/d) · 2^62`. -/
theorem atan_ratio_spec (n d : Std.U128) (hn : n.val ≤ 2 ^ 64) (hd : d.val ≤ 2 ^ 64)
    (h0 : 0 < n.val ∨ 0 < d.val) :
    fulcrum.trig.atan_ratio n d ⦃ a =>
      |(a.val : ℝ) - Complex.arg ⟨d.val, n.val⟩ * 2 ^ 62| ≤ 34 / 10 ⦄ := by
  unfold fulcrum.trig.atan_ratio
  by_cases h : n ≤ d
  · have h' : n.val ≤ d.val := h
    rw [ite_eq_left h]
    refine WP.spec_mono (atan_unit_spec n d (by omega) h' hd) fun a ha => ?_
    rw [arg_of_pos _ _ (by exact_mod_cast (show 0 < d.val by omega))]
    exact ha.trans (by norm_num)
  · have h' : d.val < n.val := Nat.lt_of_not_le h
    rw [ite_eq_right h]
    refine WP.spec_bind (atan_unit_spec d n (by omega) h'.le hn) fun a ha => ?_
    have q := arctan_le_quarter (d.val : ℝ) n.val (Nat.cast_nonneg _) (by exact_mod_cast h'.le)
    have P := frac_pi_2_entry
    have le : a.val ≤ fulcrum.tables.trig.FRAC_PI_2.val := by
      have : (a.val : ℝ) ≤ fulcrum.tables.trig.FRAC_PI_2.val := by
        linarith [(abs_le.mp ha).2, (abs_le.mp P).1, Real.pi_gt_three]
      exact_mod_cast this
    refine WP.spec_mono (UScalar.sub_spec (x := fulcrum.tables.trig.FRAC_PI_2) (y := a) le) fun r ⟨hr, _⟩ => ?_
    rw [hr, Nat.cast_sub le, arg_compl _ _ (Nat.cast_nonneg _) (by exact_mod_cast (show 0 < n.val by omega))]
    have e : (fulcrum.tables.trig.FRAC_PI_2.val : ℝ) - a.val -
        (Real.pi / 2 - Real.arctan ((d.val : ℝ) / n.val)) * 2 ^ 62 =
        ((fulcrum.tables.trig.FRAC_PI_2.val : ℝ) - Real.pi / 2 * 2 ^ 62) -
          ((a.val : ℝ) - Real.arctan ((d.val : ℝ) / n.val) * 2 ^ 62) := by ring
    rw [e]
    exact (abs_sub _ _).trans ((add_le_add P ha).trans (by norm_num))

/-- The value of `tables::trig::PI`. -/
theorem pi_val : fulcrum.tables.trig.PI.val = 14488038916154245685 := by
  unfold fulcrum.tables.trig.PI; rfl

/-- The angle of `round_angle`: `A`, or `π - A` for `x < 0`, with the sign of `negative`. -/
noncomputable def roundTarget (xn ng : Bool) (A : ℝ) : ℝ :=
  (if ng then -1 else 1) * (if xn then Real.pi - A else A)

/-- L4 on the code: `trig::round_angle` of `a` within `E ≤ 100` of `A · 2^62`,
`A ∈ [0, π/2]`, `f ≤ 32`, never fails and is within `½ + (E + ½) / 2^(62 - f)` of
`roundTarget · 2^f`. -/
theorem round_angle_spec (a : Std.U64) (xn ng : Bool) (f : Std.U32) (hf : f.val ≤ 32) (A E : ℝ)
    (hA0 : 0 ≤ A) (hA : A ≤ Real.pi / 2) (hE : E ≤ 100) (ha : |(a.val : ℝ) - A * 2 ^ 62| ≤ E) :
    fulcrum.trig.round_angle a xn ng f ⦃ r =>
      |(r.val : ℝ) - roundTarget xn ng A * 2 ^ f.val| ≤ 1 / 2 + (E + 1 / 2) / 2 ^ (62 - f.val) ⦄ := by
  unfold fulcrum.trig.round_angle
  set θ : ℝ := if xn then Real.pi - A else A with hθ
  have θ0 : 0 ≤ θ := by rw [hθ]; split <;> linarith [Real.pi_gt_three]
  have θπ : θ ≤ Real.pi := by rw [hθ]; split <;> linarith [Real.pi_gt_three]
  refine WP.spec_bind (Pₘ := fun a1 : Std.U64 => |(a1.val : ℝ) - θ * 2 ^ 62| ≤ E + 1 / 2) ?_ fun a1 h1 => ?_
  · cases xn
    · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok, hθ]
      exact ha.trans (by linarith)
    · simp only [↓reduceIte, hθ]
      have P := pi_entry
      have le : a.val ≤ fulcrum.tables.trig.PI.val := by
        have : (a.val : ℝ) ≤ fulcrum.tables.trig.PI.val := by
          linarith [(abs_le.mp ha).2, (abs_le.mp P).1, Real.pi_gt_three]
        exact_mod_cast this
      refine WP.spec_mono (UScalar.sub_spec (x := fulcrum.tables.trig.PI) (y := a) le) fun r ⟨hr, _⟩ => ?_
      rw [hr, Nat.cast_sub le]
      have e : (fulcrum.tables.trig.PI.val : ℝ) - a.val - (Real.pi - A) * 2 ^ 62 =
          ((fulcrum.tables.trig.PI.val : ℝ) - Real.pi * 2 ^ 62) - ((a.val : ℝ) - A * 2 ^ 62) := by ring
      rw [e]
      exact (abs_sub _ _).trans ((add_le_add P ha).trans_eq (add_comm _ _))
  have hc : (UScalar.hcast .I128 a1).val = a1.val := by
    have mb : (a1.val : ℤ) < 2 ^ 64 := by exact_mod_cast a1.bv.isLt
    rw [UScalar.hcast_val_eq, IScalarTy.I128_numBits_eq]
    exact Int.bmod_eq_of_le ((neg_nonpos.mpr (by positivity)).trans (Int.natCast_nonneg _))
      (mb.trans_le (by norm_num))
  rw [lift, bind_ok]
  refine WP.spec_bind (UScalar.sub_spec (x := fulcrum.tables.trig.FRAC) (y := f)
    (by rw [trig_frac_val]; omega)) fun i4 ⟨hi4, _⟩ => ?_
  rw [trig_frac_val] at hi4
  refine WP.spec_bind (shr_round_spec _ i4) fun i5 hi5 => ?_
  rw [hc, hi4] at hi5
  have near := round_shift_near a1.val (62 - f.val) f.val (by omega) θ (E + 1 / 2) (by exact_mod_cast h1)
  rw [← hi5] at near
  have err : 1 / 2 + (E + 1 / 2) / 2 ^ (62 - f.val) ≤ (101 : ℝ) := by
    have : (E + 1 / 2) / 2 ^ (62 - f.val) ≤ E + 1 / 2 :=
      div_le_self (by linarith [abs_nonneg ((a.val : ℝ) - A * 2 ^ 62)]) (one_le_pow₀ one_le_two)
    linarith
  have i5b : |(i5.val : ℝ)| ≤ 2 ^ 34 := by
    have sf : |θ * 2 ^ f.val| ≤ 2 ^ 34 - 101 := by
      rw [abs_of_nonneg (by positivity)]
      have : (2 : ℝ) ^ f.val ≤ 2 ^ 32 := pow_le_pow_right₀ one_le_two hf
      nlinarith [Real.pi_lt_d2]
    calc |(i5.val : ℝ)| ≤ |(i5.val : ℝ) - θ * 2 ^ f.val| + |θ * 2 ^ f.val| :=
          sub_le_iff_le_add.mp (abs_sub_abs_le_abs_sub _ _)
      _ ≤ 101 + (2 ^ 34 - 101) := add_le_add (near.trans err) sf
      _ = 2 ^ 34 := by ring
  have i5i : -(2 ^ 34) ≤ i5.val ∧ i5.val ≤ 2 ^ 34 := by
    have ⟨l, u⟩ := abs_le.mp i5b
    exact ⟨by exact_mod_cast l, by exact_mod_cast u⟩
  have inr : InRange 63 i5.val :=
    ⟨(by unfold minOf; norm_num : minOf 63 ≤ -(2 ^ 34)).trans i5i.1,
      i5i.2.trans (by unfold maxOf; norm_num)⟩
  have cv : (IScalar.cast .I64 i5).val = i5.val :=
    (IScalar.cast_val_eq .I64 i5).trans ((wrap_eq_self_iff 63 _).2 inr)
  rw [lift, bind_ok]
  unfold roundTarget
  rw [← hθ]
  cases ng
  · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok, one_mul, cv]
    exact near
  · simp only [↓reduceIte]
    refine WP.spec_mono (IScalar.neg_step _ (fun e => ?_)) fun r hr => ?_
    · rw [cv, IScalar.min_def, IScalarTy.I64_numBits_eq] at e
      have := i5i.1; omega
    · rw [hr, cv]; push_cast
      rw [show -(i5.val : ℝ) - -1 * θ * 2 ^ f.val = -((i5.val : ℝ) - θ * 2 ^ f.val) by ring, abs_neg]
      exact near

/-- `arg (x + y i)` of integers as `roundTarget` of the angle of `|x| + |y| i`. -/
theorem arg_target (x y : ℤ) : Complex.arg ⟨(x : ℝ), (y : ℝ)⟩ =
    roundTarget (decide (x < 0)) (decide (y < 0)) (Complex.arg ⟨((x.natAbs : ℕ) : ℝ), ((y.natAbs : ℕ) : ℝ)⟩) := by
  rw [arg_signs, Nat.cast_natAbs, Nat.cast_natAbs, Int.cast_abs, Int.cast_abs]
  unfold roundTarget
  simp only [Int.cast_lt_zero, decide_eq_true_eq]

/-- L4 on the code: `trig::atan2(y, x)` with `f ≤ 32` never fails and is within
`½ + 4 / 2^(62 - f)` of `arg (x + y i) · 2^f`, the angle in `(-π, π]`. -/
theorem atan2_spec (y x : Std.I64) (f : Std.U32) (hf : f.val ≤ 32) :
    fulcrum.trig.atan2 y x f ⦃ r =>
      |(r.val : ℝ) - Complex.arg ⟨(x.val : ℝ), (y.val : ℝ)⟩ * 2 ^ f.val| ≤ 1 / 2 + 4 / 2 ^ (62 - f.val) ⦄ := by
  have tail : 0 < y.val.natAbs ∨ 0 < x.val.natAbs → (do
      let i ← core.num.I64.unsigned_abs y
      let i1 ← lift (UScalar.cast .U128 i)
      let i2 ← core.num.I64.unsigned_abs x
      let i3 ← lift (UScalar.cast .U128 i2)
      let a ← fulcrum.trig.atan_ratio i1 i3
      fulcrum.trig.round_angle a (x < 0#i64) (y < 0#i64) f) ⦃ r =>
        |(r.val : ℝ) - Complex.arg ⟨(x.val : ℝ), (y.val : ℝ)⟩ * 2 ^ f.val| ≤ 1 / 2 + 4 / 2 ^ (62 - f.val) ⦄ := by
    intro h0
    refine WP.spec_bind (I64_unsigned_abs_spec y) fun i hi => ?_
    rw [lift, bind_ok]
    refine WP.spec_bind (I64_unsigned_abs_spec x) fun i2 hi2 => ?_
    rw [lift, bind_ok]
    have yl : i.val ≤ 2 ^ 64 := i.bv.isLt.le
    have xl : i2.val ≤ 2 ^ 64 := i2.bv.isLt.le
    refine WP.spec_bind (atan_ratio_spec _ _ (by rw [cast_u128_val]; exact yl) (by rw [cast_u128_val]; exact xl)
      (by rw [cast_u128_val, cast_u128_val, hi, hi2]; exact h0)) fun a ha => ?_
    rw [cast_u128_val, cast_u128_val, hi, hi2] at ha
    have ⟨A0, A1⟩ := arg_quadrant ((x.val.natAbs : ℕ) : ℝ) ((y.val.natAbs : ℕ) : ℝ) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    refine WP.spec_mono (round_angle_spec a _ _ f hf _ (34 / 10) A0 A1 (by norm_num) ha) fun r hr => ?_
    rw [arg_target]
    have dx : decide (x < 0#i64) = decide (x.val < 0) := rfl
    have dy : decide (y < 0#i64) = decide (y.val < 0) := rfl
    rw [dx, dy] at hr
    refine hr.trans (add_le_add le_rfl (div_le_div_of_nonneg_right (by norm_num) (by positivity)))
  unfold fulcrum.trig.atan2
  by_cases hy : y = 0#i64
  · have hy' : y.val = 0 := by rw [hy]; rfl
    rw [ite_eq_left hy]
    by_cases hx : x >= 0#i64
    · have hx' : 0 ≤ x.val := hx
      rw [ite_eq_left hx, WP.spec_ok]
      rw [hy', Int.cast_zero, Complex.arg_eq_zero_iff.mpr ⟨show (0 : ℝ) ≤ (x.val : ℝ) by exact_mod_cast hx', rfl⟩]
      norm_num
      positivity
    · have hx' : x.val < 0 := not_le.mp hx
      rw [ite_eq_right hx]
      exact tail (Or.inr (Int.natAbs_pos.mpr hx'.ne))
  · have hy' : y.val ≠ 0 := fun e => hy (IScalar.eq_of_val_eq (by rw [e]; rfl))
    rw [ite_eq_right hy]
    exact tail (Or.inl (Int.natAbs_pos.mpr hy'))

/-- L4 on the code: `trig::atan` with `f ≤ 32` never fails and is within
`½ + 4 / 2^(62 - f)` of `atan (raw / 2^f) · 2^f`. -/
theorem atan_spec (raw : Std.I64) (f : Std.U32) (hf : f.val ≤ 32) :
    fulcrum.trig.atan raw f ⦃ r =>
      |(r.val : ℝ) - Real.arctan (raw.val / 2 ^ f.val) * 2 ^ f.val| ≤ 1 / 2 + 4 / 2 ^ (62 - f.val) ⦄ := by
  unfold fulcrum.trig.atan
  refine WP.spec_bind (IScalar.ShiftLeft_spec 1#i64 f (by rw [IScalarTy.I64_numBits_eq]; omega)) fun i ⟨hi, _⟩ => ?_
  have iv : i.val = 2 ^ f.val := by
    have pf : (2 : ℤ) ^ f.val ≤ 2 ^ 32 := pow_le_pow_right₀ (by norm_num) hf
    rw [hi, Int.shiftLeft_eq, show (1#i64 : Std.I64).val = 1 from rfl, one_mul, IScalarTy.I64_numBits_eq]
    exact Int.bmod_eq_of_le (by push_cast; linarith [(by positivity : (0 : ℤ) ≤ 2 ^ f.val)]) (by push_cast; linarith)
  refine WP.spec_mono (atan2_spec raw i f hf) fun r hr => ?_
  rw [iv, arg_of_pos _ _ (by positivity)] at hr
  push_cast at hr
  exact hr

/-- `(2^(2f) - m²) · 2^(2(62 - f)) = 2^124 - (m · 2^(62 - f))²` for `f ≤ 62`. -/
theorem cathetus_rest (m f : ℕ) (hf : f ≤ 62) :
    (2 ^ (2 * f) - m * m) * 2 ^ (2 * (62 - f)) = 2 ^ 124 - (m * 2 ^ (62 - f)) ^ 2 := by
  rw [Nat.sub_mul, ← pow_add, show 2 * f + 2 * (62 - f) = 124 by omega, mul_pow, ← pow_mul,
    mul_comm (62 - f) 2, sq]

/-- L4 on the code: `trig::cathetus` of `|raw| ≤ 2^f`, `f ≤ 32`, never fails and
returns `X = |raw| · 2^(62 - f)` and `⌊√(2^124 - X²)⌋`. -/
theorem cathetus_spec (raw : Std.I64) (f : Std.U32) (hf : f.val ≤ 32) (hr : raw.val.natAbs ≤ 2 ^ f.val) :
    fulcrum.trig.cathetus raw f ⦃ p =>
      p.1.val = raw.val.natAbs * 2 ^ (62 - f.val) ∧
      p.2.val = Nat.sqrt (2 ^ 124 - (raw.val.natAbs * 2 ^ (62 - f.val)) ^ 2) ⦄ := by
  have n128 : UScalarTy.U128.numBits = 128 := rfl
  have u128 : UScalar.max .U128 = 2 ^ 128 - 1 := U128_max_val
  unfold fulcrum.trig.cathetus
  refine WP.spec_bind (I64_unsigned_abs_spec raw) fun i hi => ?_
  rw [lift, bind_ok]
  have mv : (UScalar.cast .U128 i).val = raw.val.natAbs := by rw [cast_u128_val, hi]
  generalize UScalar.cast .U128 i = m at mv ⊢
  refine WP.spec_bind (UScalar.mul_spec (x := 2#u32) (y := f) (by rw [lit_val, U32_max_val]; omega))
    fun i1 h1 => ?_
  rw [lit_val] at h1
  refine WP.spec_bind (UScalar.ShiftLeft_spec 1#u128 i1 _ (by rw [h1, n128]; omega) rfl) fun i2 ⟨h2, _⟩ => ?_
  have p2f : 2 ^ (2 * f.val) ≤ 2 ^ 64 := Nat.pow_le_pow_right two_pos (by omega)
  rw [lit_val, h1, Nat.shiftLeft_eq, one_mul, UScalar.size_def, n128,
    Nat.mod_eq_of_lt (p2f.trans_lt (by norm_num))] at h2
  have mm : m.val * m.val ≤ 2 ^ (2 * f.val) := by
    rw [mv, two_mul, pow_add]; exact Nat.mul_le_mul hr hr
  refine WP.spec_bind (UScalar.mul_spec (x := m) (y := m) (by rw [u128]; omega)) fun i3 h3 => ?_
  refine WP.spec_bind (UScalar.sub_spec (x := i2) (y := i3) (by rw [h2, h3]; exact mm)) fun i4 ⟨h4, _⟩ => ?_
  rw [h2, h3] at h4
  refine WP.spec_bind (UScalar.sub_spec (x := fulcrum.tables.trig.FRAC) (y := f)
    (by rw [trig_frac_val]; omega)) fun i5 ⟨h5, _⟩ => ?_
  rw [trig_frac_val] at h5
  refine WP.spec_bind (UScalar.mul_spec (x := 2#u32) (y := i5) (by rw [lit_val, U32_max_val, h5]; omega))
    fun i6 h6 => ?_
  rw [lit_val, h5] at h6
  have restv := cathetus_rest m.val f.val (by omega)
  have rl : 2 ^ 124 - (m.val * 2 ^ (62 - f.val)) ^ 2 ≤ 2 ^ 124 := Nat.sub_le _ _
  refine WP.spec_bind (UScalar.ShiftLeft_spec i4 i6 _ (by rw [h6, n128]; omega) rfl) fun rest ⟨hr', _⟩ => ?_
  rw [h6, h4, Nat.shiftLeft_eq, UScalar.size_def, n128, restv,
    Nat.mod_eq_of_lt (rl.trans_lt (by norm_num))] at hr'
  have Xl : m.val * 2 ^ (62 - f.val) ≤ 2 ^ 62 := by
    calc m.val * 2 ^ (62 - f.val) ≤ 2 ^ f.val * 2 ^ (62 - f.val) := Nat.mul_le_mul_right _ (mv ▸ hr)
      _ = 2 ^ 62 := by rw [← pow_add]; congr 1; omega
  refine WP.spec_bind (UScalar.ShiftLeft_spec m i5 _ (by rw [h5, n128]; omega) rfl) fun i7 ⟨h7, _⟩ => ?_
  rw [h5, Nat.shiftLeft_eq, UScalar.size_def, n128, Nat.mod_eq_of_lt (Xl.trans_lt (by norm_num))] at h7
  refine WP.spec_bind (k64_isqrt_spec rest (by rw [hr']; omega)) fun i8 h8 => ?_
  rw [WP.spec_ok]
  exact ⟨by rw [h7, mv], by rw [h8, hr', mv]⟩

/-- `X / 2^62 = n / 2^f` for `X = n · 2^(62 - f)`, `f ≤ 62`. -/
theorem x_ratio (n f : ℕ) (hf : f ≤ 62) : ((n * 2 ^ (62 - f) : ℕ) : ℝ) / 2 ^ 62 = n / 2 ^ f := by
  have e : (2 : ℝ) ^ 62 = 2 ^ (62 - f) * 2 ^ f := by rw [← pow_add, Nat.sub_add_cancel hf]
  rw [e]; push_cast; field_simp

/-- The root of `asin` and `acos` in units of `2^-62`: `U · 1/(U - 1) ≤ 1.01`. -/
theorem root_units : (2 : ℝ) ^ 62 * (1 / (2 ^ 62 - 1)) ≤ 101 / 100 := by norm_num

/-- The common part of `asin` and `acos`: `cathetus`, then `atan_ratio` of
`X = |raw| · 2^(62 - f)` and the root `ŝ` in either order, within `4.41` units of
the angle `B` that the exact root gives. -/
theorem cathetus_ratio_spec {α} (raw : Std.I64) (f : Std.U32) (hf : f.val ≤ 32) (hr : raw.val.natAbs ≤ 2 ^ f.val)
    (swap : Bool) (k : Std.U64 → Result α) (P : α → Prop)
    (hk : ∀ a : Std.U64, ∀ X : ℕ, X = raw.val.natAbs * 2 ^ (62 - f.val) →
      |(a.val : ℝ) - (if swap then Real.arccos (X / 2 ^ 62) else Real.arcsin (X / 2 ^ 62)) * 2 ^ 62| ≤ 441 / 100 →
      k a ⦃ P ⦄) :
    (do
      let (x, s) ← fulcrum.trig.cathetus raw f
      let a ← if swap then fulcrum.trig.atan_ratio s x else fulcrum.trig.atan_ratio x s
      k a) ⦃ P ⦄ := by
  refine WP.spec_bind (cathetus_spec raw f hf hr) fun p ⟨h1, h2⟩ => ?_
  obtain ⟨x, s⟩ := p
  dsimp only at h1 h2 ⊢
  have Xl : raw.val.natAbs * 2 ^ (62 - f.val) ≤ 2 ^ 62 := by
    calc raw.val.natAbs * 2 ^ (62 - f.val) ≤ 2 ^ f.val * 2 ^ (62 - f.val) := Nat.mul_le_mul_right _ hr
      _ = 2 ^ 62 := by rw [← pow_add]; congr 1; omega
  generalize raw.val.natAbs * 2 ^ (62 - f.val) = X at h1 h2 Xl hk
  have xl : x.val ≤ 2 ^ 64 := by rw [h1]; exact Xl.trans (by norm_num)
  have sl : s.val ≤ 2 ^ 64 := by
    rw [h2]; exact (Nat.sqrt_le_sqrt (Nat.sub_le _ _)).trans
      (by rw [show 2 ^ 124 = (2 ^ 62) ^ 2 by norm_num, Nat.sqrt_eq']; norm_num)
  have h0 : 0 < x.val ∨ 0 < s.val := by
    rcases Nat.eq_zero_or_pos X with hz | hz
    · right; rw [h2, hz, show 2 ^ 124 - 0 ^ 2 = (2 ^ 62) ^ 2 by norm_num, Nat.sqrt_eq']; positivity
    · left; rw [h1]; exact hz
  have ⟨ra, rc⟩ := root_angles_near X Xl
  have ru := root_units
  have U0 : (0 : ℝ) < 2 ^ 62 := by positivity
  cases swap
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_bind (atan_ratio_spec x s xl sl h0) fun a ha => ?_
    refine hk a X rfl ?_
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [h1, h2] at ha
    have d : |(Complex.arg ⟨(Nat.sqrt (2 ^ 124 - X ^ 2) : ℝ), (X : ℝ)⟩ - Real.arcsin (X / 2 ^ 62)) * 2 ^ 62| ≤ 101 / 100 := by
      rw [abs_mul, abs_of_pos U0, mul_comm]; exact (mul_le_mul_of_nonneg_left ra U0.le).trans ru
    calc _ ≤ |(a.val : ℝ) - Complex.arg ⟨(Nat.sqrt (2 ^ 124 - X ^ 2) : ℝ), (X : ℝ)⟩ * 2 ^ 62| +
          |(Complex.arg ⟨(Nat.sqrt (2 ^ 124 - X ^ 2) : ℝ), (X : ℝ)⟩ - Real.arcsin (X / 2 ^ 62)) * 2 ^ 62| := by
          exact (abs_sub_le _ _ _).trans_eq (by rw [sub_mul])
      _ ≤ 34 / 10 + 101 / 100 := add_le_add ha d
      _ = 441 / 100 := by norm_num
  · simp only [↓reduceIte]
    refine WP.spec_bind (atan_ratio_spec s x sl xl h0.symm) fun a ha => ?_
    refine hk a X rfl ?_
    simp only [↓reduceIte]
    rw [h1, h2] at ha
    have d : |(Complex.arg ⟨(X : ℝ), (Nat.sqrt (2 ^ 124 - X ^ 2) : ℝ)⟩ - Real.arccos (X / 2 ^ 62)) * 2 ^ 62| ≤ 101 / 100 := by
      rw [abs_mul, abs_of_pos U0, mul_comm]; exact (mul_le_mul_of_nonneg_left rc U0.le).trans ru
    calc _ ≤ |(a.val : ℝ) - Complex.arg ⟨(X : ℝ), (Nat.sqrt (2 ^ 124 - X ^ 2) : ℝ)⟩ * 2 ^ 62| +
          |(Complex.arg ⟨(X : ℝ), (Nat.sqrt (2 ^ 124 - X ^ 2) : ℝ)⟩ - Real.arccos (X / 2 ^ 62)) * 2 ^ 62| := by
          exact (abs_sub_le _ _ _).trans_eq (by rw [sub_mul])
      _ ≤ 34 / 10 + 101 / 100 := add_le_add ha d
      _ = 441 / 100 := by norm_num

/-- L4 on the code: `trig::asin` of `|raw| ≤ 2^f`, `f ≤ 32`, never fails and is
within `½ + 5 / 2^(62 - f)` of `asin (raw / 2^f) · 2^f`. -/
theorem asin_spec (raw : Std.I64) (f : Std.U32) (hf : f.val ≤ 32) (hr : raw.val.natAbs ≤ 2 ^ f.val) :
    fulcrum.trig.asin raw f ⦃ r =>
      |(r.val : ℝ) - Real.arcsin (raw.val / 2 ^ f.val) * 2 ^ f.val| ≤ 1 / 2 + 5 / 2 ^ (62 - f.val) ⦄ := by
  unfold fulcrum.trig.asin
  refine cathetus_ratio_spec raw f hf hr false _ _ fun a X hX ha => ?_
  simp only [Bool.false_eq_true, ↓reduceIte] at ha
  have q0 : (0 : ℝ) ≤ X / 2 ^ 62 := by positivity
  refine WP.spec_mono (round_angle_spec a false _ f hf _ (441 / 100) (Real.arcsin_nonneg.mpr q0)
    (Real.arcsin_le_pi_div_two _) (by norm_num) ha) fun r hr => ?_
  rw [hX, x_ratio _ _ (by omega)] at hr
  have e : Real.arcsin ((raw.val : ℝ) / 2 ^ f.val) =
      roundTarget false (decide (raw < 0#i64)) (Real.arcsin (((raw.val.natAbs : ℕ) : ℝ) / 2 ^ f.val)) := by
    unfold roundTarget
    have dr : decide (raw < 0#i64) = decide (raw.val < 0) := rfl
    rw [dr, natAbs_real]
    by_cases hn : raw.val < 0
    · simp only [hn, decide_true, ↓reduceIte, Bool.false_eq_true, neg_div, Real.arcsin_neg]; ring
    · simp only [hn, decide_false, Bool.false_eq_true, ↓reduceIte, one_mul]
  rw [e]
  exact hr.trans (add_le_add le_rfl (div_le_div_of_nonneg_right (by norm_num) (by positivity)))

/-- L4 on the code: `trig::acos` of `|raw| ≤ 2^f`, `f ≤ 32`, never fails and is
within `½ + 5 / 2^(62 - f)` of `acos (raw / 2^f) · 2^f`. -/
theorem acos_spec (raw : Std.I64) (f : Std.U32) (hf : f.val ≤ 32) (hr : raw.val.natAbs ≤ 2 ^ f.val) :
    fulcrum.trig.acos raw f ⦃ r =>
      |(r.val : ℝ) - Real.arccos (raw.val / 2 ^ f.val) * 2 ^ f.val| ≤ 1 / 2 + 5 / 2 ^ (62 - f.val) ⦄ := by
  unfold fulcrum.trig.acos
  refine cathetus_ratio_spec raw f hf hr true _ _ fun a X hX ha => ?_
  simp only [↓reduceIte] at ha
  have q0 : (0 : ℝ) ≤ X / 2 ^ 62 := by positivity
  refine WP.spec_mono (round_angle_spec a _ false f hf _ (441 / 100) (Real.arccos_nonneg _)
    (Real.arccos_le_pi_div_two.mpr q0) (by norm_num) ha) fun r hr => ?_
  rw [hX, x_ratio _ _ (by omega)] at hr
  have e : Real.arccos ((raw.val : ℝ) / 2 ^ f.val) =
      roundTarget (decide (raw < 0#i64)) false (Real.arccos (((raw.val.natAbs : ℕ) : ℝ) / 2 ^ f.val)) := by
    unfold roundTarget
    have dr : decide (raw < 0#i64) = decide (raw.val < 0) := rfl
    rw [dr, natAbs_real]
    by_cases hn : raw.val < 0
    · simp only [hn, decide_true, ↓reduceIte, Bool.false_eq_true, one_mul, neg_div, Real.arccos_neg]; ring
    · simp only [hn, decide_false, Bool.false_eq_true, ↓reduceIte, one_mul]
  rw [e]
  exact hr.trans (add_le_add le_rfl (div_le_div_of_nonneg_right (by norm_num) (by positivity)))

end Fulcrum

end
