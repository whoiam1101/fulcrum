module

public import Fulcrum.Math.Quarter
public import Fulcrum.Tables.Trig
public import Fulcrum.Lemmas.Scalar

/-!
# L4: `trig::sin_quarter` (INTERNALS §3.11)

On the code extracted by Aeneas: `sin_quarter(p, bits)` with `p ≤ 2^bits` and
`bits ≤ 62` never fails and is within `6.1` units of `sin (p / 2^bits · π/2) · 2^62`.
Up to `8` bits it reads the table (`½`); above, the entry `k` of the top bits and
the remainder `b` give the table values `s`, `c` and `θ = b · 2^(62 - bits) · π/2`,
every product stays below `2^126`, and the result is `quarterN` of
`Math/Quarter.lean`, whose bound is `quarter_near`.

`maxRecDepth` is raised for the file: `2^62` in `ℝ` comes from two instances of
the power (`Monoid.npow` and `Real.instPow`), and unifying them unfolds 62 steps
of `npowRec`.
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace Fulcrum

set_option maxRecDepth 10000

/-- `tables::trig::FRAC` is `62`. -/
theorem trig_frac_val : fulcrum.tables.trig.FRAC.val = 62 := by
  unfold fulcrum.tables.trig.FRAC; rfl

/-- `tables::trig::STEPS` is `8`. -/
theorem trig_steps_val : fulcrum.tables.trig.STEPS.val = 8 := by
  unfold fulcrum.tables.trig.STEPS; rfl

/-- `trig::ONE` is `2^62`. -/
theorem trig_one_spec : fulcrum.trig.ONE ⦃ r => r.val = 2 ^ 62 ⦄ := by
  unfold fulcrum.trig.ONE
  refine WP.spec_mono (UScalar.ShiftLeft_spec 1#u64 fulcrum.tables.trig.FRAC _
    (by rw [trig_frac_val]; exact Nat.le_of_ble_eq_true rfl) rfl) fun r ⟨hr, _⟩ => ?_
  rw [hr, trig_frac_val, lit_val, Nat.shiftLeft_eq, one_mul, UScalar.size_def, UScalarTy.U64_numBits_eq]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right one_lt_two (Nat.le_of_ble_eq_true rfl))

/-- `trig::mul` is `⌊a · b / 2^62⌋` when the quotient fits `u64`. -/
theorem trig_mul_spec (a b : Std.U64) (h : a.val * b.val < 2 ^ 126) :
    fulcrum.trig.mul a b ⦃ r => r.val = mul62 a.val b.val ⦄ := by
  unfold fulcrum.trig.mul
  have ca : (UScalar.cast .U128 a).val = a.val :=
    UScalar.cast_val_mod_pow_greater_numBits_eq _ _ (Nat.le_of_ble_eq_true rfl)
  have cb : (UScalar.cast .U128 b).val = b.val :=
    UScalar.cast_val_mod_pow_greater_numBits_eq _ _ (Nat.le_of_ble_eq_true rfl)
  rw [lift, bind_ok, lift, bind_ok]
  refine WP.spec_bind (UScalar.mul_spec (x := UScalar.cast .U128 a) (y := UScalar.cast .U128 b)
    (by rw [ca, cb, U128_max_val]
        exact Nat.le_pred_of_lt (h.trans (Nat.pow_lt_pow_right one_lt_two (Nat.le_of_ble_eq_true rfl : 126 < 128)))))
    fun i hi => ?_
  refine WP.spec_bind (UScalar.ShiftRight_spec i fulcrum.tables.trig.FRAC
    (by rw [trig_frac_val]; exact Nat.le_of_ble_eq_true rfl)) fun j ⟨hj, _⟩ => ?_
  have jv : j.val = mul62 a.val b.val := by
    rw [hj, trig_frac_val, hi, ca, cb, Nat.shiftRight_eq_div_pow]; rfl
  rw [WP.spec_ok, UScalar.cast_val_mod_pow_of_inBounds_eq _ _ ?_, jv]
  rw [jv]
  exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 62)).mpr (h.trans_eq (by norm_num))

/-- The value of `tables::trig::FRAC_PI_2`. -/
theorem frac_pi_2_val : fulcrum.tables.trig.FRAC_PI_2.val = 7244019458077122842 := by
  unfold fulcrum.tables.trig.FRAC_PI_2; rfl

/-- An entry `k ≤ 256` of `SIN_QUARTER`, read by `index_usize`: within `½` of
`sin (k/256 · π/2) · 2^62`, and at most `2^62`. -/
theorem sin_table_spec (i : Std.Usize) (hi : i.val ≤ 256) :
    Array.index_usize fulcrum.tables.trig.SIN_QUARTER i ⦃ x =>
      |(x.val : ℝ) - Real.sin (i.val / 256 * (Real.pi / 2)) * 2 ^ 62| ≤ 1 / 2 ∧ x.val ≤ 2 ^ 62 ⦄ := by
  have hl : i.val < fulcrum.tables.trig.SIN_QUARTER.length := by
    rw [Array.length, fulcrum.tables.trig.SIN_QUARTER.property]; exact Nat.lt_succ_of_le hi
  refine WP.spec_mono (Array.index_usize_spec _ i hl) fun x hx => ?_
  have e := sin_quarter_entry i.val (Nat.lt_succ_of_le hi)
  rw [getElem!_pos fulcrum.tables.trig.SIN_QUARTER.val i.val (show i.val < fulcrum.tables.trig.SIN_QUARTER.val.length from hl), ← hx] at e
  refine ⟨e, ?_⟩
  have u : (x.val : ℝ) < 2 ^ 62 + 1 := by
    have s1 : Real.sin (i.val / 256 * (Real.pi / 2)) * 2 ^ 62 ≤ 2 ^ 62 :=
      (mul_le_mul_of_nonneg_right (Real.sin_le_one _) (by positivity)).trans_eq (one_mul _)
    exact (sub_le_iff_le_add'.mp (abs_le.mp e).2).trans_lt
      ((add_le_add s1 le_rfl).trans_lt (by norm_num : (2 : ℝ) ^ 62 + 1 / 2 < 2 ^ 62 + 1))
  exact Nat.lt_succ_iff.mp (by exact_mod_cast u)

/-- `⌊a · b / 2^62⌋ ≤ ⌊A · B / 2^62⌋` for `a ≤ A`, `b ≤ B`. -/
theorem mul62_mono (a b A B : ℕ) (ha : a ≤ A) (hb : b ≤ B) : mul62 a b ≤ A * B / 2 ^ 62 :=
  Nat.div_le_div_right (Nat.mul_le_mul ha hb)

/-- `trig::mul` of operands at most `A`, `B` with `A · B < 2^126`. -/
theorem trig_mul_le_spec (a b : Std.U64) (A B : ℕ) (ha : a.val ≤ A) (hb : b.val ≤ B)
    (h : A * B < 2 ^ 126) : fulcrum.trig.mul a b ⦃ r => r.val = mul62 a.val b.val ⦄ :=
  trig_mul_spec a b ((Nat.mul_le_mul ha hb).trans_lt h)

/-- A division of a `u64` by a non-zero literal. -/
theorem u64_div_spec (x y : Std.U64) (d : ℕ) (hy : y.val = d) (hd : 0 < d) :
    (x / y) ⦃ r => r.val = x.val / d ⦄ := by
  obtain ⟨z, hz, hv⟩ := UScalar.div_spec x (y := y) (by omega)
  rw [hz, WP.spec_ok, hv, hy]

/-- `k / 256 = p / 2^bits` for `k = p · 2^(8 - bits)` and `bits ≤ 8`. -/
theorem angle_scale_up (p bits : ℕ) (hb : bits ≤ 8) :
    ((p * 2 ^ (8 - bits) : ℕ) : ℝ) / 256 = p / 2 ^ bits := by
  have e : (256 : ℝ) = 2 ^ (8 - bits) * 2 ^ bits := by
    rw [← pow_add, Nat.sub_add_cancel hb]; norm_num
  rw [e]; push_cast; field_simp

/-- L4 on the code: `trig::sin_quarter` of `p ≤ 2^bits`, `bits ≤ 62`, never fails
and is within `6.1` units of `sin (p / 2^bits · π/2) · 2^62`. -/
theorem sin_quarter_spec (p : Std.U64) (bits : Std.U32) (hb : bits.val ≤ 62)
    (hp : p.val ≤ 2 ^ bits.val) :
    fulcrum.trig.sin_quarter p bits ⦃ r =>
      |(r.val : ℝ) - Real.sin (p.val / 2 ^ bits.val * (Real.pi / 2)) * 2 ^ 62| ≤ 61 / 10 ⦄ := by
  unfold fulcrum.trig.sin_quarter
  by_cases h8 : bits ≤ fulcrum.tables.trig.STEPS
  · have h8' : bits.val ≤ 8 := trig_steps_val ▸ h8
    rw [ite_eq_left h8]
    refine WP.spec_bind (UScalar.sub_spec (x := fulcrum.tables.trig.STEPS) (y := bits)
      (by rw [trig_steps_val]; exact h8')) fun i ⟨hi, _⟩ => ?_
    rw [trig_steps_val] at hi
    have kv : p.val * 2 ^ (8 - bits.val) ≤ 256 :=
      (Nat.mul_le_mul_right _ hp).trans (by rw [← pow_add, Nat.add_sub_cancel' h8']; exact le_rfl)
    refine WP.spec_bind (UScalar.ShiftLeft_spec p i _ (by rw [hi, UScalarTy.U64_numBits_eq]; omega) rfl) fun i1 ⟨hi1, _⟩ => ?_
    rw [hi, Nat.shiftLeft_eq, UScalar.size_def, UScalarTy.U64_numBits_eq,
      Nat.mod_eq_of_lt (kv.trans_lt (Nat.le_of_ble_eq_true rfl))] at hi1
    rw [lift, bind_ok]
    have c2 := usize_cast_val i1 (by rw [hi1]; exact kv.trans_lt (Nat.le_of_ble_eq_true rfl))
    refine WP.spec_mono (sin_table_spec _ (by rw [c2, hi1]; exact kv)) fun x ⟨hx, _⟩ => ?_
    rw [c2, hi1, angle_scale_up _ _ h8'] at hx
    exact hx.trans (by norm_num)
  have h8' : 8 < bits.val := Nat.lt_of_not_le (trig_steps_val ▸ h8)
  rw [ite_eq_right h8]
  refine WP.spec_bind (UScalar.sub_spec (x := bits) (y := fulcrum.tables.trig.STEPS)
    (by rw [trig_steps_val]; exact h8'.le)) fun rest ⟨hr, _⟩ => ?_
  rw [trig_steps_val] at hr
  refine WP.spec_bind (UScalar.ShiftRight_spec p rest (by rw [hr, UScalarTy.U64_numBits_eq]; omega))
    fun k ⟨hk, _⟩ => ?_
  rw [hr, Nat.shiftRight_eq_div_pow] at hk
  have pw : 2 ^ bits.val = 2 ^ (bits.val - 8) * 256 := by
    rw [show (256 : ℕ) = 2 ^ 8 from rfl, ← pow_add, Nat.sub_add_cancel h8'.le]
  have k256 : k.val ≤ 256 := by
    rw [hk]; exact (Nat.div_le_iff_le_mul_add_pred (Nat.two_pow_pos _)).mpr (by rw [← pw]; omega)
  refine WP.spec_bind (UScalar.ShiftLeft_spec 1#u64 rest _ (by rw [hr, UScalarTy.U64_numBits_eq]; omega) rfl)
    fun i ⟨hi, _⟩ => ?_
  have pr : 2 ^ (bits.val - 8) < 2 ^ 64 := Nat.pow_lt_pow_right one_lt_two (by omega)
  rw [hr, lit_val, Nat.shiftLeft_eq, one_mul, UScalar.size_def, UScalarTy.U64_numBits_eq,
    Nat.mod_eq_of_lt pr] at hi
  refine WP.spec_bind (UScalar.sub_spec (x := i) (y := 1#u64) (by rw [hi, lit_val]; exact Nat.one_le_two_pow))
    fun i1 ⟨hi1, _⟩ => ?_
  rw [hi, lit_val] at hi1
  rw [lift, bind_ok]
  have bv : (p &&& i1).val = p.val % 2 ^ (bits.val - 8) := by
    rw [UScalar.val_and, hi1, Nat.and_two_pow_sub_one_eq_mod]
  generalize p &&& i1 = b at bv ⊢
  rw [lift, bind_ok]
  have ck := usize_cast_val k (by omega)
  refine WP.spec_bind (sin_table_spec _ (by rw [ck]; exact k256)) fun sv ⟨hs, sU⟩ => ?_
  rw [ck, hk] at hs
  have pk : p.val = 2 ^ (bits.val - 8) * (p.val / 2 ^ (bits.val - 8)) + p.val % 2 ^ (bits.val - 8) :=
    (Nat.div_add_mod _ _).symm
  by_cases hb0 : b = 0#u64
  · rw [ite_eq_left hb0, WP.spec_ok]
    have m0 : p.val % 2 ^ (bits.val - 8) = 0 := by rw [← bv, hb0]; rfl
    have ang : ((p.val / 2 ^ (bits.val - 8) : ℕ) : ℝ) / 256 = p.val / 2 ^ bits.val := by
      have pwR : (2 : ℝ) ^ bits.val = 2 ^ (bits.val - 8) * 256 := by exact_mod_cast pw
      rw [pwR, Nat.cast_div (Nat.dvd_of_mod_eq_zero m0) (by positivity)]
      push_cast; field_simp
    rw [ang] at hs
    exact hs.trans (by norm_num)
  rw [ite_eq_right hb0]
  have b54 : b.val * 2 ^ (62 - bits.val) ≤ 2 ^ 54 := by
    have bl : b.val < 2 ^ (bits.val - 8) := bv ▸ Nat.mod_lt _ (Nat.two_pow_pos _)
    calc b.val * 2 ^ (62 - bits.val) ≤ 2 ^ (bits.val - 8) * 2 ^ (62 - bits.val) :=
          Nat.mul_le_mul_right _ bl.le
      _ = 2 ^ 54 := by rw [← pow_add]; congr 1; omega
  refine WP.spec_bind (UScalar.ShiftLeft_spec 1#u64 fulcrum.tables.trig.STEPS _
    (by rw [trig_steps_val, UScalarTy.U64_numBits_eq]; omega) rfl) fun i3 ⟨hi3, _⟩ => ?_
  rw [trig_steps_val, lit_val, Nat.shiftLeft_eq, one_mul, UScalar.size_def, UScalarTy.U64_numBits_eq,
    Nat.mod_eq_of_lt (Nat.pow_lt_pow_right one_lt_two (by omega))] at hi3
  refine WP.spec_bind (UScalar.sub_spec (x := i3) (y := k) (by rw [hi3]; exact k256)) fun i4 ⟨hi4, _⟩ => ?_
  rw [hi3] at hi4
  rw [lift, bind_ok]
  have c4 := usize_cast_val i4 (by omega)
  refine WP.spec_bind (sin_table_spec _ (by rw [c4, hi4]; omega)) fun cv ⟨hc, cU⟩ => ?_
  rw [c4, hi4] at hc
  refine WP.spec_bind (UScalar.sub_spec (x := fulcrum.tables.trig.FRAC) (y := bits)
    (by rw [trig_frac_val]; exact hb)) fun i6 ⟨hi6, _⟩ => ?_
  rw [trig_frac_val] at hi6
  refine WP.spec_bind (UScalar.ShiftLeft_spec b i6 _ (by rw [hi6, UScalarTy.U64_numBits_eq]; omega) rfl)
    fun i7 ⟨hi7, _⟩ => ?_
  rw [hi6, Nat.shiftLeft_eq, UScalar.size_def, UScalarTy.U64_numBits_eq,
    Nat.mod_eq_of_lt (b54.trans_lt (Nat.pow_lt_pow_right one_lt_two (by omega)))] at hi7
  have P63 : fulcrum.tables.trig.FRAC_PI_2.val ≤ 2 ^ 63 := by
    rw [frac_pi_2_val]; exact Nat.le_of_ble_eq_true rfl
  refine WP.spec_bind (trig_mul_le_spec i7 _ _ _ (hi7 ▸ b54) P63 (Nat.le_of_ble_eq_true rfl))
    fun θ hθ => ?_
  have θ55 : θ.val ≤ 2 ^ 55 :=
    hθ ▸ (mul62_mono _ _ _ _ (hi7 ▸ b54) P63).trans (Nat.le_of_ble_eq_true rfl)
  refine WP.spec_bind (trig_mul_le_spec θ θ _ _ θ55 θ55 (Nat.le_of_ble_eq_true rfl)) fun z hz => ?_
  have z48 : z.val ≤ 2 ^ 48 := hz ▸ (mul62_mono _ _ _ _ θ55 θ55).trans (Nat.le_of_ble_eq_true rfl)
  have zU : z.val ≤ 2 ^ 62 := z48.trans (Nat.pow_le_pow_right two_pos (by omega))
  refine WP.spec_bind (u64_div_spec z 6#u64 6 rfl (by omega)) fun i8 hi8 => ?_
  refine WP.spec_bind (u64_div_spec z 20#u64 20 rfl (by omega)) fun i9 hi9 => ?_
  refine WP.spec_bind trig_one_spec fun one hone => ?_
  have dz : ∀ d, z.val / d ≤ 2 ^ 48 := fun d => (Nat.div_le_self _ _).trans z48
  refine WP.spec_bind (UScalar.sub_spec (x := one) (y := i9) (by rw [hone, hi9]; exact div_le_U _ _ zU))
    fun i11 ⟨hi11, _⟩ => ?_
  rw [hone, hi9] at hi11
  refine WP.spec_bind (trig_mul_le_spec i8 i11 _ _ (hi8 ▸ dz 6) (hi11 ▸ Nat.sub_le _ _)
    (Nat.le_of_ble_eq_true rfl)) fun i12 hi12 => ?_
  have i12U : i12.val ≤ 2 ^ 62 :=
    hi12 ▸ (mul62_le_left _ _ (hi11 ▸ Nat.sub_le _ _)).trans (hi8 ▸ div_le_U _ _ zU)
  refine WP.spec_bind (UScalar.sub_spec (x := one) (y := i12) (by rw [hone]; exact i12U))
    fun i13 ⟨hi13, _⟩ => ?_
  rw [hone] at hi13
  refine WP.spec_bind (trig_mul_le_spec θ i13 _ _ θ55 (hi13 ▸ Nat.sub_le _ _)
    (Nat.le_of_ble_eq_true rfl)) fun sb hsb => ?_
  have sb55 : sb.val ≤ 2 ^ 55 := hsb ▸ (mul62_le_left _ _ (hi13 ▸ Nat.sub_le _ _)).trans θ55
  refine WP.spec_bind (u64_div_spec z 2#u64 2 rfl (by omega)) fun i14 hi14 => ?_
  refine WP.spec_bind (u64_div_spec z 12#u64 12 rfl (by omega)) fun i15 hi15 => ?_
  refine WP.spec_bind (u64_div_spec z 30#u64 30 rfl (by omega)) fun i16 hi16 => ?_
  refine WP.spec_bind (UScalar.sub_spec (x := one) (y := i16) (by rw [hone, hi16]; exact div_le_U _ _ zU))
    fun i17 ⟨hi17, _⟩ => ?_
  rw [hone, hi16] at hi17
  refine WP.spec_bind (trig_mul_le_spec i15 i17 _ _ (hi15 ▸ dz 12) (hi17 ▸ Nat.sub_le _ _)
    (Nat.le_of_ble_eq_true rfl)) fun i18 hi18 => ?_
  have i18U : i18.val ≤ 2 ^ 62 :=
    hi18 ▸ (mul62_le_left _ _ (hi17 ▸ Nat.sub_le _ _)).trans (hi15 ▸ div_le_U _ _ zU)
  refine WP.spec_bind (UScalar.sub_spec (x := one) (y := i18) (by rw [hone]; exact i18U))
    fun i19 ⟨hi19, _⟩ => ?_
  rw [hone] at hi19
  refine WP.spec_bind (trig_mul_le_spec i14 i19 _ _ (hi14 ▸ dz 2) (hi19 ▸ Nat.sub_le _ _)
    (Nat.le_of_ble_eq_true rfl)) fun omc homc => ?_
  have omcU : omc.val ≤ 2 ^ 62 :=
    homc ▸ (mul62_le_left _ _ (hi19 ▸ Nat.sub_le _ _)).trans (hi14 ▸ div_le_U _ _ zU)
  have omc48 : omc.val ≤ 2 ^ 48 :=
    homc ▸ (mul62_le_left _ _ (hi19 ▸ Nat.sub_le _ _)).trans (hi14 ▸ dz 2)
  refine WP.spec_bind (trig_mul_le_spec sv omc _ _ sU omc48 (Nat.le_of_ble_eq_true rfl)) fun i20 hi20 => ?_
  refine WP.spec_bind (UScalar.sub_spec (x := sv) (y := i20) (by rw [hi20]; exact mul62_le_left _ _ omcU))
    fun i21 ⟨hi21, _⟩ => ?_
  refine WP.spec_bind (trig_mul_le_spec cv sb _ _ cU sb55 (Nat.le_of_ble_eq_true rfl)) fun i22 hi22 => ?_
  have i22s : mul62 cv.val sb.val ≤ sb.val := by
    unfold mul62; rw [Nat.mul_comm]; exact mul62_le_left sb.val cv.val cU
  have i22b : i22.val ≤ 2 ^ 55 := hi22 ▸ i22s.trans sb55
  refine WP.spec_mono (UScalar.add_spec (x := i21) (y := i22) (by
    rw [hi21, U64_max_val]
    exact (Nat.add_le_add (Nat.sub_le _ _) i22b).trans ((Nat.add_le_add sU le_rfl).trans
      (Nat.le_of_ble_eq_true rfl)))) fun r hr => ?_
  have rv : r.val = quarterN sv.val cv.val i7.val fulcrum.tables.trig.FRAC_PI_2.val := by
    rw [hr, hi21, hi20, hi22, homc, hsb, hi19, hi18, hi17, hi15, hi14, hi13, hi12, hi11, hi8,
      hz, hθ]
    rfl
  rw [rv]
  rw [← hk] at hs
  have pi0 : 0 ≤ Real.pi / 2 := by positivity
  have k1 : (k.val : ℝ) / 256 ≤ 1 := (div_le_one (by norm_num)).mpr (by exact_mod_cast k256)
  have hs' : |(sv.val : ℝ) - 2 ^ 62 * Real.sin (k.val / 256 * (Real.pi / 2))| ≤ 1 / 2 := by
    rw [mul_comm (2 ^ 62 : ℝ)]; exact hs
  have hc' : |(cv.val : ℝ) - 2 ^ 62 * Real.cos (k.val / 256 * (Real.pi / 2))| ≤ 1 / 2 := by
    rw [Nat.cast_sub (show k.val ≤ 2 ^ 8 from k256), Nat.cast_pow, Nat.cast_ofNat,
      show ((2 : ℝ) ^ 8 - k.val) / 256 * (Real.pi / 2) = Real.pi / 2 - k.val / 256 * (Real.pi / 2) by ring,
      Real.sin_pi_div_two_sub] at hc
    rw [mul_comm (2 ^ 62 : ℝ)]; exact hc
  have hP' : |(fulcrum.tables.trig.FRAC_PI_2.val : ℝ) - 2 ^ 62 * (Real.pi / 2)| ≤ 1 / 2 := by
    rw [mul_comm (2 ^ 62 : ℝ)]; exact frac_pi_2_entry
  have hq := quarter_near sv.val cv.val i7.val _ (k.val / 256 * (Real.pi / 2)) (by positivity)
    (mul_le_of_le_one_left pi0 k1) hs' hc' (hi7 ▸ b54) hP'
  have ang : (k.val : ℝ) / 256 * (Real.pi / 2) + (i7.val : ℝ) * (Real.pi / 2) / 2 ^ 62 =
      p.val / 2 ^ bits.val * (Real.pi / 2) := by
    have pR : (p.val : ℝ) = 2 ^ (bits.val - 8) * k.val + b.val := by
      rw [hk, bv]; exact_mod_cast pk
    have pwR : (2 : ℝ) ^ bits.val = 2 ^ (bits.val - 8) * 256 := by exact_mod_cast pw
    have h62 : (2 : ℝ) ^ 62 = 2 ^ (62 - bits.val) * (2 ^ (bits.val - 8) * 256) := by
      rw [← pwR, ← pow_add]; congr 1; omega
    rw [hi7, pR, pwR, h62]; push_cast; field_simp
  rw [ang] at hq
  rw [mul_comm (Real.sin _)]
  exact hq

end Fulcrum

end
