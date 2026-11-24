module

public import Fulcrum.L4.Turns
public import Fulcrum.L4.Atan

/-!
# L4: `trig::angle_sin`, `angle_cos`, `angle_scale`, `angle_to_radians`, `angle_from_radians` (INTERNALS §3.14)

On the code extracted by Aeneas. An angle of `n` bits is `t / 2^n` of a turn.

- `angle_sin`, `angle_cos`: the quarter of `sin_position` with `n - 2` bits of
  position, within `½ + 6.1 / 2^(62 - f)` of `sin`, `cos (2π · t / 2^n) · 2^f`.
- `((t << (64 - n)) as i64) >> (64 - n)` is `t` read as signed on `n` bits,
  `Int.bmod t (2^n)` (`signed_angle_spec`, `bmod_shift`).
- `angle_scale` is exactly `rnd(s · raw / 2^f) mod 2^n`.
- `angle_to_radians`: `|s| · PI_126` from two words is `⌊|s| · PI_126 / 2^64⌋`,
  within `5/4` of `|s| · π · 2^62` (`pi_product_near`), rounded once:
  within `½ + (5/4) / 2^(61 + n - f)` of `2π · s / 2^n · 2^f`.
- `angle_from_radians`: the quarter turns of `reduce` rounded to `n - 2` bits of
  position, wrapped and negated for `raw < 0`, are within `½ + (5/4) / 2^(130 - n)`
  of `raw / 2^f / 2π · 2^n` modulo `2^n` (`from_radians_near`, `wrap_turns`, `neg_turns`).
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace Fulcrum

set_option maxRecDepth 10000

/-- L4 on the code: `trig::angle_mask(n)` with `n ≤ 64` is `2^n - 1`. -/
theorem angle_mask_spec (n : Std.U32) (hn : n.val ≤ 64) :
    fulcrum.trig.angle_mask n ⦃ m => m.val = 2 ^ n.val - 1 ⦄ := by
  unfold fulcrum.trig.angle_mask
  by_cases h : n = 64#u32
  · have : n.val = 64 := by rw [h]; rfl
    rw [ite_eq_left h, WP.spec_ok, this]; rfl
  · have h' : n.val < 64 := by
      have : n.val ≠ 64 := fun e => h (UScalar.eq_of_val_eq (by rw [e]; rfl))
      omega
    rw [ite_eq_right h]
    refine WP.spec_bind (UScalar.ShiftLeft_spec 1#u64 n _ (by rw [UScalarTy.U64_numBits_eq]; exact h') rfl)
      fun i ⟨hi, _⟩ => ?_
    rw [lit_val, Nat.shiftLeft_eq, one_mul, UScalar.size_def, UScalarTy.U64_numBits_eq,
      Nat.mod_eq_of_lt (Nat.pow_lt_pow_right one_lt_two h')] at hi
    refine WP.spec_mono (UScalar.sub_spec (x := i) (y := 1#u64) (by rw [hi, lit_val]; exact Nat.one_le_two_pow))
      fun r ⟨hr, _⟩ => ?_
    rw [hr, hi, lit_val]

/-- `x &&& (2^n - 1)` keeps `x mod 2^n`. -/
theorem and_mask_val (x m : Std.U64) (n : ℕ) (hm : m.val = 2 ^ n - 1) : (x &&& m).val = x.val % 2 ^ n := by
  rw [UScalar.val_and, hm, Nat.and_two_pow_sub_one_eq_mod]

/-- L4 on the code: `trig::angle_sin` of `t < 2^n`, `2 ≤ n ≤ 64`, `f ≤ 62`, never fails
and is within `½ + 6.1 / 2^(62 - f)` of `sin (2π · t / 2^n) · 2^f`. -/
theorem angle_sin_spec (t : Std.U64) (n f : Std.U32) (hn2 : 2 ≤ n.val) (hn : n.val ≤ 64) (hf : f.val ≤ 62)
    (ht : t.val < 2 ^ n.val) :
    fulcrum.trig.angle_sin t n f ⦃ r =>
      |(r.val : ℝ) - Real.sin (2 * Real.pi * t.val / 2 ^ n.val) * 2 ^ f.val| ≤
        1 / 2 + 61 / 10 / 2 ^ (62 - f.val) ⦄ := by
  unfold fulcrum.trig.angle_sin
  refine WP.spec_bind (UScalar.sub_spec (x := n) (y := 2#u32) (by rw [lit_val]; exact hn2))
    fun i ⟨hi, _⟩ => ?_
  rw [lit_val] at hi
  refine WP.spec_mono (sin_position_spec t i f (by omega) hf (by rw [hi, Nat.sub_add_cancel hn2]; exact ht))
    fun r hr => ?_
  have e : (t.val : ℝ) / 2 ^ i.val * (Real.pi / 2) = 2 * Real.pi * t.val / 2 ^ n.val := by
    have : (2 : ℝ) ^ n.val = 2 ^ i.val * 4 := by
      rw [hi, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_add, Nat.sub_add_cancel hn2]
    rw [this]; field_simp; ring
  rw [e] at hr
  exact hr

/-- L4 on the code: `trig::angle_cos` of any `t`, `2 ≤ n ≤ 64`, `f ≤ 62`, never fails
and is within `½ + 6.1 / 2^(62 - f)` of `cos (2π · t / 2^n) · 2^f`. -/
theorem angle_cos_spec (t : Std.U64) (n f : Std.U32) (hn2 : 2 ≤ n.val) (hn : n.val ≤ 64) (hf : f.val ≤ 62) :
    fulcrum.trig.angle_cos t n f ⦃ r =>
      |(r.val : ℝ) - Real.cos (2 * Real.pi * t.val / 2 ^ n.val) * 2 ^ f.val| ≤
        1 / 2 + 61 / 10 / 2 ^ (62 - f.val) ⦄ := by
  unfold fulcrum.trig.angle_cos
  refine WP.spec_bind (UScalar.sub_spec (x := n) (y := 2#u32) (by rw [lit_val]; exact hn2))
    fun i ⟨hi, _⟩ => ?_
  rw [lit_val] at hi
  refine WP.spec_bind (UScalar.ShiftLeft_spec 1#u64 i _ (by rw [hi, UScalarTy.U64_numBits_eq]; omega) rfl)
    fun i1 ⟨hi1, _⟩ => ?_
  rw [hi, lit_val, Nat.shiftLeft_eq, one_mul, UScalar.size_def, UScalarTy.U64_numBits_eq,
    Nat.mod_eq_of_lt (Nat.pow_lt_pow_right one_lt_two (by omega))] at hi1
  rw [lift, bind_ok]
  refine WP.spec_bind (angle_mask_spec n hn) fun m hm => ?_
  rw [lift, bind_ok]
  have wv : (core.num.U64.wrapping_add t i1 &&& m).val = (t.val + 2 ^ (n.val - 2)) % 2 ^ n.val := by
    rw [and_mask_val _ _ _ hm, show core.num.U64.wrapping_add t i1 = UScalar.wrapping_add t i1 from rfl,
      UScalar.wrapping_add_val_eq, hi1, UScalar.size_def, UScalarTy.U64_numBits_eq,
      Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hn)]
  refine WP.spec_mono (angle_sin_spec _ n f hn2 hn hf (by rw [wv]; exact Nat.mod_lt _ (Nat.two_pow_pos _)))
    fun r hr => ?_
  rw [wv, ← sin_turn_mod] at hr
  have e : 2 * Real.pi * ((t.val + 2 ^ (n.val - 2) : ℕ) : ℝ) / 2 ^ n.val =
      2 * Real.pi * t.val / 2 ^ n.val + Real.pi / 2 := by
    have : (2 : ℝ) ^ n.val = 2 ^ (n.val - 2) * 4 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_add, Nat.sub_add_cancel hn2]
    rw [this]; push_cast; field_simp; ring
  rw [e, Real.sin_add_pi_div_two] at hr
  exact hr

/-- Shifting `a < 2h` up by `K`, reading it as signed on `2h · K` and shifting back
gives `a` as signed on `2h`. -/
theorem bmod_shift (a h K : ℕ) (hK : 0 < K) (ha : a < 2 * h) :
    Int.bmod ((a * K : ℕ) : ℤ) (2 * h * K) / (K : ℤ) = Int.bmod (a : ℤ) (2 * h) := by
  have Kz : (0 : ℤ) < K := by exact_mod_cast hK
  have lt : a * K < 2 * h * K := Nat.mul_lt_mul_of_pos_right ha hK
  rw [Int.bmod_def, Int.bmod_def, Int.emod_eq_of_lt (by positivity) (by exact_mod_cast lt),
    Int.emod_eq_of_lt (by positivity) (by exact_mod_cast ha)]
  have e1 : (((2 * h * K : ℕ) : ℤ) + 1) / 2 = ((h * K : ℕ) : ℤ) := by push_cast; rw [mul_assoc]; omega
  have e2 : (((2 * h : ℕ) : ℤ) + 1) / 2 = (h : ℤ) := by push_cast; omega
  rw [e1, e2]
  by_cases hah : a < h
  · have : a * K < h * K := Nat.mul_lt_mul_of_pos_right hah hK
    rw [ite_eq_left (by exact_mod_cast this), ite_eq_left (by exact_mod_cast hah)]
    push_cast; exact Int.mul_ediv_cancel _ Kz.ne'
  · have : h * K ≤ a * K := Nat.mul_le_mul_right K (not_lt.mp hah)
    rw [ite_eq_right (by exact_mod_cast not_lt.mpr this), ite_eq_right (by exact_mod_cast hah)]
    push_cast
    rw [show (a : ℤ) * K - 2 * h * K = (a - 2 * h) * K by ring]
    exact Int.mul_ediv_cancel _ Kz.ne'

/-- The signed angle of `trig::angle_to_radians` and `angle_scale`:
`((t << (64 - n)) as i64) >> (64 - n)` is `t` read as signed on `n` bits,
`Int.bmod t (2^n) ∈ [-2^(n-1), 2^(n-1))`, for `1 ≤ n ≤ 64`; stated for any
continuation `k`. -/
theorem signed_angle_spec {α} (t : Std.U64) (n : Std.U32) (hn1 : 1 ≤ n.val) (hn : n.val ≤ 64)
    (k : Std.I64 → Result α) (P : α → Prop)
    (hk : ∀ s : Std.I64, s.val = Int.bmod (t.val : ℤ) (2 ^ n.val) → k s ⦃ P ⦄) :
    (do
      let i ← 64#u32 - n
      let i1 ← t <<< i
      let i2 ← lift (UScalar.hcast .I64 i1)
      let s ← i2 >>> i
      k s) ⦃ P ⦄ := by
  refine WP.spec_bind (UScalar.sub_spec (x := 64#u32) (y := n) (by rw [lit_val]; exact hn)) fun i ⟨hi, _⟩ => ?_
  rw [lit_val] at hi
  refine WP.spec_bind (UScalar.ShiftLeft_spec t i _ (by rw [hi, UScalarTy.U64_numBits_eq]; omega) rfl)
    fun i1 ⟨h1, _⟩ => ?_
  rw [lift, bind_ok]
  refine WP.spec_bind (IScalar.ShiftRight_spec _ i (by rw [hi, IScalarTy.I64_numBits_eq]; omega)) fun s ⟨hs, _⟩ => ?_
  refine hk s ?_
  have p64 : (2 : ℕ) ^ 64 = 2 * 2 ^ (n.val - 1) * 2 ^ (64 - n.val) := by
    rw [mul_comm 2, ← pow_succ, ← pow_add]; congr 1; omega
  have hpow : (2 : ℕ) ^ n.val = 2 * 2 ^ (n.val - 1) := by
    rw [mul_comm, ← pow_succ]; congr 1; omega
  rw [hs, UScalar.hcast_val_eq, h1, hi, Nat.shiftLeft_eq, UScalar.size_def, UScalarTy.U64_numBits_eq,
    IScalarTy.I64_numBits_eq, shr_eq_div, p64, Nat.mul_mod_mul_right, ← hpow]
  have b := bmod_shift (t.val % 2 ^ n.val) (2 ^ (n.val - 1)) (2 ^ (64 - n.val)) (Nat.two_pow_pos _)
    (hpow ▸ Nat.mod_lt _ (Nat.two_pow_pos _))
  rw [← hpow] at b
  push_cast at b ⊢
  rw [b, Int.bmod_def, Int.bmod_def]
  push_cast
  rw [Int.emod_emod_of_dvd _ (dvd_refl _)]

/-- An `i64` widened to `i128` keeps its value. -/
theorem cast_i128_val (x : Std.I64) : (IScalar.cast .I128 x).val = x.val := by
  rw [IScalar.cast_val_eq, IScalarTy.I128_numBits_eq, IScalarTy.I64_numBits_eq]
  have ⟨l, u⟩ := val_bounds x IScalarTy.I64_numBits_eq
  exact Int.bmod_eq_of_le (by push_cast; norm_num at l ⊢; omega) (by push_cast; norm_num at u ⊢; omega)

/-- L4 on the code: `trig::angle_scale(t, n, raw, f)` with `1 ≤ n ≤ 64` never fails
and is `rnd(s · raw / 2^f) mod 2^n`, `s` the angle `t` read as signed on `n` bits:
exact, one rounding, ties up. -/
theorem angle_scale_spec (t : Std.U64) (n : Std.U32) (raw : Std.I64) (f : Std.U32) (hn1 : 1 ≤ n.val)
    (hn : n.val ≤ 64) :
    fulcrum.trig.angle_scale t n raw f ⦃ r =>
      (r.val : ℤ) = roundHalfUp (exact f.val (Int.bmod (t.val : ℤ) (2 ^ n.val) * raw.val)) % 2 ^ n.val ⦄ := by
  unfold fulcrum.trig.angle_scale
  refine signed_angle_spec t n hn1 hn _ _ fun s hs => ?_
  rw [lift, bind_ok, lift, bind_ok]
  have ⟨sl, su⟩ := val_bounds s IScalarTy.I64_numBits_eq
  have ⟨rl, ru⟩ := val_bounds raw IScalarTy.I64_numBits_eq
  have pb : |s.val * raw.val| ≤ 2 ^ 126 := by
    rw [abs_mul, show (2 : ℤ) ^ 126 = 2 ^ 63 * 2 ^ 63 by norm_num]
    exact mul_le_mul (abs_le.mpr ⟨sl, su.le⟩) (abs_le.mpr ⟨rl, ru.le⟩) (abs_nonneg _) (by positivity)
  have ⟨pl, pu⟩ := abs_le.mp pb
  have ib := in_bounds_of_pow IScalarTy.I128_numBits_eq (m := 127) (x := s.val * raw.val)
    (le_trans (by norm_num) pl) (lt_of_le_of_lt pu (by norm_num))
  refine WP.spec_bind (IScalar.mul_spec (x := IScalar.cast .I128 s) (y := IScalar.cast .I128 raw)
    (by rw [cast_i128_val, cast_i128_val]; exact ib.1) (by rw [cast_i128_val, cast_i128_val]; exact ib.2))
    fun i5 h5 => ?_
  rw [cast_i128_val, cast_i128_val] at h5
  refine WP.spec_bind (shr_round_spec i5 f) fun r hr => ?_
  rw [lift, bind_ok]
  refine WP.spec_bind (angle_mask_spec n hn) fun m hm => ?_
  rw [WP.spec_ok, and_mask_val _ _ _ hm, IScalar.hcast_val_eq, UScalarTy.U64_numBits_eq, hr, h5, hs]
  have d : ((2 : ℤ) ^ n.val) ∣ 2 ^ 64 := pow_dvd_pow 2 hn
  generalize roundHalfUp (exact f.val (Int.bmod (t.val : ℤ) (2 ^ n.val) * raw.val)) = x
  have nn : 0 ≤ x % 2 ^ 64 := Int.emod_nonneg _ (by positivity)
  rw [Int.natCast_mod, Int.toNat_of_nonneg nn, Nat.cast_pow, Nat.cast_ofNat, Int.emod_emod_of_dvd _ d]

/-- An integer read as signed on `n ≥ 1` bits has magnitude at most `2^(n-1)`. -/
theorem bmod_natAbs_le (x : ℤ) (n : ℕ) (hn : 1 ≤ n) : (Int.bmod x (2 ^ n)).natAbs ≤ 2 ^ (n - 1) := by
  have p : (2 : ℕ) ^ n = 2 * 2 ^ (n - 1) := by rw [mul_comm, ← pow_succ]; congr 1; omega
  have l := Int.le_bmod (x := x) (m := 2 ^ n) (Nat.two_pow_pos _)
  have u := Int.bmod_lt (x := x) (m := 2 ^ n) (Nat.two_pow_pos _)
  generalize Int.bmod x (2 ^ n) = b at l u ⊢
  rw [p] at l u
  generalize 2 ^ (n - 1) = q at l u ⊢
  push_cast at l u
  omega

/-- `m · rnd(π · 2^126) / 2^64`, floored, is within `5/4` of `m · π · 2^62` for `m ≤ 2^63`. -/
theorem pi_product_near (m P : ℕ) (hm : m ≤ 2 ^ 63) (hP : |(P : ℝ) - Real.pi * 2 ^ 126| ≤ 1 / 2) :
    |((m * P / 2 ^ 64 : ℕ) : ℝ) - m * Real.pi * 2 ^ 62| ≤ 5 / 4 := by
  have ⟨l, u⟩ := floor_div_near (m * P) (2 ^ 64) (by positivity)
  push_cast at l u
  have mR : (m : ℝ) ≤ 2 ^ 63 := by exact_mod_cast hm
  have d : |(m : ℝ) * P / 2 ^ 64 - m * Real.pi * 2 ^ 62| ≤ 1 / 4 := by
    rw [show (m : ℝ) * P / 2 ^ 64 - m * Real.pi * 2 ^ 62 = m * (P - Real.pi * 2 ^ 126) / 2 ^ 64 by ring,
      abs_div, abs_mul, Nat.abs_cast, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 64), div_le_iff₀ (by positivity)]
    calc (m : ℝ) * |(P : ℝ) - Real.pi * 2 ^ 126| ≤ 2 ^ 63 * (1 / 2) :=
          mul_le_mul mR hP (abs_nonneg _) (by positivity)
      _ = 1 / 4 * 2 ^ 64 := by norm_num
  have ⟨dl, du⟩ := abs_le.mp d
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Rounding `h / 2^k` once, for `h` within `E` of `S · 2^k`, is within `½ + E / 2^k` of `S`. -/
theorem round_div_near (h : ℤ) (k : ℕ) (S E : ℝ) (hh : |(h : ℝ) - S * 2 ^ k| ≤ E) :
    |((roundHalfUp (exact k h) : ℤ) : ℝ) - S| ≤ 1 / 2 + E / 2 ^ k := by
  have r := roundHalfUp_near (exact k h)
  have r' : |((roundHalfUp (exact k h) : ℤ) : ℝ) - (h : ℝ) / 2 ^ k| ≤ 1 / 2 := by
    have := (Rat.cast_le (K := ℝ)).mpr r
    push_cast [exact] at this
    exact this
  have p : (0 : ℝ) < 2 ^ k := by positivity
  have e : (h : ℝ) / 2 ^ k - S = ((h : ℝ) - S * 2 ^ k) / 2 ^ k := by field_simp
  calc _ ≤ |((roundHalfUp (exact k h) : ℤ) : ℝ) - (h : ℝ) / 2 ^ k| + |(h : ℝ) / 2 ^ k - S| := abs_sub_le _ _ _
    _ ≤ 1 / 2 + E / 2 ^ k := by
        refine add_le_add r' ?_
        rw [e, abs_div, abs_of_pos p]
        exact div_le_div_of_nonneg_right hh p.le

/-- The value of `tables::trig::PI_126`. -/
theorem pi_126_lt : fulcrum.tables.trig.PI_126.val < 2 ^ 128 := fulcrum.tables.trig.PI_126.bv.isLt

/-- L4 on the code: `trig::angle_to_radians(t, n, f)` with `1 ≤ n ≤ 64`, `f ≤ 32` never
fails and is within `½ + (5/4) / 2^(61 + n - f)` of `2π · s / 2^n · 2^f`, `s` the angle
`t` read as signed on `n` bits, in `[-2^(n-1), 2^(n-1))`. -/
theorem angle_to_radians_spec (t : Std.U64) (n f : Std.U32) (hn1 : 1 ≤ n.val) (hn : n.val ≤ 64)
    (hf : f.val ≤ 32) :
    fulcrum.trig.angle_to_radians t n f ⦃ r =>
      |(r.val : ℝ) - 2 * Real.pi * (Int.bmod (t.val : ℤ) (2 ^ n.val) : ℝ) / 2 ^ n.val * 2 ^ f.val| ≤
        1 / 2 + 5 / 4 / 2 ^ (61 + n.val - f.val) ⦄ := by
  have n128 : UScalarTy.U128.numBits = 128 := rfl
  have u128 : UScalar.max .U128 = 2 ^ 128 - 1 := U128_max_val
  unfold fulcrum.trig.angle_to_radians
  refine signed_angle_spec t n hn1 hn _ _ fun s hs => ?_
  refine WP.spec_bind (I64_unsigned_abs_spec s) fun i3 h3 => ?_
  rw [lift, bind_ok]
  have mv : (UScalar.cast .U128 i3).val = s.val.natAbs := by rw [cast_u128_val, h3]
  have ml : s.val.natAbs ≤ 2 ^ (n.val - 1) := hs ▸ bmod_natAbs_le _ _ hn1
  have m63 : s.val.natAbs ≤ 2 ^ 63 := ml.trans (Nat.pow_le_pow_right two_pos (by omega))
  generalize UScalar.cast .U128 i3 = m at mv ⊢
  set P := fulcrum.tables.trig.PI_126.val with hP
  have Pl : P < 2 ^ 128 := pi_126_lt
  refine WP.spec_bind (shr_i32_spec fulcrum.tables.trig.PI_126 64#i32 64 rfl (by rw [n128]; norm_num))
    fun i4 h4 => ?_
  have i4l : i4.val < 2 ^ 64 := by rw [h4, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]; exact Pl.trans_eq (by norm_num)
  refine WP.spec_bind (UScalar.mul_spec (x := m) (y := i4) (by
    rw [u128, mv]; exact (Nat.mul_le_mul m63 i4l.le).trans (by norm_num))) fun i5 h5 => ?_
  rw [lift, bind_ok, lift, bind_ok]
  have c7 : (UScalar.cast .U128 (UScalar.cast .U64 fulcrum.tables.trig.PI_126)).val = P % 2 ^ 64 := by
    rw [cast_u128_val, cast_u64_val]
  refine WP.spec_bind (UScalar.mul_spec (x := m) (y := UScalar.cast .U128 (UScalar.cast .U64 fulcrum.tables.trig.PI_126))
    (by rw [u128, mv, c7]; exact (Nat.mul_le_mul m63 (Nat.mod_lt _ (Nat.two_pow_pos 64)).le).trans (by norm_num)))
    fun i8 h8 => ?_
  rw [c7] at h8
  refine WP.spec_bind (shr_i32_spec i8 64#i32 64 rfl (by rw [n128]; norm_num)) fun i9 h9 => ?_
  have hv : i5.val + i9.val = s.val.natAbs * P / 2 ^ 64 := by
    rw [h5, h9, h8, h4, mv]
    conv_rhs => rw [← Nat.div_add_mod P (2 ^ 64)]
    rw [Nat.mul_add, ← mul_assoc, mul_comm _ (2 ^ 64), mul_assoc, Nat.mul_add_div (Nat.two_pow_pos 64), mul_comm]
  have hl : s.val.natAbs * P / 2 ^ 64 < 2 ^ 127 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    calc s.val.natAbs * P < 2 ^ 63 * 2 ^ 128 := Nat.mul_lt_mul_of_le_of_lt m63 Pl (by positivity)
      _ = 2 ^ 127 * 2 ^ 64 := by norm_num
  refine WP.spec_bind (UScalar.add_spec (x := i5) (y := i9) (by rw [u128, hv]; omega)) fun high hh => ?_
  rw [hv] at hh
  refine WP.spec_bind (UScalar.add_spec (x := 125#u32) (y := n) (by rw [lit_val, U32_max_val]; omega))
    fun i10 h10 => ?_
  rw [lit_val] at h10
  refine WP.spec_bind (UScalar.sub_spec (x := i10) (y := f) (by rw [h10]; omega)) fun i11 ⟨h11, _⟩ => ?_
  refine WP.spec_bind (UScalar.sub_spec (x := i11) (y := 64#u32) (by rw [h11, h10, lit_val]; omega))
    fun k ⟨hk, _⟩ => ?_
  rw [h11, h10, lit_val] at hk
  rw [lift, bind_ok]
  have hc : (UScalar.hcast .I128 high).val = (high.val : ℤ) := by
    rw [UScalar.hcast_val_eq, IScalarTy.I128_numBits_eq]
    exact Int.bmod_eq_of_le ((neg_nonpos.mpr (by positivity)).trans (Int.natCast_nonneg _))
      ((by exact_mod_cast (hh ▸ hl) : (high.val : ℤ) < 2 ^ 127).trans_le (by norm_num))
  refine WP.spec_bind (shr_round_spec _ k) fun i13 h13 => ?_
  rw [hc, hk] at h13
  have kv : 125 + n.val - f.val - 64 = 61 + n.val - f.val := by omega
  rw [kv] at h13
  set S : ℝ := (s.val.natAbs : ℝ) * Real.pi * 2 ^ (1 + f.val) / 2 ^ n.val with hS
  have near := round_div_near (high.val : ℤ) (61 + n.val - f.val) S (5 / 4) (by
    push_cast
    rw [hh]
    have e : S * 2 ^ (61 + n.val - f.val) = s.val.natAbs * Real.pi * 2 ^ 62 := by
      have : (2 : ℝ) ^ (1 + f.val) * 2 ^ (61 + n.val - f.val) = 2 ^ n.val * 2 ^ 62 := by
        rw [← pow_add, ← pow_add]; congr 1; omega
      rw [hS, div_mul_eq_mul_div, mul_assoc, this]; field_simp
    rw [e]
    exact pi_product_near _ P m63 pi_126_entry)
  rw [← h13] at near
  have Sb : S ≤ 2 ^ 34 := by
    have m1 : (s.val.natAbs : ℝ) ≤ 2 ^ (n.val - 1) := by exact_mod_cast ml
    have e : (2 : ℝ) ^ (n.val - 1) * 2 ^ (1 + f.val) / 2 ^ n.val = 2 ^ f.val := by
      have : (2 : ℝ) ^ (n.val - 1) * 2 ^ (1 + f.val) = 2 ^ f.val * 2 ^ n.val := by
        rw [← pow_add, ← pow_add]; congr 1; omega
      rw [this]; field_simp
    have pf : (2 : ℝ) ^ f.val ≤ 2 ^ 32 := pow_le_pow_right₀ one_le_two hf
    calc S ≤ 2 ^ (n.val - 1) * 4 * 2 ^ (1 + f.val) / 2 ^ n.val := by
          rw [hS]
          refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by positivity)) (by positivity)
          exact mul_le_mul m1 (by linarith [Real.pi_lt_d2]) Real.pi_pos.le (by positivity)
      _ = 4 * 2 ^ f.val := by rw [mul_comm _ (4 : ℝ), mul_assoc, mul_div_assoc, e]
      _ ≤ 2 ^ 34 := by nlinarith
  have S0 : 0 ≤ S := by positivity
  have err : 1 / 2 + 5 / 4 / 2 ^ (61 + n.val - f.val) ≤ (1 : ℝ) := by
    have : (5 / 4 : ℝ) / 2 ^ (61 + n.val - f.val) ≤ 5 / 4 / 2 ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (pow_le_pow_right₀ one_le_two (by omega))
    linarith
  have ib : -(2 ^ 35) ≤ i13.val ∧ i13.val ≤ 2 ^ 35 := by
    have ⟨l, u⟩ := abs_le.mp (near.trans err)
    constructor
    · have : -(2 : ℝ) ^ 35 ≤ i13.val := by linarith
      exact_mod_cast this
    · have : (i13.val : ℝ) ≤ 2 ^ 35 := by linarith
      exact_mod_cast this
  have inr : InRange 63 i13.val :=
    ⟨(by unfold minOf; norm_num : minOf 63 ≤ -(2 ^ 35)).trans ib.1, ib.2.trans (by unfold maxOf; norm_num)⟩
  have cv : (IScalar.cast .I64 i13).val = i13.val :=
    (IScalar.cast_val_eq .I64 i13).trans ((wrap_eq_self_iff 63 _).2 inr)
  rw [lift, bind_ok]
  have target : 2 * Real.pi * (Int.bmod (t.val : ℤ) (2 ^ n.val) : ℝ) / 2 ^ n.val * 2 ^ f.val =
      (if s.val < 0 then -S else S) := by
    rw [← hs, hS, natAbs_real]
    split_ifs <;> rw [pow_add] <;> ring
  rw [target]
  by_cases hn' : s < 0#i64
  · have hv : s.val < 0 := hn'
    rw [ite_eq_left hn', ite_eq_left hv]
    refine WP.spec_mono (IScalar.neg_step _ (fun e => ?_)) fun r hr => ?_
    · rw [cv, IScalar.min_def, IScalarTy.I64_numBits_eq] at e
      have := ib.1; omega
    · rw [hr, cv]; push_cast
      rw [show -(i13.val : ℝ) - -S = -((i13.val : ℝ) - S) by ring, abs_neg]
      exact near
  · have hv : ¬ s.val < 0 := hn'
    rw [ite_eq_right hn', ite_eq_right hv, WP.spec_ok, cv]
    exact near

/-- `angle_from_radians` on naturals, before the wrap to `n` bits: the quarter
`q` of the quarter turns `N = ⌊m · C / 2^(f + 64)⌋` shifted to the top two of `n`
bits, plus the 128 bits of the fraction rounded to `n - 2`, are `m / 2^f / 2π`
turns in units of `2^-n`, within `½ + (5/4) / 2^(130 - n)`, minus whole turns. -/
theorem from_radians_near (m f n : ℕ) (hm : m ≤ 2 ^ 63) (hn2 : 2 ≤ n) (hn : n ≤ 64) :
    ∃ K : ℤ, |((m * frac2PiN / 2 ^ (f + 64) / 2 ^ 128 % 4 * 2 ^ (n - 2) +
        (m * frac2PiN / 2 ^ (f + 64) % 2 ^ 128 + 2 ^ (129 - n)) / 2 ^ (130 - n) : ℕ) : ℝ) -
        (m / 2 ^ f / (2 * Real.pi) * 2 ^ n + K * 2 ^ n)| ≤ 1 / 2 + 5 / 4 / 2 ^ (130 - n) := by
  have hC : |(frac2PiN : ℝ) - 2 / Real.pi * 2 ^ 192| ≤ 1 / 2 := frac_2_pi_entry
  set N := m * frac2PiN / 2 ^ (f + 64) with hN
  have eG : N % 2 ^ 130 = N / 2 ^ 128 % 4 * 2 ^ 128 + N % 2 ^ 128 := by
    rw [show (2 : ℕ) ^ 130 = 2 ^ 128 * 4 by norm_num, Nat.mod_mul, add_comm, mul_comm]
  have eN := Nat.mod_add_div N (2 ^ 130)
  refine ⟨-((N / 2 ^ 130 : ℕ) : ℤ), ?_⟩
  set fr := N % 2 ^ 128
  set q := N / 2 ^ 128 % 4
  have ⟨l, u⟩ := floor_div_near (fr + 2 ^ (129 - n)) (2 ^ (130 - n)) (by positivity)
  have ⟨nl, nu⟩ := floor_div_near (m * frac2PiN) (2 ^ (f + 64)) (by positivity)
  rw [← hN] at nl nu
  push_cast at l u nl nu
  rw [Int.cast_neg, Int.cast_natCast, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have half : (2 : ℝ) ^ (129 - n) / 2 ^ (130 - n) = 1 / 2 := by
    rw [show 130 - n = 129 - n + 1 by omega, pow_succ]; field_simp
  rw [add_div, half] at l u
  have eG' : ((N % 2 ^ 130 : ℕ) : ℝ) = q * 2 ^ 128 + fr := by rw [eG]; push_cast; ring
  have eN' : ((N % 2 ^ 130 : ℕ) : ℝ) + 2 ^ 130 * ((N / 2 ^ 130 : ℕ) : ℝ) = N := by exact_mod_cast eN
  have mR : (m : ℝ) ≤ 2 ^ 63 := by exact_mod_cast hm
  have d : |(m : ℝ) * frac2PiN / 2 ^ (f + 64) - m / 2 ^ f * (2 / Real.pi) * 2 ^ 128| ≤ 1 / 4 := by
    rw [show (m : ℝ) * frac2PiN / 2 ^ (f + 64) - m / 2 ^ f * (2 / Real.pi) * 2 ^ 128 =
        m * (frac2PiN - 2 / Real.pi * 2 ^ 192) / 2 ^ (f + 64) by
          have hF : (2 : ℝ) ^ f ≠ 0 := by positivity
          have hB : (2 : ℝ) ^ 64 ≠ 0 := by positivity
          have pi0 := Real.pi_pos.ne'
          rw [pow_add, show (2 : ℝ) ^ 192 = 2 ^ 128 * 2 ^ 64 by norm_num]
          generalize (2 : ℝ) ^ 128 = A
          generalize (2 : ℝ) ^ 64 = B at hB ⊢
          generalize (2 : ℝ) ^ f = Fp at hF ⊢
          generalize (frac2PiN : ℝ) = Cc
          generalize (m : ℝ) = M
          field_simp,
      abs_div, abs_mul, Nat.abs_cast, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (f + 64)), div_le_iff₀ (by positivity)]
    calc (m : ℝ) * |(frac2PiN : ℝ) - 2 / Real.pi * 2 ^ 192| ≤ 2 ^ 63 * (1 / 2) :=
          mul_le_mul mR hC (abs_nonneg _) (by positivity)
      _ = 1 / 4 * 2 ^ 64 := by norm_num
      _ ≤ 1 / 4 * 2 ^ (f + 64) := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ one_le_two (by omega)) (by norm_num)
  have ⟨dl, du⟩ := abs_le.mp d
  set A := ((N / 2 ^ 130 : ℕ) : ℝ)
  set P := ((fr + 2 ^ (129 - n)) / 2 ^ (130 - n) : ℕ)
  have key : (q : ℝ) * 2 ^ (n - 2) + P - (m / 2 ^ f / (2 * Real.pi) * 2 ^ n + -A * 2 ^ n) =
      (P - (fr / 2 ^ (130 - n) + 1 / 2) + 1 / 2) +
        ((N : ℝ) - m / 2 ^ f * (2 / Real.pi) * 2 ^ 128) / 2 ^ (130 - n) := by
    have e1 : (q : ℝ) * 2 ^ (n - 2) = q * 2 ^ 128 / 2 ^ (130 - n) := by
      have : (2 : ℝ) ^ (n - 2) * 2 ^ (130 - n) = 2 ^ 128 := by rw [← pow_add]; congr 1; omega
      rw [eq_div_iff (by positivity), mul_assoc, this]
    have e2 : -A * 2 ^ n = -(2 ^ 130 * A) / 2 ^ (130 - n) := by
      have : (2 : ℝ) ^ n * 2 ^ (130 - n) = 2 ^ 130 := by rw [← pow_add]; congr 1; omega
      rw [eq_div_iff (by positivity), mul_assoc, this]; ring
    have e3 : (m : ℝ) / 2 ^ f / (2 * Real.pi) * 2 ^ n = m / 2 ^ f * (2 / Real.pi) * 2 ^ 128 / 2 ^ (130 - n) := by
      have : (2 : ℝ) ^ n * 2 ^ (130 - n) = 2 ^ 128 * 4 := by
        rw [← pow_add, show (2 : ℝ) ^ 128 * 4 = 2 ^ 130 by norm_num]; congr 1; omega
      rw [eq_div_iff (by positivity), mul_assoc, this]
      generalize (m : ℝ) / 2 ^ f = M
      generalize (2 : ℝ) ^ 128 = W
      have pi0 := Real.pi_pos.ne'
      field_simp; ring
    rw [e1, e2, e3, ← eN', eG']; ring
  rw [key]
  have b1 : |(P : ℝ) - (fr / 2 ^ (130 - n) + 1 / 2) + 1 / 2| ≤ 1 / 2 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have b2 : |((N : ℝ) - m / 2 ^ f * (2 / Real.pi) * 2 ^ 128) / 2 ^ (130 - n)| ≤ 5 / 4 / 2 ^ (130 - n) := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (130 - n))]
    exact div_le_div_of_nonneg_right (abs_le.mpr ⟨by linarith, by linarith⟩) (by positivity)
  exact (abs_add_le _ _).trans (add_le_add b1 b2)

/-- Wrapping `v` to `n` bits keeps it within `E` of `X` modulo whole turns. -/
theorem wrap_turns (v n : ℕ) (X E : ℝ) (h : ∃ K : ℤ, |(v : ℝ) - (X + K * 2 ^ n)| ≤ E) :
    ∃ K : ℤ, |((v % 2 ^ n : ℕ) : ℝ) - (X + K * 2 ^ n)| ≤ E := by
  obtain ⟨K, hK⟩ := h
  refine ⟨K - ((v / 2 ^ n : ℕ) : ℤ), ?_⟩
  have e : ((v % 2 ^ n : ℕ) : ℝ) = v - 2 ^ n * ((v / 2 ^ n : ℕ) : ℝ) := by
    have := Nat.mod_add_div v (2 ^ n)
    have : ((v % 2 ^ n : ℕ) : ℝ) + 2 ^ n * ((v / 2 ^ n : ℕ) : ℝ) = v := by exact_mod_cast this
    linarith
  rw [e, Int.cast_sub, Int.cast_natCast]
  rw [show (v : ℝ) - 2 ^ n * ((v / 2 ^ n : ℕ) : ℝ) - (X + (K - ((v / 2 ^ n : ℕ) : ℝ)) * 2 ^ n) =
    (v : ℝ) - (X + K * 2 ^ n) by ring]
  exact hK

/-- The negation `(2^64 - t) mod 2^n` of an angle `t < 2^n ≤ 2^64` is within `E` of `-X`
modulo whole turns when `t` is within `E` of `X`. -/
theorem neg_turns (t n : ℕ) (hn : n ≤ 64) (ht : t < 2 ^ n) (X E : ℝ)
    (h : ∃ K : ℤ, |(t : ℝ) - (X + K * 2 ^ n)| ≤ E) :
    ∃ K : ℤ, |(((2 ^ 64 - t) % 2 ^ n : ℕ) : ℝ) - (-X + K * 2 ^ n)| ≤ E := by
  refine wrap_turns _ n _ E ?_
  obtain ⟨K, hK⟩ := h
  have tl : t ≤ 2 ^ 64 := ht.le.trans (Nat.pow_le_pow_right two_pos hn)
  refine ⟨2 ^ (64 - n) - K, ?_⟩
  have p : (2 : ℝ) ^ 64 = 2 ^ (64 - n) * 2 ^ n := by rw [← pow_add, Nat.sub_add_cancel hn]
  rw [Nat.cast_sub tl, Nat.cast_pow, Nat.cast_ofNat, p, Int.cast_sub, Int.cast_pow, Int.cast_ofNat]
  rw [show (2 : ℝ) ^ (64 - n) * 2 ^ n - t - (-X + (2 ^ (64 - n) - K) * 2 ^ n) = -((t : ℝ) - (X + K * 2 ^ n)) by ring,
    abs_neg]
  exact hK

/-- `u64::wrapping_neg` is `(2^64 - x) mod 2^64`. -/
theorem u64_wrapping_neg_spec (x : Std.U64) :
    core.num.U64.wrapping_neg x ⦃ y => y.val = (2 ^ 64 - x.val) % 2 ^ 64 ⦄ := by
  unfold core.num.U64.wrapping_neg
  rw [WP.spec_ok]
  show (-x.bv).toNat = _
  rw [BitVec.toNat_neg]; rfl

/-- Halving `⌊x / 2^a⌋` with the dropped bit added rounds `x / 2^(a+1)`. -/
theorem half_round (x a : ℕ) : (x / 2 ^ a + 1) / 2 = (x + 2 ^ a) / 2 ^ (a + 1) := by
  rw [← Nat.add_div_right x (Nat.two_pow_pos a), Nat.div_div_eq_div_mul, pow_succ]

/-- L4 on the code: `trig::angle_from_radians(raw, f, n)` with `f ≤ 62`, `2 ≤ n ≤ 64`
never fails and returns `t < 2^n` within `½ + (5/4) / 2^(130 - n)` of
`raw / 2^f / 2π · 2^n` modulo `2^n`: `x / 2π mod 1` in units of `2^-n` turn. -/
theorem angle_from_radians_spec (raw : Std.I64) (f n : Std.U32) (hf : f.val ≤ 62) (hn2 : 2 ≤ n.val)
    (hn : n.val ≤ 64) :
    fulcrum.trig.angle_from_radians raw f n ⦃ t => t.val < 2 ^ n.val ∧
      ∃ K : ℤ, |(t.val : ℝ) - ((raw.val : ℝ) / 2 ^ f.val / (2 * Real.pi) * 2 ^ n.val + K * 2 ^ n.val)| ≤
        1 / 2 + 5 / 4 / 2 ^ (130 - n.val) ⦄ := by
  have n128 : UScalarTy.U128.numBits = 128 := rfl
  unfold fulcrum.trig.angle_from_radians
  refine WP.spec_bind (I64_unsigned_abs_spec raw) fun m hm => ?_
  have m63 : m.val ≤ 2 ^ 63 := hm ▸ natAbs_le_pow raw 63 IScalarTy.I64_numBits_eq
  refine WP.spec_bind (reduce_spec m f hf) fun r ⟨hq, hfr⟩ => ?_
  obtain ⟨q, fr⟩ := r
  dsimp only at hq hfr ⊢
  refine WP.spec_bind (UScalar.sub_spec (x := 129#u32) (y := n) (by rw [lit_val]; omega)) fun i1 ⟨h1, _⟩ => ?_
  rw [lit_val] at h1
  refine WP.spec_bind (UScalar.ShiftRight_spec fr i1 (by rw [h1, n128]; omega)) fun i2 ⟨h2, _⟩ => ?_
  rw [h1, Nat.shiftRight_eq_div_pow] at h2
  have i2l : i2.val < 2 ^ 63 := by
    rw [h2, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add]
    exact fr.bv.isLt.trans_le (Nat.pow_le_pow_right two_pos (by omega))
  rw [lift, bind_ok]
  have hc : (UScalar.hcast .I128 i2).val = (i2.val : ℤ) := by
    rw [UScalar.hcast_val_eq, IScalarTy.I128_numBits_eq]
    exact Int.bmod_eq_of_le ((neg_nonpos.mpr (by positivity)).trans (Int.natCast_nonneg _))
      ((by exact_mod_cast i2l : (i2.val : ℤ) < 2 ^ 63).trans_le (by norm_num))
  refine WP.spec_bind (shr_round_spec _ 1#u32) fun i4 h4 => ?_
  rw [hc, lit_val, ← zero_add 1, ← add_half_shr, shr_eq_div, pow_zero, zero_add, pow_one] at h4
  rw [lift, bind_ok]
  have pv : (IScalar.hcast .U64 i4).val = (fr.val + 2 ^ (129 - n.val)) / 2 ^ (130 - n.val) := by
    rw [IScalar.hcast_val_eq, h4, UScalarTy.U64_numBits_eq, h2,
      show 130 - n.val = 129 - n.val + 1 by omega, ← half_round]
    have : (fr.val / 2 ^ (129 - n.val) + 1) / 2 < 2 ^ 64 := by omega
    omega
  generalize IScalar.hcast .U64 i4 = pos at pv ⊢
  refine WP.spec_bind (UScalar.sub_spec (x := n) (y := 2#u32) (by rw [lit_val]; exact hn2)) fun i5 ⟨h5, _⟩ => ?_
  rw [lit_val] at h5
  refine WP.spec_bind (UScalar.ShiftLeft_spec q i5 _ (by rw [h5, UScalarTy.U64_numBits_eq]; omega) rfl)
    fun i6 ⟨h6, _⟩ => ?_
  rw [h5, Nat.shiftLeft_eq, UScalar.size_def, UScalarTy.U64_numBits_eq] at h6
  rw [lift, bind_ok]
  refine WP.spec_bind (angle_mask_spec n hn) fun msk hmsk => ?_
  rw [lift, bind_ok]
  have dv : 2 ^ n.val ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 hn
  set v := q.val * 2 ^ (n.val - 2) + pos.val with hv
  have tv : (core.num.U64.wrapping_add i6 pos &&& msk).val = v % 2 ^ n.val := by
    rw [and_mask_val _ _ _ hmsk, show core.num.U64.wrapping_add i6 pos = UScalar.wrapping_add i6 pos from rfl,
      UScalar.wrapping_add_val_eq, h6, UScalar.size_def, UScalarTy.U64_numBits_eq, Nat.mod_add_mod,
      Nat.mod_mod_of_dvd _ dv]
  generalize core.num.U64.wrapping_add i6 pos &&& msk = t at tv ⊢
  have near := from_radians_near m.val f.val n.val m63 hn2 hn
  rw [← hq, ← hfr, ← pv] at near
  have wt := wrap_turns v n.val _ _ near
  rw [← tv] at wt
  have tl : t.val < 2 ^ n.val := tv ▸ Nat.mod_lt _ (Nat.two_pow_pos _)
  have mr := natAbs_real raw.val
  rw [← hm] at mr
  by_cases hneg : raw < 0#i64
  · have hneg' : raw.val < 0 := hneg
    rw [ite_eq_left hneg]
    refine WP.spec_bind (u64_wrapping_neg_spec t) fun i9 h9 => ?_
    rw [WP.spec_ok, and_mask_val _ _ _ hmsk, h9, Nat.mod_mod_of_dvd _ dv]
    refine ⟨Nat.mod_lt _ (Nat.two_pow_pos _), ?_⟩
    have := neg_turns t.val n.val hn tl _ _ wt
    rw [ite_eq_left hneg'] at mr
    have e : (raw.val : ℝ) / 2 ^ f.val / (2 * Real.pi) * 2 ^ n.val =
        -((m.val : ℝ) / 2 ^ f.val / (2 * Real.pi) * 2 ^ n.val) := by rw [mr]; ring
    rw [e]; exact this
  · have hneg' : ¬ raw.val < 0 := hneg
    rw [ite_eq_right hneg, WP.spec_ok]
    rw [ite_eq_right hneg'] at mr
    rw [← mr]
    exact ⟨tl, wt⟩

end Fulcrum

end
