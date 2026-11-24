module

public import Fulcrum.L4.SinQuarter
public import Fulcrum.L1.ShrRound
public import Fulcrum.Math.Range

/-!
# L4: `trig::sin_position`, `sin_turns`, `cos_turns` (INTERNALS §3.11)

On the code extracted by Aeneas: `sin_position(t, bits, f)` takes the quadrant
from the top two bits of `t < 2^(bits + 2)` and the position from the rest,
reads the quarter of `sin_quarter` forwards or backwards, rounds once to `f`
bits by `kernel::shr_round` and sets the sign; it is within `½ + 6.1 / 2^(62 - f)`
of `sin (t / 2^bits · π/2) · 2^f`, under `½ + 2^-27` ulp for `f ≤ 32`.
`sin_turns` masks the fraction of a turn and `cos_turns` adds a quarter turn,
wrapping, so both hold for every raw value and `2 ≤ f ≤ 62`.
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace Fulcrum

set_option maxRecDepth 10000

/-- L4 on the code: `trig::sin_position` of `t < 2^(bits + 2)`, `bits ≤ 62`,
`f ≤ 62` never fails and is within `½ + 6.1 / 2^(62 - f)` of
`sin (t / 2^bits · π/2) · 2^f`: the quarter of the low `bits` bits, read
backwards in an odd quadrant, rounded once and signed by the quadrant. -/
theorem sin_position_spec (t : Std.U64) (bits f : Std.U32) (hb : bits.val ≤ 62) (hf : f.val ≤ 62)
    (ht : t.val < 2 ^ (bits.val + 2)) :
    fulcrum.trig.sin_position t bits f ⦃ r =>
      |(r.val : ℝ) - Real.sin (t.val / 2 ^ bits.val * (Real.pi / 2)) * 2 ^ f.val| ≤
        1 / 2 + 61 / 10 / 2 ^ (62 - f.val) ⦄ := by
  unfold fulcrum.trig.sin_position
  refine WP.spec_bind (UScalar.ShiftRight_spec t bits (by rw [UScalarTy.U64_numBits_eq]; omega))
    fun q ⟨hq, _⟩ => ?_
  rw [Nat.shiftRight_eq_div_pow] at hq
  have q4 : q.val < 4 := by
    rw [hq, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    exact ht.trans_eq (by rw [pow_add, mul_comm]; rfl)
  refine WP.spec_bind (UScalar.ShiftLeft_spec 1#u64 bits _ (by rw [UScalarTy.U64_numBits_eq]; omega) rfl)
    fun i ⟨hi, _⟩ => ?_
  rw [lit_val, Nat.shiftLeft_eq, one_mul, UScalar.size_def, UScalarTy.U64_numBits_eq,
    Nat.mod_eq_of_lt (Nat.pow_lt_pow_right one_lt_two (by omega))] at hi
  refine WP.spec_bind (UScalar.sub_spec (x := i) (y := 1#u64) (by rw [hi, lit_val]; exact Nat.one_le_two_pow))
    fun i1 ⟨hi1, _⟩ => ?_
  rw [hi, lit_val] at hi1
  rw [lift, bind_ok]
  have pv : (t &&& i1).val = t.val % 2 ^ bits.val := by
    rw [UScalar.val_and, hi1, Nat.and_two_pow_sub_one_eq_mod]
  generalize t &&& i1 = p at pv ⊢
  have pl : p.val < 2 ^ bits.val := pv ▸ Nat.mod_lt _ (Nat.two_pow_pos _)
  have tq : t.val = q.val * 2 ^ bits.val + p.val := by
    rw [hq, pv, mul_comm]; exact (Nat.div_add_mod _ _).symm
  rw [lift, bind_ok]
  have i2v : (q &&& 1#u64).val = q.val % 2 := by rw [UScalar.val_and, lit_val, Nat.and_one_is_mod]
  generalize q &&& 1#u64 = i2 at i2v ⊢
  set p' : ℕ := if q.val % 2 = 0 then p.val else 2 ^ bits.val - p.val with hp'
  set S : ℝ := Real.sin (p' / 2 ^ bits.val * (Real.pi / 2)) with hS
  refine WP.spec_bind (Pₘ := fun m : Std.U64 => |(m.val : ℝ) - S * 2 ^ 62| ≤ 61 / 10) ?_ fun m hm => ?_
  · by_cases h0 : i2 = 0#u64
    · have e : q.val % 2 = 0 := by rw [← i2v, h0]; rfl
      rw [ite_eq_left h0]
      refine WP.spec_mono (sin_quarter_spec p bits hb pl.le) fun m hm => ?_
      rw [hS, hp', ite_eq_left e]; exact hm
    · have e : ¬ q.val % 2 = 0 := fun e => h0 (UScalar.eq_of_val_eq (by rw [i2v, e]; rfl))
      rw [ite_eq_right h0]
      refine WP.spec_bind (UScalar.sub_spec (x := i) (y := p) (by rw [hi]; exact pl.le)) fun i3 ⟨hi3, _⟩ => ?_
      rw [hi] at hi3
      refine WP.spec_mono (sin_quarter_spec i3 bits hb (hi3 ▸ Nat.sub_le _ _)) fun m hm => ?_
      rw [hS, hp', ite_eq_right e, ← hi3]; exact hm
  have S1 : S ≤ 1 := Real.sin_le_one _
  have hc : (UScalar.hcast .I128 m).val = m.val := by
    have mb : (m.val : ℤ) < 2 ^ 64 := by exact_mod_cast m.bv.isLt
    rw [UScalar.hcast_val_eq, IScalarTy.I128_numBits_eq]
    exact Int.bmod_eq_of_le ((neg_nonpos.mpr (by positivity)).trans (Int.natCast_nonneg _))
      (mb.trans_le (by norm_num))
  rw [lift, bind_ok]
  refine WP.spec_bind (UScalar.sub_spec (x := fulcrum.tables.trig.FRAC) (y := f)
    (by rw [trig_frac_val]; exact hf)) fun i4 ⟨hi4, _⟩ => ?_
  rw [trig_frac_val] at hi4
  refine WP.spec_bind (shr_round_spec _ i4) fun i5 hi5 => ?_
  rw [hc, hi4] at hi5
  have near := round_shift_near m.val (62 - f.val) f.val (by omega) S (61 / 10) (by exact_mod_cast hm)
  rw [← hi5] at near
  have err : 1 / 2 + 61 / 10 / 2 ^ (62 - f.val) ≤ (7 : ℝ) :=
    (add_le_add le_rfl (div_le_self (by norm_num) (one_le_pow₀ one_le_two))).trans (by norm_num)
  have i5b : |(i5.val : ℝ)| ≤ 2 ^ 62 + 7 := by
    have sf : |S * 2 ^ f.val| ≤ 2 ^ 62 := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ f.val)]
      exact (mul_le_mul (Real.abs_sin_le_one _) (pow_le_pow_right₀ one_le_two hf) (by positivity)
        zero_le_one).trans_eq (one_mul _)
    calc |(i5.val : ℝ)| ≤ |(i5.val : ℝ) - S * 2 ^ f.val| + |S * 2 ^ f.val| :=
          sub_le_iff_le_add.mp (abs_sub_abs_le_abs_sub _ _)
      _ ≤ 7 + 2 ^ 62 := add_le_add (near.trans err) sf
      _ = 2 ^ 62 + 7 := add_comm _ _
  have i5i : -(2 ^ 62 + 7) ≤ i5.val ∧ i5.val ≤ 2 ^ 62 + 7 := by
    have ⟨l, u⟩ := abs_le.mp i5b
    exact ⟨by exact_mod_cast l, by exact_mod_cast u⟩
  have inr : InRange 63 i5.val :=
    ⟨(by unfold minOf; norm_num : minOf 63 ≤ -(2 ^ 62 + 7)).trans i5i.1,
      i5i.2.trans (by unfold maxOf; norm_num)⟩
  have cv : (IScalar.cast .I64 i5).val = i5.val :=
    (IScalar.cast_val_eq .I64 i5).trans ((wrap_eq_self_iff 63 _).2 inr)
  rw [lift, bind_ok]
  have tR : (t.val : ℝ) = ((q.val * 2 ^ bits.val + p.val : ℕ) : ℝ) := by rw [tq]
  rw [tR, sin_quadrant q.val p.val bits.val q4 pl.le, ← hp', ← hS]
  by_cases h2 : q < 2#u64
  · have h2' : q.val < 2 := h2
    rw [ite_eq_left h2, WP.spec_ok, cv, ite_eq_left h2', one_mul]
    exact near
  · have h2' : ¬ q.val < 2 := h2
    rw [ite_eq_right h2, ite_eq_right h2']
    refine WP.spec_mono (IScalar.neg_step _ (fun e => ?_)) fun r hr => ?_
    · rw [cv, IScalar.min_def, IScalarTy.I64_numBits_eq] at e
      have := i5i.1; omega
    · rw [hr, cv]; push_cast
      rw [show -(i5.val : ℝ) - -1 * S * 2 ^ f.val = -((i5.val : ℝ) - S * 2 ^ f.val) by ring, abs_neg]
      exact near

/-- L4 on the code: `trig::sin_turns` with `2 ≤ f ≤ 62` never fails and is within
`½ + 6.1 / 2^(62 - f)` of `sin (2π · raw / 2^f) · 2^f`. -/
theorem sin_turns_spec (raw : Std.U64) (f : Std.U32) (hf2 : 2 ≤ f.val) (hf : f.val ≤ 62) :
    fulcrum.trig.sin_turns raw f ⦃ r =>
      |(r.val : ℝ) - Real.sin (2 * Real.pi * raw.val / 2 ^ f.val) * 2 ^ f.val| ≤
        1 / 2 + 61 / 10 / 2 ^ (62 - f.val) ⦄ := by
  unfold fulcrum.trig.sin_turns
  refine WP.spec_bind (UScalar.ShiftLeft_spec 1#u64 f _ (by rw [UScalarTy.U64_numBits_eq]; omega) rfl)
    fun i ⟨hi, _⟩ => ?_
  rw [lit_val, Nat.shiftLeft_eq, one_mul, UScalar.size_def, UScalarTy.U64_numBits_eq,
    Nat.mod_eq_of_lt (Nat.pow_lt_pow_right one_lt_two (by omega))] at hi
  refine WP.spec_bind (UScalar.sub_spec (x := i) (y := 1#u64) (by rw [hi, lit_val]; exact Nat.one_le_two_pow))
    fun i1 ⟨hi1, _⟩ => ?_
  rw [hi, lit_val] at hi1
  rw [lift, bind_ok]
  have tv : (raw &&& i1).val = raw.val % 2 ^ f.val := by
    rw [UScalar.val_and, hi1, Nat.and_two_pow_sub_one_eq_mod]
  generalize raw &&& i1 = t at tv ⊢
  refine WP.spec_bind (UScalar.sub_spec (x := f) (y := 2#u32) (by rw [lit_val]; exact hf2))
    fun i3 ⟨hi3, _⟩ => ?_
  rw [lit_val] at hi3
  refine WP.spec_mono (sin_position_spec t i3 f (by omega) hf (by
    rw [tv, hi3, Nat.sub_add_cancel hf2]; exact Nat.mod_lt _ (Nat.two_pow_pos _))) fun r hr => ?_
  rw [sin_turn_mod, ← tv]
  have e : (t.val : ℝ) / 2 ^ i3.val * (Real.pi / 2) = 2 * Real.pi * t.val / 2 ^ f.val := by
    have : (2 : ℝ) ^ f.val = 2 ^ i3.val * 4 := by
      rw [hi3, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_add, Nat.sub_add_cancel hf2]
    rw [this]; field_simp; ring
  rw [e] at hr
  exact hr

/-- L4 on the code: `trig::cos_turns` with `2 ≤ f ≤ 62` never fails and is within
`½ + 6.1 / 2^(62 - f)` of `cos (2π · raw / 2^f) · 2^f`. -/
theorem cos_turns_spec (raw : Std.U64) (f : Std.U32) (hf2 : 2 ≤ f.val) (hf : f.val ≤ 62) :
    fulcrum.trig.cos_turns raw f ⦃ r =>
      |(r.val : ℝ) - Real.cos (2 * Real.pi * raw.val / 2 ^ f.val) * 2 ^ f.val| ≤
        1 / 2 + 61 / 10 / 2 ^ (62 - f.val) ⦄ := by
  unfold fulcrum.trig.cos_turns
  refine WP.spec_bind (UScalar.sub_spec (x := f) (y := 2#u32) (by rw [lit_val]; exact hf2))
    fun i ⟨hi, _⟩ => ?_
  rw [lit_val] at hi
  refine WP.spec_bind (UScalar.ShiftLeft_spec 1#u64 i _ (by rw [hi, UScalarTy.U64_numBits_eq]; omega) rfl)
    fun i1 ⟨hi1, _⟩ => ?_
  rw [hi, lit_val, Nat.shiftLeft_eq, one_mul, UScalar.size_def, UScalarTy.U64_numBits_eq,
    Nat.mod_eq_of_lt (Nat.pow_lt_pow_right one_lt_two (by omega))] at hi1
  rw [lift, bind_ok]
  refine WP.spec_mono (sin_turns_spec _ f hf2 hf) fun r hr => ?_
  have wv : (core.num.U64.wrapping_add raw i1).val % 2 ^ f.val = (raw.val + 2 ^ (f.val - 2)) % 2 ^ f.val := by
    rw [show core.num.U64.wrapping_add raw i1 = UScalar.wrapping_add raw i1 from rfl,
      UScalar.wrapping_add_val_eq, hi1, UScalar.size_def, UScalarTy.U64_numBits_eq,
      Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]
  rw [sin_turn_mod, wv, ← sin_turn_mod] at hr
  have e : 2 * Real.pi * ((raw.val + 2 ^ (f.val - 2) : ℕ) : ℝ) / 2 ^ f.val =
      2 * Real.pi * raw.val / 2 ^ f.val + Real.pi / 2 := by
    have : (2 : ℝ) ^ f.val = 2 ^ (f.val - 2) * 4 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_add, Nat.sub_add_cancel hf2]
    rw [this]; push_cast; field_simp; ring
  rw [e, Real.sin_add_pi_div_two] at hr
  exact hr
end Fulcrum

end
