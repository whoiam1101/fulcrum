module

public import Fulcrum.Round
public import Fulcrum.Narrow

/-!
# L3: `kernel::rescale`

`rescale(raw, src_frac, dst_frac)` of a scaled `i128`, as Aeneas extracts it,
never fails when the scales differ by less than `128`. With bits dropped it is
`shr_round`, rounded to nearest with ties toward `+∞`, and no overflow. With
bits added it is the exact product `raw · 2^s` in two's complement on `128`
bits, and the flag says exactly when that product leaves `i128`.
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace Fulcrum

/-- `i128::wrapping_shl` by `s < 128` is `raw · 2^s` wrapped to `128` bits. -/
theorem wrapping_shl_val (raw : Std.I128) (s : Std.U32) (hs : s.val < 128) :
    (core.num.I128.wrapping_shl raw s).val = wrap 127 (raw.val * 2 ^ s.val) := by
  rw [IScalar.val]
  simp only [core.num.I128.wrapping_shl_bv_eq]
  rw [Nat.mod_eq_of_lt hs]
  exact (BitVec.toInt_shiftLeft_eq_toInt_shiftLeft_bmod _ _).trans
    (by rw [Int.shiftLeft_eq]; rfl)

/-- L3 on the code: `kernel::rescale`. -/
theorem rescale_spec (raw : Std.I128) (src dst : Std.U32) (hs : dst.val - src.val < 128) :
    fulcrum.kernel.rescale raw src dst ⦃ r =>
      if dst.val ≤ src.val then
        r.1.val = roundHalfUp (exact (src.val - dst.val) raw.val) ∧ r.2 = false
      else
        r.1.val = wrap 127 (raw.val * 2 ^ (dst.val - src.val)) ∧
          (r.2 = true ↔ ¬ InRange 127 (raw.val * 2 ^ (dst.val - src.val))) ⦄ := by
  unfold fulcrum.kernel.rescale
  by_cases h : src ≥ dst
  · have h' : dst.val ≤ src.val := h
    rw [ite_eq_left h]
    refine WP.spec_bind (U32.sub_spec h') fun i ⟨hi, _⟩ => ?_
    refine WP.spec_bind (shr_round_spec raw i) fun i1 hi1 => ?_
    rw [WP.spec_ok, ite_eq_left h', hi1, hi]
    exact ⟨rfl, rfl⟩
  have h' : ¬ dst.val ≤ src.val := h
  rw [ite_eq_right h]
  refine WP.spec_bind (U32.sub_spec (Nat.le_of_lt (Nat.lt_of_not_le h'))) fun s ⟨hs', _⟩ => ?_
  have s128 : s.val < 128 := hs' ▸ hs
  rw [lift, bind_ok]
  have hw := wrapping_shl_val raw s s128
  have pos : (0 : ℤ) < 2 ^ s.val := pow_pos zero_lt_two _
  refine WP.spec_bind (IScalar.ShiftRight_spec core.num.I128.MAX s s128) fun i1 ⟨hi1, _⟩ => ?_
  rw [shr_eq_div, show core.num.I128.MAX.val = maxOf 127 from rfl] at hi1
  by_cases hgt : raw > i1
  · rw [ite_eq_left hgt, WP.spec_ok, ite_eq_right h', hw, ← hs']
    have hm : maxOf 127 < raw.val * 2 ^ s.val :=
      (Int.ediv_lt_iff_lt_mul pos).1 (hi1 ▸ (show i1.val < raw.val from hgt))
    exact ⟨rfl, iff_of_true rfl fun r => absurd r.2 (not_le.mpr hm)⟩
  rw [ite_eq_right hgt]
  have hm : raw.val * 2 ^ s.val ≤ maxOf 127 :=
    (Int.le_ediv_iff_mul_le pos).1 (hi1 ▸ (not_lt.mp hgt))
  refine WP.spec_bind (IScalar.ShiftRight_spec core.num.I128.MIN s s128) fun i2 ⟨hi2, _⟩ => ?_
  rw [shr_eq_div, show core.num.I128.MIN.val = minOf 127 from rfl] at hi2
  have dvd : (2 : ℤ) ^ s.val ∣ minOf 127 :=
    ⟨-2 ^ (127 - s.val), by rw [minOf, mul_neg, ← pow_add, Nat.add_sub_of_le (Nat.le_of_lt_succ s128)]⟩
  rw [WP.spec_ok, ite_eq_right h', hw, ← hs']
  refine ⟨rfl, ?_⟩
  rw [decide_eq_true_iff, show raw < i2 ↔ raw.val < i2.val from Iff.rfl, hi2,
    Int.lt_ediv_iff_mul_lt pos dvd]
  exact ⟨fun l r => absurd r.1 (not_le.mpr l), fun n => not_le.mp fun l => n ⟨l, hm⟩⟩

end Fulcrum

end
