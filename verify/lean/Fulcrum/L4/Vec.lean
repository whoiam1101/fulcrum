module

public import Fulcrum.L4.Atan
public import Fulcrum.Spec
import Fulcrum.L1.ShrRound
import Fulcrum.L3.Sqrt.K64
import Fulcrum.L4.Angle
import Fulcrum.L4.SinQuarter
import Fulcrum.Lemmas.Scalar
import Fulcrum.Math.Atan
import Fulcrum.Math.Quarter
import Mathlib.Algebra.Order.Ring.Star
import all Aeneas.Std.Scalar.OverflowingOps.Add

/-!
# L4: `trig::rotate`, `atan2_wide`, `angle_between2`, `angle_between3` (INTERNALS §3.15)

On the code extracted by Aeneas.

- `angle_sin_frac` is the quarter of `sin_position` before its rounding, within `6.1`
  units; `rotate` multiplies exactly and rounds each component once: within
  `½ + 6.1 (|x| + |y|) / 2^62` of the turned vector.
- `to_63_bits` scales a pair by `κ = 2^62 / 2^⌊log₂ max⌋`, truncating by less than `1`,
  the larger into `[2^62, 2^63)`; truncating moves the angle by at most `1.01 · e / 2^62`
  (`arg_truncate` of `Math/Atan.lean`), so `atan2_wide` is within `½ + 5 / 2^(62 - f)`.
- `sum_parts` and `add_parts` are exact sums as a sign and a magnitude, so
  `angle_between2` is `atan2_wide` of the exact cross and dot products.
- `angle_between3`: the cross components and the dot product are shifted together,
  the integer root of the sum of squares is within `2.74` below the scaled length
  (`root_length_near`), and the pair is shifted again: within `½ + 8 / 2^(62 - f)` of
  `arg (a · b + |a × b| i) · 2^f`.

`overflowing_add` of a signed type has no exposed body in Aeneas; the file reads it with
`import all` of its module.
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace Fulcrum

set_option maxRecDepth 10000

/-- L4 on the code: `trig::angle_sin_frac` of `t < 2^n`, `2 ≤ n ≤ 64`, never fails and
is within `6.1` units of `sin (2π · t / 2^n) · 2^62`, unrounded, of magnitude at most
`2^62 + 7`. -/
theorem angle_sin_frac_spec (t : Std.U64) (n : Std.U32) (hn2 : 2 ≤ n.val) (hn : n.val ≤ 64)
    (ht : t.val < 2 ^ n.val) :
    fulcrum.trig.angle_sin_frac t n ⦃ r =>
      |(r.val : ℝ) - Real.sin (2 * Real.pi * t.val / 2 ^ n.val) * 2 ^ 62| ≤ 61 / 10 ∧
        |r.val| ≤ 2 ^ 62 + 7 ⦄ := by
  unfold fulcrum.trig.angle_sin_frac
  refine WP.spec_bind (UScalar.sub_spec (x := n) (y := 2#u32) (by rw [lit_val]; exact hn2))
    fun bits ⟨hb, _⟩ => ?_
  rw [lit_val] at hb
  refine WP.spec_bind (UScalar.ShiftRight_spec t bits (by rw [hb, UScalarTy.U64_numBits_eq]; omega))
    fun q ⟨hq, _⟩ => ?_
  rw [Nat.shiftRight_eq_div_pow] at hq
  have ht' : t.val < 2 ^ (bits.val + 2) := by rw [hb, Nat.sub_add_cancel hn2]; exact ht
  have q4 : q.val < 4 := by
    rw [hq, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    exact ht'.trans_eq (by rw [pow_add, mul_comm]; rfl)
  refine WP.spec_bind (UScalar.ShiftLeft_spec 1#u64 bits _ (by rw [hb, UScalarTy.U64_numBits_eq]; omega) rfl)
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
  set! p' : ℕ := if q.val % 2 = 0 then p.val else 2 ^ bits.val - p.val with hp'
  set! S : ℝ := Real.sin (p' / 2 ^ bits.val * (Real.pi / 2)) with hS
  refine WP.spec_bind (Pₘ := fun m : Std.U64 => |(m.val : ℝ) - S * 2 ^ 62| ≤ 61 / 10) ?_ fun m hm => ?_
  · by_cases h0 : i2 = 0#u64
    · have e : q.val % 2 = 0 := by rw [← i2v, h0]; rfl
      rw [ite_eq_left h0]
      refine WP.spec_mono (sin_quarter_spec p bits (by omega) pl.le) fun m hm => ?_
      rw [hS, hp', ite_eq_left e]; exact hm
    · have e : ¬ q.val % 2 = 0 := fun e => h0 (UScalar.eq_of_val_eq (by rw [i2v, e]; rfl))
      rw [ite_eq_right h0]
      refine WP.spec_bind (UScalar.sub_spec (x := i) (y := p) (by rw [hi]; exact pl.le)) fun i3 ⟨hi3, _⟩ => ?_
      rw [hi] at hi3
      refine WP.spec_mono (sin_quarter_spec i3 bits (by omega) (hi3 ▸ Nat.sub_le _ _)) fun m hm => ?_
      rw [hS, hp', ite_eq_right e, ← hi3]; exact hm
  have S1 : |S| ≤ 1 := Real.abs_sin_le_one _
  have mb : (m.val : ℝ) ≤ 2 ^ 62 + 7 := by
    have : S * 2 ^ 62 ≤ 2 ^ 62 := by nlinarith only [(abs_le.mp S1).2]
    linarith only [(abs_le.mp hm).2, this]
  have mb' : m.val ≤ 2 ^ 62 + 7 := by exact_mod_cast mb
  have hc : (UScalar.hcast .I64 m).val = m.val := by
    rw [UScalar.hcast_val_eq, IScalarTy.I64_numBits_eq]
    exact Int.bmod_eq_of_le ((neg_nonpos.mpr (by positivity)).trans (Int.natCast_nonneg _))
      ((by exact_mod_cast mb' : (m.val : ℤ) ≤ 2 ^ 62 + 7).trans_lt (by norm_num))
  rw [lift, bind_ok]
  have tR : (t.val : ℝ) = ((q.val * 2 ^ bits.val + p.val : ℕ) : ℝ) := by rw [tq]
  have e : 2 * Real.pi * (t.val : ℝ) / 2 ^ n.val = ((q.val * 2 ^ bits.val + p.val : ℕ) : ℝ) / 2 ^ bits.val * (Real.pi / 2) := by
    have : (2 : ℝ) ^ n.val = 2 ^ bits.val * 4 := by
      rw [hb, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_add, Nat.sub_add_cancel hn2]
    rw [tR, this]; field_simp; ring
  rw [e, sin_quadrant q.val p.val bits.val q4 pl.le, ← hp', ← hS]
  have m0 : (0 : ℤ) ≤ m.val := Int.natCast_nonneg _
  by_cases h2 : q < 2#u64
  · have h2' : q.val < 2 := h2
    rw [ite_eq_left h2, WP.spec_ok, hc, ite_eq_left h2', one_mul]
    refine ⟨by exact_mod_cast hm, ?_⟩
    rw [abs_of_nonneg m0]; exact_mod_cast mb'
  · have h2' : ¬ q.val < 2 := h2
    rw [ite_eq_right h2, ite_eq_right h2']
    refine WP.spec_mono (IScalar.neg_step _ (fun e => ?_)) fun r hr => ?_
    · rw [hc, IScalar.min_def, IScalarTy.I64_numBits_eq] at e
      omega
    · rw [hr, hc]
      refine ⟨?_, by rw [abs_neg, abs_of_nonneg m0]; exact_mod_cast mb'⟩
      push_cast
      rw [show -(m.val : ℝ) - -1 * S * 2 ^ 62 = -((m.val : ℝ) - S * 2 ^ 62) by ring, abs_neg]
      exact hm

/-- One rounded component of `rotate`: `rnd(v / 2^62)` for `v = a · c ± b · s` with
`c`, `s` within `6.1` of `C · 2^62`, `S · 2^62` is within `½ + 6.1 (|a| + |b|) / 2^62`
of `a · C ± b · S`. -/
theorem rotate_component (v a b c s : ℤ) (C S : ℝ) (hc : |(c : ℝ) - C * 2 ^ 62| ≤ 61 / 10)
    (hs : |(s : ℝ) - S * 2 ^ 62| ≤ 61 / 10) (hv : v = a * c + b * s) :
    |((roundHalfUp (exact 62 v) : ℤ) : ℝ) - (a * C + b * S)| ≤
      1 / 2 + 61 / 10 * (|(a : ℝ)| + |(b : ℝ)|) / 2 ^ 62 := by
  refine round_div_near v 62 _ _ ?_
  rw [hv]; push_cast
  rw [show (a : ℝ) * c + b * s - (a * C + b * S) * 2 ^ 62 = a * (c - C * 2 ^ 62) + b * (s - S * 2 ^ 62) by ring]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, mul_add]
  exact add_le_add (by nlinarith only [abs_nonneg (a : ℝ), hc]) (by nlinarith only [abs_nonneg (b : ℝ), hs])

/-- L4 on the code: `trig::rotate(x, y, t, n)` with `2 ≤ n ≤ 64` never fails and turns
`(x, y)` by `θ = 2π · t / 2^n`: each component is within `½ + 6.1 (|x| + |y|) / 2^62`
of `x cos θ - y sin θ` and `x sin θ + y cos θ`, before saturation. -/
theorem rotate_spec (x y : Std.I64) (t : Std.U64) (n : Std.U32) (hn2 : 2 ≤ n.val) (hn : n.val ≤ 64) :
    fulcrum.trig.rotate x y t n ⦃ r =>
      |(r.1.val : ℝ) - (x.val * Real.cos (2 * Real.pi * t.val / 2 ^ n.val) -
          y.val * Real.sin (2 * Real.pi * t.val / 2 ^ n.val))| ≤
        1 / 2 + 61 / 10 * (|(x.val : ℝ)| + |(y.val : ℝ)|) / 2 ^ 62 ∧
      |(r.2.val : ℝ) - (x.val * Real.sin (2 * Real.pi * t.val / 2 ^ n.val) +
          y.val * Real.cos (2 * Real.pi * t.val / 2 ^ n.val))| ≤
        1 / 2 + 61 / 10 * (|(x.val : ℝ)| + |(y.val : ℝ)|) / 2 ^ 62 ⦄ := by
  unfold fulcrum.trig.rotate
  refine WP.spec_bind (angle_mask_spec n hn) fun msk hmsk => ?_
  rw [lift, bind_ok]
  refine WP.spec_bind (angle_sin_frac_spec _ n hn2 hn (by rw [and_mask_val _ _ _ hmsk]; exact Nat.mod_lt _ (Nat.two_pow_pos _)))
    fun s0 ⟨hs0, bs0⟩ => ?_
  rw [and_mask_val _ _ _ hmsk, ← sin_turn_mod] at hs0
  rw [lift, bind_ok]
  refine WP.spec_bind (UScalar.sub_spec (x := n) (y := 2#u32) (by rw [lit_val]; exact hn2)) fun i3 ⟨h3, _⟩ => ?_
  rw [lit_val] at h3
  refine WP.spec_bind (UScalar.ShiftLeft_spec 1#u64 i3 _ (by rw [h3, UScalarTy.U64_numBits_eq]; omega) rfl)
    fun i4 ⟨h4, _⟩ => ?_
  rw [h3, lit_val, Nat.shiftLeft_eq, one_mul, UScalar.size_def, UScalarTy.U64_numBits_eq,
    Nat.mod_eq_of_lt (Nat.pow_lt_pow_right one_lt_two (by omega))] at h4
  rw [lift, bind_ok, lift, bind_ok]
  have wv : (core.num.U64.wrapping_add t i4 &&& msk).val = (t.val + 2 ^ (n.val - 2)) % 2 ^ n.val := by
    rw [and_mask_val _ _ _ hmsk, show core.num.U64.wrapping_add t i4 = UScalar.wrapping_add t i4 from rfl,
      UScalar.wrapping_add_val_eq, h4, UScalar.size_def, UScalarTy.U64_numBits_eq,
      Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hn)]
  refine WP.spec_bind (angle_sin_frac_spec _ n hn2 hn (by rw [wv]; exact Nat.mod_lt _ (Nat.two_pow_pos _)))
    fun c0 ⟨hc0, bc0⟩ => ?_
  rw [wv, ← sin_turn_mod] at hc0
  have e : 2 * Real.pi * ((t.val + 2 ^ (n.val - 2) : ℕ) : ℝ) / 2 ^ n.val =
      2 * Real.pi * t.val / 2 ^ n.val + Real.pi / 2 := by
    have : (2 : ℝ) ^ n.val = 2 ^ (n.val - 2) * 4 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_add, Nat.sub_add_cancel hn2]
    rw [this]; push_cast; field_simp; ring
  rw [e, Real.sin_add_pi_div_two] at hc0
  set θ := 2 * Real.pi * (t.val : ℝ) / 2 ^ n.val
  rw [lift, bind_ok, lift, bind_ok, lift, bind_ok]
  have ⟨xl, xu⟩ := val_bounds x IScalarTy.I64_numBits_eq
  have ⟨yl, yu⟩ := val_bounds y IScalarTy.I64_numBits_eq
  have xa : |x.val| ≤ 2 ^ 63 := abs_le.mpr ⟨xl, xu.le⟩
  have ya : |y.val| ≤ 2 ^ 63 := abs_le.mpr ⟨yl, yu.le⟩
  have pb : ∀ a b : ℤ, |a| ≤ 2 ^ 63 → |b| ≤ 2 ^ 62 + 7 → |a * b| ≤ 2 ^ 125 + 2 ^ 66 := fun a b ha hb => by
    rw [abs_mul]
    calc |a| * |b| ≤ 2 ^ 63 * (2 ^ 62 + 7) := mul_le_mul ha hb (abs_nonneg _) (by positivity)
      _ ≤ 2 ^ 125 + 2 ^ 66 := by norm_num
  have mn : IScalar.min .I128 = -2 ^ 127 := min_eq_neg_pow IScalarTy.I128_numBits_eq
  have mx : IScalar.max .I128 = 2 ^ 127 - 1 := max_eq_pow_sub_one IScalarTy.I128_numBits_eq
  have b1 := pb _ _ xa bc0
  have b2 := pb _ _ ya bs0
  have b3 := pb _ _ xa bs0
  have b4 := pb _ _ ya bc0
  refine WP.spec_bind (IScalar.mul_spec (x := IScalar.cast .I128 x) (y := IScalar.cast .I128 c0)
    (by rw [cast_i128_val, cast_i128_val, mn]; linarith only [(abs_le.mp b1).1])
    (by rw [cast_i128_val, cast_i128_val, mx]; linarith only [(abs_le.mp b1).2])) fun i8 h8 => ?_
  refine WP.spec_bind (IScalar.mul_spec (x := IScalar.cast .I128 y) (y := IScalar.cast .I128 s0)
    (by rw [cast_i128_val, cast_i128_val, mn]; linarith only [(abs_le.mp b2).1])
    (by rw [cast_i128_val, cast_i128_val, mx]; linarith only [(abs_le.mp b2).2])) fun i9 h9 => ?_
  rw [cast_i128_val, cast_i128_val] at h8 h9
  refine WP.spec_bind (IScalar.sub_spec (x := i8) (y := i9)
    (by rw [h8, h9, mn]; linarith only [(abs_le.mp b1).1, (abs_le.mp b2).2])
    (by rw [h8, h9, mx]; linarith only [(abs_le.mp b1).2, (abs_le.mp b2).1])) fun i10 h10 => ?_
  refine WP.spec_bind (shr_round_spec i10 fulcrum.tables.trig.FRAC) fun i11 h11 => ?_
  refine WP.spec_bind (IScalar.mul_spec (x := IScalar.cast .I128 x) (y := IScalar.cast .I128 s0)
    (by rw [cast_i128_val, cast_i128_val, mn]; linarith only [(abs_le.mp b3).1])
    (by rw [cast_i128_val, cast_i128_val, mx]; linarith only [(abs_le.mp b3).2])) fun i12 h12 => ?_
  refine WP.spec_bind (IScalar.mul_spec (x := IScalar.cast .I128 y) (y := IScalar.cast .I128 c0)
    (by rw [cast_i128_val, cast_i128_val, mn]; linarith only [(abs_le.mp b4).1])
    (by rw [cast_i128_val, cast_i128_val, mx]; linarith only [(abs_le.mp b4).2])) fun i13 h13 => ?_
  rw [cast_i128_val, cast_i128_val] at h12 h13
  refine WP.spec_bind (IScalar.add_spec (x := i12) (y := i13)
    (by rw [h12, h13, mn]; linarith only [(abs_le.mp b3).1, (abs_le.mp b4).1])
    (by rw [h12, h13, mx]; linarith only [(abs_le.mp b3).2, (abs_le.mp b4).2])) fun i14 h14 => ?_
  refine WP.spec_bind (shr_round_spec i14 fulcrum.tables.trig.FRAC) fun i15 h15 => ?_
  rw [WP.spec_ok]
  rw [trig_frac_val] at h11 h15
  dsimp only
  rw [h11, h15]
  refine ⟨?_, ?_⟩
  · have := rotate_component i10.val x.val (-y.val) c0.val s0.val (Real.cos θ) (Real.sin θ) hc0 hs0
      (by rw [h10, h8, h9]; ring)
    push_cast at this
    rw [abs_neg] at this
    rw [show (x.val : ℝ) * Real.cos θ - y.val * Real.sin θ = x.val * Real.cos θ + -y.val * Real.sin θ by ring]
    exact this
  · have := rotate_component i14.val x.val y.val s0.val c0.val (Real.sin θ) (Real.cos θ) hs0 hc0
      (by rw [h14, h12, h13])
    exact this

/-- L4 on the code: `trig::shift_to(v, bits, 63)` with `bits ≤ 128` is `⌊v / 2^(bits - 63)⌋`
above 63 bits and `v · 2^(63 - bits)` otherwise, when that fits. -/
theorem shift_to_spec (v : Std.U128) (bits : Std.U32) (hb : bits.val ≤ 128)
    (hfit : bits.val ≤ 63 → v.val * 2 ^ (63 - bits.val) < 2 ^ 128) :
    fulcrum.trig.shift_to v bits 63#u32 ⦃ r =>
      r.val = if 63 < bits.val then v.val / 2 ^ (bits.val - 63) else v.val * 2 ^ (63 - bits.val) ⦄ := by
  have n128 : UScalarTy.U128.numBits = 128 := rfl
  unfold fulcrum.trig.shift_to
  by_cases h : bits > 63#u32
  · have h' : 63 < bits.val := by have := h; rw [GT.gt, UScalar.lt_equiv, lit_val] at this; exact this
    rw [ite_eq_left h, ite_eq_left h']
    refine WP.spec_bind (UScalar.sub_spec (x := bits) (y := 63#u32) (by rw [lit_val]; omega)) fun i ⟨hi, _⟩ => ?_
    rw [lit_val] at hi
    refine WP.spec_mono (UScalar.ShiftRight_spec v i (by rw [hi, n128]; omega)) fun r ⟨hr, _⟩ => ?_
    rw [hr, hi, Nat.shiftRight_eq_div_pow]
  · have h' : ¬ 63 < bits.val := by
      intro e; exact h (by rw [GT.gt, UScalar.lt_equiv, lit_val]; exact e)
    rw [ite_eq_right h, ite_eq_right h']
    refine WP.spec_bind (UScalar.sub_spec (x := 63#u32) (y := bits) (by rw [lit_val]; omega)) fun i ⟨hi, _⟩ => ?_
    rw [lit_val] at hi
    refine WP.spec_mono (UScalar.ShiftLeft_spec v i _ (by rw [hi, n128]; omega) rfl) fun r ⟨hr, _⟩ => ?_
    rw [hr, hi, Nat.shiftLeft_eq, UScalar.size_def, n128, Nat.mod_eq_of_lt (hfit (by omega))]

/-- The shift of `to_63_bits` on one value `v ≤ M`, `2^L ≤ M < 2^(L+1)`: below `2^63`,
within `1` below `v · 2^62 / 2^L`, and at least `2^62` for `v = M`. -/
theorem shift63_props (v M L : ℕ) (hv : v ≤ M) (hL : 2 ^ L ≤ M) (hL1 : M < 2 ^ (L + 1)) :
    let s := if 63 < L + 1 then v / 2 ^ (L + 1 - 63) else v * 2 ^ (63 - (L + 1))
    (s : ℝ) ≤ v * 2 ^ 62 / 2 ^ L ∧ (v : ℝ) * 2 ^ 62 / 2 ^ L < s + 1 ∧ s < 2 ^ 63 ∧
      (v = M → 2 ^ 62 ≤ s) := by
  intro s
  have vl : v < 2 ^ (L + 1) := lt_of_le_of_lt hv hL1
  by_cases h : 63 < L + 1
  · have sv : s = v / 2 ^ (L - 62) := by simp only [s, ite_eq_left h]; congr 2
    have e : (v : ℝ) * 2 ^ 62 / 2 ^ L = v / 2 ^ (L - 62) := by
      have : (2 : ℝ) ^ L = 2 ^ (L - 62) * 2 ^ 62 := by rw [← pow_add]; congr 1; omega
      rw [this]; field_simp
    have ⟨l, u⟩ := floor_div_near v (2 ^ (L - 62)) (by positivity)
    push_cast at l u
    rw [sv, e]
    refine ⟨l, by linarith only [u], ?_, fun hvM => ?_⟩
    · rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add]
      exact vl.trans_le (Nat.pow_le_pow_right two_pos (by omega))
    · rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos _), ← pow_add, hvM]
      exact (Nat.pow_le_pow_right two_pos (by omega)).trans hL
  · have sv : s = v * 2 ^ (62 - L) := by simp only [s, ite_eq_right h]; congr 2; omega
    have e : (v : ℝ) * 2 ^ 62 / 2 ^ L = v * 2 ^ (62 - L) := by
      have : (2 : ℝ) ^ 62 = 2 ^ (62 - L) * 2 ^ L := by rw [← pow_add]; congr 1; omega
      rw [this]; field_simp
    rw [sv, e]; push_cast
    refine ⟨le_rfl, by linarith only [], ?_, fun hvM => ?_⟩
    · calc v * 2 ^ (62 - L) < 2 ^ (L + 1) * 2 ^ (62 - L) := Nat.mul_lt_mul_of_pos_right vl (by positivity)
        _ = 2 ^ 63 := by rw [← pow_add]; congr 1; omega
    · rw [hvM]
      calc 2 ^ 62 = 2 ^ L * 2 ^ (62 - L) := by rw [← pow_add]; congr 1; omega
        _ ≤ M * 2 ^ (62 - L) := Nat.mul_le_mul_right _ hL

/-- L4 on the code: `trig::to_63_bits(a, b)`, not both `0`, never fails and scales both by
`κ = 2^62 / 2^L`, `L = ⌊log₂ max(a, b)⌋`, truncating by less than `1`: both below `2^63`,
the larger at least `2^62`. -/
theorem to_63_bits_spec (a b : Std.U128) (h0 : 0 < a.val ∨ 0 < b.val) :
    fulcrum.trig.to_63_bits a b ⦃ p =>
      (p.1.val : ℝ) ≤ a.val * 2 ^ 62 / 2 ^ Nat.log 2 (max a.val b.val) ∧
      (a.val : ℝ) * 2 ^ 62 / 2 ^ Nat.log 2 (max a.val b.val) < p.1.val + 1 ∧
      (p.2.val : ℝ) ≤ b.val * 2 ^ 62 / 2 ^ Nat.log 2 (max a.val b.val) ∧
      (b.val : ℝ) * 2 ^ 62 / 2 ^ Nat.log 2 (max a.val b.val) < p.2.val + 1 ∧
      p.1.val < 2 ^ 63 ∧ p.2.val < 2 ^ 63 ∧ 2 ^ 62 ≤ max p.1.val p.2.val ⦄ := by
  unfold fulcrum.trig.to_63_bits
  refine WP.spec_bind (Pₘ := fun m : Std.U128 => m.val = max a.val b.val) ?_ fun m hm => ?_
  · by_cases h : a > b
    · have h' : b.val < a.val := h
      rw [ite_eq_left h, WP.spec_ok, max_eq_left h'.le]
    · have h' : ¬ b.val < a.val := h
      rw [ite_eq_right h, WP.spec_ok, max_eq_right (not_lt.mp h')]
  have m0 : m.val ≠ 0 := by rw [hm]; omega
  set L := Nat.log 2 (max a.val b.val) with hL
  have hlo : 2 ^ L ≤ max a.val b.val := Nat.pow_log_le_self 2 (hm ▸ m0)
  have hhi : max a.val b.val < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two _
  have Lle : L ≤ 127 := by
    have : max a.val b.val < 2 ^ 128 := max_lt a.bv.isLt b.bv.isLt
    exact Nat.le_of_lt_succ ((Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp (hlo.trans_lt this))
  have hlz : (core.num.U128.leading_zeros m).val = 128 - L - 1 := by
    rw [hL, ← hm]; exact leading_zeros_val m m0 (Nat.le_of_ble_eq_true rfl)
  rw [lift, bind_ok]
  refine WP.spec_bind (UScalar.sub_spec (x := 128#u32) (y := core.num.U128.leading_zeros m)
    (by rw [hlz, lit_val]; omega)) fun bits ⟨hb, _⟩ => ?_
  rw [hlz, lit_val] at hb
  have bv : bits.val = L + 1 := by omega
  have fit : ∀ v : Std.U128, v.val ≤ max a.val b.val → bits.val ≤ 63 → v.val * 2 ^ (63 - bits.val) < 2 ^ 128 :=
    fun v hv h => by
      rw [bv]
      calc v.val * 2 ^ (63 - (L + 1)) < 2 ^ (L + 1) * 2 ^ (63 - (L + 1)) :=
            Nat.mul_lt_mul_of_pos_right (hv.trans_lt hhi) (by positivity)
        _ = 2 ^ 63 := by rw [← pow_add]; congr 1; omega
        _ < 2 ^ 128 := by norm_num
  refine WP.spec_bind (shift_to_spec a bits (by omega) (fit a (le_max_left _ _))) fun a' ha => ?_
  refine WP.spec_bind (shift_to_spec b bits (by omega) (fit b (le_max_right _ _))) fun b' hb' => ?_
  rw [WP.spec_ok]
  dsimp only
  rw [bv] at ha hb'
  have pa := shift63_props a.val _ L (le_max_left _ _) hlo hhi
  have pb := shift63_props b.val _ L (le_max_right _ _) hlo hhi
  dsimp only at pa pb
  rw [← ha] at pa
  rw [← hb'] at pb
  refine ⟨pa.1, pa.2.1, pb.1, pb.2.1, pa.2.2.1, pb.2.2.1, ?_⟩
  rcases le_total b.val a.val with hab | hab
  · exact (pa.2.2.2 (max_eq_left hab).symm).trans (le_max_left _ _)
  · exact (pb.2.2.2 (max_eq_right hab).symm).trans (le_max_right _ _)

/-- The angle of a point given by signs and magnitudes, `x`, `y ≥ 0`. -/
noncomputable def signedArg (xn : Bool) (x : ℝ) (yn : Bool) (y : ℝ) : ℝ :=
  Complex.arg ⟨if xn then -x else x, if yn then -y else y⟩

/-- `signedArg` is `roundTarget` of the angle of the magnitudes when a negative sign
comes with a positive magnitude. -/
theorem signedArg_eq (xn yn : Bool) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hxn : xn = true → 0 < x)
    (hyn : yn = true → 0 < y) : signedArg xn x yn y = roundTarget xn yn (Complex.arg ⟨x, y⟩) := by
  unfold signedArg roundTarget
  rw [arg_signs]
  have nx : ¬ x < 0 := not_lt.mpr hx
  have ny : ¬ y < 0 := not_lt.mpr hy
  cases xn <;> cases yn
  · simp only [Bool.false_eq_true, ↓reduceIte, abs_of_nonneg hx, abs_of_nonneg hy, nx, ny]
  · have := hyn rfl
    simp only [Bool.false_eq_true, ↓reduceIte, abs_neg, abs_of_nonneg hx, abs_of_nonneg hy, nx, neg_lt_zero, this]
  · have := hxn rfl
    simp only [Bool.false_eq_true, ↓reduceIte, abs_neg, abs_of_nonneg hx, abs_of_nonneg hy, ny, neg_lt_zero, this]
  · have h1 := hxn rfl
    have h2 := hyn rfl
    simp only [↓reduceIte, abs_neg, abs_of_nonneg hx, abs_of_nonneg hy, neg_lt_zero, h1, h2]

/-- L4 on the code: `trig::atan2_wide` of a sign and a magnitude each, a negative sign only
with a positive magnitude, `f ≤ 32`, never fails and is within `½ + 5 / 2^(62 - f)` of the
angle of the point times `2^f`; `0` at the origin. -/
theorem atan2_wide_spec (yn : Bool) (y : Std.U128) (xn : Bool) (x : Std.U128) (f : Std.U32) (hf : f.val ≤ 32)
    (hyn : yn = true → 0 < y.val) (hxn : xn = true → 0 < x.val) :
    fulcrum.trig.atan2_wide yn y xn x f ⦃ r =>
      |(r.val : ℝ) - signedArg xn x.val yn y.val * 2 ^ f.val| ≤ 1 / 2 + 5 / 2 ^ (62 - f.val) ⦄ := by
  have hyn' : yn = true → (0 : ℝ) < y.val := fun h => by exact_mod_cast hyn h
  have hxn' : xn = true → (0 : ℝ) < x.val := fun h => by exact_mod_cast hxn h
  have tail : 0 < y.val ∨ 0 < x.val → (do
      let (n, d) ← fulcrum.trig.to_63_bits y x
      let i ← fulcrum.trig.atan_ratio n d
      fulcrum.trig.round_angle i xn yn f) ⦃ r =>
        |(r.val : ℝ) - signedArg xn x.val yn y.val * 2 ^ f.val| ≤ 1 / 2 + 5 / 2 ^ (62 - f.val) ⦄ := by
    intro h0
    refine WP.spec_bind (to_63_bits_spec y x h0) fun p ⟨n1, n2, d1, d2, nl, dl, pm⟩ => ?_
    obtain ⟨n', d'⟩ := p
    dsimp only at n1 n2 d1 d2 nl dl pm ⊢
    have pos : 0 < n'.val ∨ 0 < d'.val := by
      rcases le_total n'.val d'.val with h | h
      · right; rw [max_eq_right h] at pm; exact lt_of_lt_of_le (by norm_num) pm
      · left; rw [max_eq_left h] at pm; exact lt_of_lt_of_le (by norm_num) pm
    refine WP.spec_bind (atan_ratio_spec n' d' (nl.le.trans (by norm_num)) (dl.le.trans (by norm_num)) pos)
      fun a ha => ?_
    set κ : ℝ := 2 ^ 62 / 2 ^ Nat.log 2 (max y.val x.val) with hκ
    have κ0 : 0 < κ := by positivity
    have e1 : (y.val : ℝ) * 2 ^ 62 / 2 ^ Nat.log 2 (max y.val x.val) = y.val * κ := by rw [hκ]; ring
    have e2 : (x.val : ℝ) * 2 ^ 62 / 2 ^ Nat.log 2 (max y.val x.val) = x.val * κ := by rw [hκ]; ring
    rw [e1] at n1 n2
    rw [e2] at d1 d2
    have M : (2 : ℝ) ^ 62 ≤ max (n'.val : ℝ) (d'.val : ℝ) := by
      rw [← Nat.cast_max]; exact_mod_cast pm
    have tr := arg_truncate n'.val d'.val (y.val * κ) (x.val * κ) (2 ^ 62) 1 (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      n1 n2.le d1 d2.le (by positivity) M (by norm_num)
    rw [arg_scale _ _ _ κ0] at tr
    have ⟨A0, A1⟩ := arg_quadrant (x.val : ℝ) (y.val : ℝ) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    have hA : |(a.val : ℝ) - Complex.arg ⟨(x.val : ℝ), (y.val : ℝ)⟩ * 2 ^ 62| ≤ 441 / 100 := by
      have d : |(Complex.arg ⟨(d'.val : ℝ), (n'.val : ℝ)⟩ - Complex.arg ⟨(x.val : ℝ), (y.val : ℝ)⟩) * 2 ^ 62| ≤ 101 / 100 := by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 62)]
        calc _ ≤ 101 / 100 * (1 / 2 ^ 62) * 2 ^ 62 := mul_le_mul_of_nonneg_right tr (by positivity)
          _ = 101 / 100 := by field_simp
      calc _ ≤ |(a.val : ℝ) - Complex.arg ⟨(d'.val : ℝ), (n'.val : ℝ)⟩ * 2 ^ 62| +
            |(Complex.arg ⟨(d'.val : ℝ), (n'.val : ℝ)⟩ - Complex.arg ⟨(x.val : ℝ), (y.val : ℝ)⟩) * 2 ^ 62| :=
            (abs_sub_le _ _ _).trans_eq (by rw [sub_mul])
        _ ≤ 34 / 10 + 101 / 100 := add_le_add ha d
        _ = 441 / 100 := by norm_num
    refine WP.spec_mono (round_angle_spec a xn yn f hf _ (441 / 100) A0 A1 (by norm_num) hA) fun r hr => ?_
    rw [signedArg_eq xn yn _ _ (Nat.cast_nonneg _) (Nat.cast_nonneg _) hxn' hyn']
    exact hr.trans (by gcongr; norm_num)
  unfold fulcrum.trig.atan2_wide
  have b : (0 : ℝ) ≤ 1 / 2 + 5 / 2 ^ (62 - f.val) := by positivity
  by_cases hy : y = 0#u128
  · have hy' : y.val = 0 := by rw [hy]; rfl
    have ynf : yn = false := by cases yn; rfl; exact absurd (hyn rfl) (by omega)
    rw [ite_eq_left hy]
    by_cases hx : x = 0#u128
    · have hx' : x.val = 0 := by rw [hx]; rfl
      have xnf : xn = false := by cases xn; rfl; exact absurd (hxn rfl) (by omega)
      rw [ite_eq_left hx, WP.spec_ok, signedArg, xnf, ynf, hx', hy']
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.cast_zero]
      rw [show (⟨0, 0⟩ : ℂ) = 0 from rfl, Complex.arg_zero]
      simpa using b
    · have hx' : x.val ≠ 0 := fun e => hx (UScalar.eq_of_val_eq (by rw [e]; rfl))
      rw [ite_eq_right hx]
      cases xn
      · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
        rw [signedArg, ynf, hy']
        simp only [Bool.false_eq_true, ↓reduceIte, Nat.cast_zero]
        rw [Complex.arg_eq_zero_iff.mpr ⟨Nat.cast_nonneg _, rfl⟩]
        simpa using b
      · simp only [↓reduceIte]
        exact tail (Or.inr (Nat.pos_of_ne_zero hx'))
  · have hy' : y.val ≠ 0 := fun e => hy (UScalar.eq_of_val_eq (by rw [e]; rfl))
    rw [ite_eq_right hy]
    exact tail (Or.inl (Nat.pos_of_ne_zero hy'))

/-- `i128::unsigned_abs` is `natAbs`. -/
theorem I128_unsigned_abs_spec (x : Std.I128) :
    core.num.I128.unsigned_abs x ⦃ u => u.val = x.val.natAbs ⦄ :=
  (WP.spec_ok _).mpr (toNat_abs_eq_natAbs x.bv)

/-- A number given as a sign and a magnitude. -/
def signedVal (neg : Bool) (m : ℕ) : ℤ := if neg then -(m : ℤ) else m

/-- The product of two `i64` values lies in `[-(2^126 - 2^63), 2^126]`. -/
theorem i64_product_bounds (a b : ℤ) (ha : -2 ^ 63 ≤ a) (ha' : a < 2 ^ 63) (hb : -2 ^ 63 ≤ b)
    (hb' : b < 2 ^ 63) : -(2 ^ 126 - 2 ^ 63) ≤ a * b ∧ a * b ≤ 2 ^ 126 := by
  constructor <;> nlinarith only [mul_nonneg (show (0 : ℤ) ≤ a + 2 ^ 63 by omega) (show (0 : ℤ) ≤ b + 2 ^ 63 by omega),
    mul_nonneg (show (0 : ℤ) ≤ 2 ^ 63 - 1 - a by omega) (show (0 : ℤ) ≤ 2 ^ 63 - 1 - b by omega),
    mul_nonneg (show (0 : ℤ) ≤ a + 2 ^ 63 by omega) (show (0 : ℤ) ≤ 2 ^ 63 - 1 - b by omega),
    mul_nonneg (show (0 : ℤ) ≤ 2 ^ 63 - 1 - a by omega) (show (0 : ℤ) ≤ b + 2 ^ 63 by omega)]

/-- L4 on the code: `trig::sum_parts(p, q)` with `|p|, |q| ≤ 2^126` never fails and is the sign
and the magnitude of `p + q`, the sign negative only with a positive magnitude. -/
theorem sum_parts_spec (p q : Std.I128) (hp : |p.val| ≤ 2 ^ 126) (hq : |q.val| ≤ 2 ^ 126) :
    fulcrum.trig.sum_parts p q ⦃ r => signedVal r.1 r.2.val = p.val + q.val ∧ (r.1 = true → 0 < r.2.val) ⦄ := by
  unfold fulcrum.trig.sum_parts
  rw [lift, bind_ok]
  have ⟨pl, pu⟩ := abs_le.mp hp
  have ⟨ql, qu⟩ := abs_le.mp hq
  have oe : core.num.I128.overflowing_add p q = (⟨p.bv + q.bv⟩, BitVec.saddOverflow p.bv q.bv) := by
    simp only [core.num.I128.overflowing_add, IScalar.overflowing_add]
  have sv : (core.num.I128.overflowing_add p q).1.val = Int.bmod (p.val + q.val) (2 ^ 128) := by
    rw [oe]
    show (p.bv + q.bv).toInt = _
    rw [BitVec.toInt_add]; rfl
  have ov : (core.num.I128.overflowing_add p q).2 = decide (2 ^ 127 ≤ p.val + q.val) := by
    rw [oe]
    show BitVec.saddOverflow p.bv q.bv = _
    unfold BitVec.saddOverflow
    have : ¬ (p.bv.toInt + q.bv.toInt < -2 ^ (128 - 1)) := by
      show ¬ (p.val + q.val < -2 ^ (128 - 1)); norm_num; omega
    simp only [this, decide_false, Bool.or_false]
    rfl
  generalize core.num.I128.overflowing_add p q = o at sv ov ⊢
  obtain ⟨sum, ovf⟩ := o
  dsimp only at sv ov
  change (if ovf = true then (do let i ← lift (IScalar.hcast .U128 sum); ok (false, i))
    else (do let i ← core.num.I128.unsigned_abs sum; ok (decide (sum < 0#i128), i))) ⦃ r =>
      signedVal r.1 r.2.val = p.val + q.val ∧ (r.1 = true → 0 < r.2.val) ⦄
  by_cases h : ovf = true
  · have e : p.val + q.val = 2 ^ 127 := by
      rw [h] at ov; have := of_decide_eq_true ov.symm; omega
    rw [ite_eq_left h, lift, bind_ok, WP.spec_ok]
    have sv' : sum.val = -2 ^ 127 := by rw [sv, e, Int.bmod_def]; norm_num
    refine ⟨?_, fun h => by simp at h⟩
    rw [signedVal, IScalar.hcast_val_eq, sv', UScalarTy.U128_numBits_eq, e]
    norm_num
  · have hf : ovf = false := by simpa using h
    have e : p.val + q.val < 2 ^ 127 := by
      rw [hf] at ov; have := of_decide_eq_false ov.symm; omega
    rw [ite_eq_right h]
    refine WP.spec_bind (I128_unsigned_abs_spec sum) fun i hi => ?_
    rw [WP.spec_ok]
    have sv' : sum.val = p.val + q.val := by
      rw [sv]; exact Int.bmod_eq_of_le (by push_cast; omega) (by push_cast; omega)
    have dn : decide (sum < 0#i128) = decide (sum.val < 0) := rfl
    dsimp only
    rw [dn, signedVal, hi, ← sv']
    constructor
    · by_cases hs : sum.val < 0
      · simp only [hs, decide_true, ↓reduceIte]; omega
      · simp only [hs, decide_false, Bool.false_eq_true, ↓reduceIte]; omega
    · intro hs; have := of_decide_eq_true hs; omega

/-- `signedArg` of a sign and a magnitude is the angle of the signed values. -/
theorem signedArg_signedVal (xn yn : Bool) (x y : ℕ) :
    signedArg xn x yn y = Complex.arg ⟨(signedVal xn x : ℝ), (signedVal yn y : ℝ)⟩ := by
  unfold signedArg signedVal
  cases xn <;> cases yn <;> simp

/-- L4 on the code: `trig::angle_between2(ax, ay, bx, by, f)` with `f ≤ 32` never fails and is
within `½ + 5 / 2^(62 - f)` of `arg (a · b + (a × b) i) · 2^f`, the signed angle from `a` to `b`. -/
theorem angle_between2_spec (ax ay bx by' : Std.I64) (f : Std.U32) (hf : f.val ≤ 32) :
    fulcrum.trig.angle_between2 ax ay bx by' f ⦃ r =>
      |(r.val : ℝ) - Complex.arg ⟨((ax.val * bx.val + ay.val * by'.val : ℤ) : ℝ),
        ((ax.val * by'.val - ay.val * bx.val : ℤ) : ℝ)⟩ * 2 ^ f.val| ≤ 1 / 2 + 5 / 2 ^ (62 - f.val) ⦄ := by
  unfold fulcrum.trig.angle_between2
  rw [lift, bind_ok, lift, bind_ok, lift, bind_ok, lift, bind_ok]
  have b := fun (x : Std.I64) => val_bounds x IScalarTy.I64_numBits_eq
  have ⟨axl, axu⟩ := b ax
  have ⟨ayl, ayu⟩ := b ay
  have ⟨bxl, bxu⟩ := b bx
  have ⟨byl, byu⟩ := b by'
  have mn : IScalar.min .I128 = -2 ^ 127 := min_eq_neg_pow IScalarTy.I128_numBits_eq
  have mx : IScalar.max .I128 = 2 ^ 127 - 1 := max_eq_pow_sub_one IScalarTy.I128_numBits_eq
  have p1 := i64_product_bounds _ _ axl axu byl byu
  have p2 := i64_product_bounds _ _ ayl ayu bxl bxu
  have p3 := i64_product_bounds _ _ axl axu bxl bxu
  have p4 := i64_product_bounds _ _ ayl ayu byl byu
  refine WP.spec_bind (IScalar.mul_spec (x := IScalar.cast .I128 ax) (y := IScalar.cast .I128 by')
    (by rw [cast_i128_val, cast_i128_val, mn]; omega) (by rw [cast_i128_val, cast_i128_val, mx]; omega))
    fun i hi => ?_
  refine WP.spec_bind (IScalar.mul_spec (x := IScalar.cast .I128 ay) (y := IScalar.cast .I128 bx)
    (by rw [cast_i128_val, cast_i128_val, mn]; omega) (by rw [cast_i128_val, cast_i128_val, mx]; omega))
    fun i1 hi1 => ?_
  rw [cast_i128_val, cast_i128_val] at hi hi1
  refine WP.spec_bind (IScalar.sub_spec (x := i) (y := i1) (by rw [hi, hi1, mn]; omega)
    (by rw [hi, hi1, mx]; omega)) fun cross hc => ?_
  refine WP.spec_bind (IScalar.mul_spec (x := IScalar.cast .I128 ax) (y := IScalar.cast .I128 bx)
    (by rw [cast_i128_val, cast_i128_val, mn]; omega) (by rw [cast_i128_val, cast_i128_val, mx]; omega))
    fun i2 hi2 => ?_
  refine WP.spec_bind (IScalar.mul_spec (x := IScalar.cast .I128 ay) (y := IScalar.cast .I128 by')
    (by rw [cast_i128_val, cast_i128_val, mn]; omega) (by rw [cast_i128_val, cast_i128_val, mx]; omega))
    fun i3 hi3 => ?_
  rw [cast_i128_val, cast_i128_val] at hi2 hi3
  refine WP.spec_bind (sum_parts_spec i2 i3 (by rw [hi2]; exact abs_le.mpr ⟨by omega, by omega⟩)
    (by rw [hi3]; exact abs_le.mpr ⟨by omega, by omega⟩)) fun pr ⟨hpv, hpn⟩ => ?_
  obtain ⟨dn, dot⟩ := pr
  dsimp only at hpv hpn ⊢
  refine WP.spec_bind (I128_unsigned_abs_spec cross) fun i4 h4 => ?_
  have dc : decide (cross < 0#i128) = decide (cross.val < 0) := rfl
  refine WP.spec_mono (atan2_wide_spec _ i4 dn dot f hf (fun h => by
    rw [dc] at h; rw [h4]; have := of_decide_eq_true h; omega) hpn) fun r hr => ?_
  rw [signedArg_signedVal] at hr
  have e1 : signedVal dn dot.val = ax.val * bx.val + ay.val * by'.val := by rw [hpv, hi2, hi3]
  have e2 : signedVal (decide (cross < 0#i128)) i4.val = ax.val * by'.val - ay.val * bx.val := by
    rw [dc, signedVal, h4]
    by_cases hs : cross.val < 0
    · simp only [hs, decide_true, ↓reduceIte]; omega
    · simp only [hs, decide_false, Bool.false_eq_true, ↓reduceIte]; omega
  rw [e1, e2] at hr
  exact hr

/-- L4 on the code: `trig::add_parts(a, b)` of two signs and magnitudes whose magnitudes
add within `u128` never fails and is their sum as a sign and a magnitude. -/
theorem add_parts_spec (a b : Bool × Std.U128) (h : a.2.val + b.2.val ≤ UScalar.max .U128) :
    fulcrum.trig.add_parts a b ⦃ r => signedVal r.1 r.2.val = signedVal a.1 a.2.val + signedVal b.1 b.2.val ⦄ := by
  obtain ⟨s1, m1⟩ := a
  obtain ⟨s2, m2⟩ := b
  dsimp only at h ⊢
  unfold fulcrum.trig.add_parts
  change (if s1 = s2 then (do let i2 ← m1 + m2; ok (s1, i2))
    else if m1 >= m2 then (do let i2 ← m1 - m2; ok (s1, i2)) else (do let i2 ← m2 - m1; ok (s2, i2))) ⦃ r =>
      signedVal r.1 r.2.val = signedVal s1 m1.val + signedVal s2 m2.val ⦄
  by_cases he : s1 = s2
  · rw [ite_eq_left he]
    refine WP.spec_bind (UScalar.add_spec (x := m1) (y := m2) h) fun r hr => ?_
    rw [WP.spec_ok]; dsimp only
    subst he
    unfold signedVal; rw [hr]; cases s1 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> push_cast <;> ring
  · rw [ite_eq_right he]
    by_cases hmn : m1 ≥ m2
    · have hmn' : m2.val ≤ m1.val := hmn
      rw [ite_eq_left hmn]
      refine WP.spec_bind (UScalar.sub_spec (x := m1) (y := m2) hmn') fun r ⟨hr, _⟩ => ?_
      rw [WP.spec_ok]; dsimp only
      unfold signedVal; rw [hr, Nat.cast_sub hmn']
      cases s1 <;> cases s2 <;> simp_all <;> ring
    · have hlt : m1.val < m2.val := Nat.lt_of_not_le hmn
      rw [ite_eq_right hmn]
      refine WP.spec_bind (UScalar.sub_spec (x := m2) (y := m1) hlt.le) fun r ⟨hr, _⟩ => ?_
      rw [WP.spec_ok]; dsimp only
      unfold signedVal; rw [hr, Nat.cast_sub hlt.le]
      cases s1 <;> cases s2 <;> simp_all <;> ring

/-- L4 on the code: the loop of `trig::angle_between3` is the largest of `m` and the
magnitudes of the three components of `c`. -/
theorem max_loop_spec (c0 c1 c2 : Std.I128) (m : Std.U128) :
    fulcrum.trig.angle_between3_loop (Array.make 3#usize [c0, c1, c2]) m 0#usize ⦃ r =>
      r.val = max (max (max m.val c0.val.natAbs) c1.val.natAbs) c2.val.natAbs ⦄ := by
  unfold fulcrum.trig.angle_between3_loop
  set c := Array.make 3#usize [c0, c1, c2]
  set g : ℕ → ℕ := fun i => if i = 0 then m.val else if i = 1 then max m.val c0.val.natAbs
    else if i = 2 then max (max m.val c0.val.natAbs) c1.val.natAbs
    else max (max (max m.val c0.val.natAbs) c1.val.natAbs) c2.val.natAbs with hg
  refine loop.spec_decr_nat (fun y => 3 - y.2.val) (fun y => y.2.val ≤ 3 ∧ y.1.val = g y.2.val) _ _ _ ?_
    ⟨by simp, by simp [hg]⟩
  rintro ⟨x, i⟩ ⟨hi, hx⟩
  dsimp only at hi hx ⊢
  unfold fulcrum.trig.angle_between3_loop.body
  by_cases h3 : i < 3#usize
  · have h3' : i.val < 3 := h3
    rw [ite_eq_left h3]
    have hl : i.val < c.length := by show i.val < 3; exact h3'
    refine WP.spec_bind (Array.index_usize_spec c i hl) fun v hv => ?_
    refine WP.spec_bind (I128_unsigned_abs_spec v) fun a ha => ?_
    refine WP.spec_bind (Pₘ := fun m1 : Std.U128 => m1.val = max x.val a.val) ?_ fun m1 hm1 => ?_
    · by_cases hgt : a > x
      · rw [ite_eq_left hgt]
        refine WP.spec_mono (I128_unsigned_abs_spec v) fun r hr => ?_
        rw [hr, ← ha, max_eq_right (show x.val ≤ a.val from le_of_lt hgt)]
      · rw [ite_eq_right hgt, WP.spec_ok, max_eq_left (show a.val ≤ x.val from not_lt.mp hgt)]
    refine WP.spec_bind (UScalar.add_spec (x := i) (y := 1#usize) (by
      have := usize_max_ge; rw [lit_val]; omega)) fun i3 hi3 => ?_
    rw [WP.spec_ok]
    dsimp only
    rw [lit_val] at hi3
    refine ⟨⟨by omega, ?_⟩, by omega⟩
    rw [hm1, hx, ha, hv, hi3]
    have : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
    rcases this with e | e | e <;> simp [hg, c, Array.make, e]
  · have h3' : ¬ i.val < 3 := h3
    rw [ite_eq_right h3, WP.spec_ok]
    dsimp only
    rw [hx, show i.val = 3 by omega]
    simp [hg]

/-- `arg (-x + y i) = π - arg (x + y i)` off the origin, `x, y ≥ 0`. -/
theorem arg_neg_re (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (h : 0 < x ∨ 0 < y) :
    Complex.arg ⟨-x, y⟩ = Real.pi - Complex.arg ⟨x, y⟩ := by
  rcases hx.lt_or_eq with hp | hz
  · rw [arg_signs, abs_neg, abs_of_nonneg hx, abs_of_nonneg hy, ite_eq_right (not_lt.mpr hy),
      ite_eq_left (neg_lt_zero.mpr hp), one_mul]
  · subst hz
    have hy' : 0 < y := h.resolve_left (lt_irrefl 0)
    rw [neg_zero, arg_compl 0 y le_rfl hy', zero_div, Real.arctan_zero]; ring

/-- `√((u κ)² + (v κ)² + (w κ)²) = κ √(u² + v² + w²)` for `κ ≥ 0`. -/
theorem sqrt3_scale (u v w κ : ℝ) (hκ : 0 ≤ κ) :
    √((u * κ) ^ 2 + (v * κ) ^ 2 + (w * κ) ^ 2) = √(u ^ 2 + v ^ 2 + w ^ 2) * κ := by
  rw [show (u * κ) ^ 2 + (v * κ) ^ 2 + (w * κ) ^ 2 = (u ^ 2 + v ^ 2 + w ^ 2) * κ ^ 2 by ring,
    Real.sqrt_mul (by positivity), Real.sqrt_sq hκ]

/-- L4 on the code: `trig::angle_between3(a, b, f)` with `f ≤ 32` never fails and is within
`½ + 8 / 2^(62 - f)` of `arg (a · b + |a × b| i) · 2^f`, the angle between `a` and `b`
in `[0, π]`; `0` when either is zero. -/
theorem angle_between3_spec (a b : Std.Array Std.I64 3#usize) (f : Std.U32) (hf : f.val ≤ 32) :
    fulcrum.trig.angle_between3 a b f ⦃ r =>
      |(r.val : ℝ) - Complex.arg ⟨(((a.val[0]!).val * (b.val[0]!).val + (a.val[1]!).val * (b.val[1]!).val +
          (a.val[2]!).val * (b.val[2]!).val : ℤ) : ℝ),
        √((((a.val[1]!).val * (b.val[2]!).val - (a.val[2]!).val * (b.val[1]!).val : ℤ) : ℝ) ^ 2 +
          (((a.val[2]!).val * (b.val[0]!).val - (a.val[0]!).val * (b.val[2]!).val : ℤ) : ℝ) ^ 2 +
          (((a.val[0]!).val * (b.val[1]!).val - (a.val[1]!).val * (b.val[0]!).val : ℤ) : ℝ) ^ 2)⟩ * 2 ^ f.val| ≤
        1 / 2 + 8 / 2 ^ (62 - f.val) ⦄ := by
  unfold fulcrum.trig.angle_between3
  refine WP.spec_bind (arr3_read a 0#usize 0 rfl (by norm_num)) fun x0 h0 => ?_
  rw [lift, bind_ok]
  refine WP.spec_bind (arr3_read a 1#usize 1 rfl (by norm_num)) fun x1 h1 => ?_
  rw [lift, bind_ok]
  refine WP.spec_bind (arr3_read a 2#usize 2 rfl (by norm_num)) fun x2 h2 => ?_
  rw [lift, bind_ok]
  refine WP.spec_bind (arr3_read b 0#usize 0 rfl (by norm_num)) fun y0 g0 => ?_
  rw [lift, bind_ok]
  refine WP.spec_bind (arr3_read b 1#usize 1 rfl (by norm_num)) fun y1 g1 => ?_
  rw [lift, bind_ok]
  refine WP.spec_bind (arr3_read b 2#usize 2 rfl (by norm_num)) fun y2 g2 => ?_
  rw [lift, bind_ok]
  have e0 : (IScalar.cast .I128 x0).val = (a.val[0]!).val := by rw [cast_i128_val, h0]
  have e1 : (IScalar.cast .I128 x1).val = (a.val[1]!).val := by rw [cast_i128_val, h1]
  have e2 : (IScalar.cast .I128 x2).val = (a.val[2]!).val := by rw [cast_i128_val, h2]
  have f0 : (IScalar.cast .I128 y0).val = (b.val[0]!).val := by rw [cast_i128_val, g0]
  have f1 : (IScalar.cast .I128 y1).val = (b.val[1]!).val := by rw [cast_i128_val, g1]
  have f2 : (IScalar.cast .I128 y2).val = (b.val[2]!).val := by rw [cast_i128_val, g2]
  have bd := fun (x : Std.I64) => val_bounds x IScalarTy.I64_numBits_eq
  have ⟨a0l, a0u⟩ := bd (a.val[0]!)
  have ⟨a1l, a1u⟩ := bd (a.val[1]!)
  have ⟨a2l, a2u⟩ := bd (a.val[2]!)
  have ⟨b0l, b0u⟩ := bd (b.val[0]!)
  have ⟨b1l, b1u⟩ := bd (b.val[1]!)
  have ⟨b2l, b2u⟩ := bd (b.val[2]!)
  have pr := fun (u v : ℤ) (hu : -2 ^ 63 ≤ u) (hu' : u < 2 ^ 63) (hv : -2 ^ 63 ≤ v) (hv' : v < 2 ^ 63) =>
    i64_product_bounds u v hu hu' hv hv'
  have mn : IScalar.min .I128 = -2 ^ 127 := min_eq_neg_pow IScalarTy.I128_numBits_eq
  have mx : IScalar.max .I128 = 2 ^ 127 - 1 := max_eq_pow_sub_one IScalarTy.I128_numBits_eq
  clear h0 h1 h2 g0 g1 g2
  generalize (a.val[0]!).val = A0 at *
  generalize (a.val[1]!).val = A1 at *
  generalize (a.val[2]!).val = A2 at *
  generalize (b.val[0]!).val = B0 at *
  generalize (b.val[1]!).val = B1 at *
  generalize (b.val[2]!).val = B2 at *
  generalize IScalar.cast .I128 x0 = a0 at e0 ⊢
  generalize IScalar.cast .I128 x1 = a1 at e1 ⊢
  generalize IScalar.cast .I128 x2 = a2 at e2 ⊢
  generalize IScalar.cast .I128 y0 = b0 at f0 ⊢
  generalize IScalar.cast .I128 y1 = b1 at f1 ⊢
  generalize IScalar.cast .I128 y2 = b2 at f2 ⊢
  have P := fun (u v : Std.I128) (U V : ℤ) (hu : u.val = U) (hv : v.val = V) (hU : -2 ^ 63 ≤ U) (hU' : U < 2 ^ 63)
      (hV : -2 ^ 63 ≤ V) (hV' : V < 2 ^ 63) =>
    IScalar.mul_spec (x := u) (y := v) (by rw [hu, hv, mn]; have := pr U V hU hU' hV hV'; (clear * - this; omega))
      (by rw [hu, hv, mx]; have := pr U V hU hU' hV hV'; (clear * - this; omega))
  have q12 := pr _ _ a1l a1u b2l b2u
  have q21 := pr _ _ a2l a2u b1l b1u
  have q20 := pr _ _ a2l a2u b0l b0u
  have q02 := pr _ _ a0l a0u b2l b2u
  have q01 := pr _ _ a0l a0u b1l b1u
  have q10 := pr _ _ a1l a1u b0l b0u
  have q00 := pr _ _ a0l a0u b0l b0u
  have q11 := pr _ _ a1l a1u b1l b1u
  have q22 := pr _ _ a2l a2u b2l b2u
  refine WP.spec_bind (P a1 b2 _ _ e1 f2 a1l a1u b2l b2u) fun i6 h6 => ?_
  refine WP.spec_bind (P a2 b1 _ _ e2 f1 a2l a2u b1l b1u) fun i7 h7 => ?_
  rw [e1, f2] at h6; rw [e2, f1] at h7
  refine WP.spec_bind (IScalar.sub_spec (x := i6) (y := i7) (by rw [h6, h7, mn]; (clear * - q12 q21 h6 h7; omega)) (by rw [h6, h7, mx]; (clear * - q12 q21 h6 h7; omega)))
    fun i8 h8 => ?_
  refine WP.spec_bind (P a2 b0 _ _ e2 f0 a2l a2u b0l b0u) fun i9 h9 => ?_
  refine WP.spec_bind (P a0 b2 _ _ e0 f2 a0l a0u b2l b2u) fun i10 h10 => ?_
  rw [e2, f0] at h9; rw [e0, f2] at h10
  refine WP.spec_bind (IScalar.sub_spec (x := i9) (y := i10) (by rw [h9, h10, mn]; (clear * - q20 q02 h9 h10; omega)) (by rw [h9, h10, mx]; (clear * - q20 q02 h9 h10; omega)))
    fun i11 h11 => ?_
  refine WP.spec_bind (P a0 b1 _ _ e0 f1 a0l a0u b1l b1u) fun i12 h12 => ?_
  refine WP.spec_bind (P a1 b0 _ _ e1 f0 a1l a1u b0l b0u) fun i13 h13 => ?_
  rw [e0, f1] at h12; rw [e1, f0] at h13
  refine WP.spec_bind (IScalar.sub_spec (x := i12) (y := i13) (by rw [h12, h13, mn]; (clear * - q01 q10 h12 h13; omega)) (by rw [h12, h13, mx]; (clear * - q01 q10 h12 h13; omega)))
    fun i14 h14 => ?_
  refine WP.spec_bind (P a2 b2 _ _ e2 f2 a2l a2u b2l b2u) fun p hp => ?_
  refine WP.spec_bind (P a0 b0 _ _ e0 f0 a0l a0u b0l b0u) fun i15 h15 => ?_
  refine WP.spec_bind (P a1 b1 _ _ e1 f1 a1l a1u b1l b1u) fun i16 h16 => ?_
  rw [e2, f2] at hp; rw [e0, f0] at h15; rw [e1, f1] at h16
  refine WP.spec_bind (sum_parts_spec i15 i16 (by rw [h15]; exact abs_le.mpr ⟨by (clear * - q00 h15; omega), by (clear * - q00 h15; omega)⟩)
    (by rw [h16]; exact abs_le.mpr ⟨by (clear * - q11 h16; omega), by (clear * - q11 h16; omega)⟩)) fun p1 ⟨hp1, hp1'⟩ => ?_
  refine WP.spec_bind (I128_unsigned_abs_spec p) fun i17 h17 => ?_
  have p1l : p1.2.val ≤ 2 ^ 127 := by
    have : (p1.2.val : ℤ) ≤ 2 ^ 127 := by
      have e := hp1; unfold signedVal at e; rw [h15, h16] at e
      split_ifs at e <;> (clear * - q00 q11 h15 h16 e; omega)
    exact_mod_cast this
  have i17l : i17.val ≤ 2 ^ 126 := by rw [h17]; (clear * - q22 hp; omega)
  refine WP.spec_bind (add_parts_spec p1 (decide (p < 0#i128), i17) (by
    rw [U128_max_val]; dsimp only; (clear * - h17 p1l i17l; omega))) fun pd hpd => ?_
  obtain ⟨dn, dot⟩ := pd
  dsimp only at hpd ⊢
  have pv : signedVal (decide (p < 0#i128)) i17.val = p.val := by
    have dc : decide (p < 0#i128) = decide (p.val < 0) := rfl
    rw [dc, signedVal, h17]
    by_cases hs : p.val < 0
    · simp only [hs, decide_true, ↓reduceIte]; (clear * - q22 hp hs; omega)
    · simp only [hs, decide_false, Bool.false_eq_true, ↓reduceIte]; (clear * - q22 hp hs; omega)
  rw [pv, hp1, h15, h16, hp] at hpd
  set D := A0 * B0 + A1 * B1 + A2 * B2 with hD
  have hpd' : signedVal dn dot.val = D := by rw [hpd]
  have dotv : (dot.val : ℤ) = |D| := by
    rw [← hpd']; unfold signedVal; split_ifs <;> simp
  set C0 := A1 * B2 - A2 * B1 with hC0
  set C1 := A2 * B0 - A0 * B2 with hC1
  set C2 := A0 * B1 - A1 * B0 with hC2
  have c0v : i8.val = C0 := by rw [h8, h6, h7]
  have c1v : i11.val = C1 := by rw [h11, h9, h10]
  have c2v : i14.val = C2 := by rw [h14, h12, h13]
  refine WP.spec_bind (max_loop_spec i8 i11 i14 dot) fun m hm => ?_
  rw [c0v, c1v, c2v] at hm
  set len := √((C0 : ℝ) ^ 2 + (C1 : ℝ) ^ 2 + (C2 : ℝ) ^ 2) with hlen
  have tgt_ok : Complex.arg ⟨(D : ℝ), len⟩ = roundTarget dn false (Complex.arg ⟨(dot.val : ℝ), len⟩) ∨
      (dot.val = 0 ∧ len = 0) := by
    by_cases hz : dot.val = 0 ∧ len = 0
    · exact Or.inr hz
    left
    have len0 : 0 ≤ len := Real.sqrt_nonneg _
    have pos : 0 < (dot.val : ℝ) ∨ 0 < len := by
      by_contra hc; push Not at hc
      exact hz ⟨by exact_mod_cast le_antisymm (by exact_mod_cast hc.1) (Nat.zero_le _), le_antisymm hc.2 len0⟩
    have Dr : (D : ℝ) = signedVal dn dot.val := by rw [hpd']
    unfold roundTarget
    rw [Dr]
    cases dn
    · simp [signedVal]
    · simp only [signedVal, ↓reduceIte, Int.cast_neg, Int.cast_natCast, Bool.false_eq_true, one_mul]
      exact arg_neg_re _ _ (Nat.cast_nonneg _) len0 pos
  by_cases hm0 : m = 0#u128
  · have m0 : m.val = 0 := by rw [hm0]; rfl
    rw [ite_eq_left hm0, WP.spec_ok]
    have d0 : dot.val = 0 := by omega
    have z0 : C0 = 0 ∧ C1 = 0 ∧ C2 = 0 := by omega
    have D0 : D = 0 := by have := dotv; rw [d0] at this; push_cast at this; exact abs_eq_zero.mp this.symm
    have l0 : len = 0 := by rw [hlen, z0.1, z0.2.1, z0.2.2]; simp
    rw [D0, l0, Int.cast_zero, show (⟨0, 0⟩ : ℂ) = 0 from rfl, Complex.arg_zero, zero_mul, sub_zero]
    show |(((0 : ℤ)) : ℝ)| ≤ _
    simp only [Int.cast_zero, abs_zero]
    positivity
  have m0 : m.val ≠ 0 := fun e => hm0 (UScalar.eq_of_val_eq (by rw [e]; rfl))
  rw [ite_eq_right hm0]
  have n128 : UScalarTy.U128.numBits = 128 := rfl
  set! L := Nat.log 2 m.val with hL
  have hlo : 2 ^ L ≤ m.val := Nat.pow_log_le_self 2 m0
  have hhi : m.val < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two _
  have Lle : L ≤ 127 := Nat.le_of_lt_succ ((Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp (hlo.trans_lt m.bv.isLt))
  have hlz : (core.num.U128.leading_zeros m).val = 128 - L - 1 :=
    leading_zeros_val m m0 (Nat.le_of_ble_eq_true rfl)
  rw [lift, bind_ok]
  refine WP.spec_bind (UScalar.sub_spec (x := 128#u32) (y := core.num.U128.leading_zeros m)
    (by rw [hlz, lit_val]; (clear * - Lle; omega))) fun bits ⟨hb, hb'⟩ => ?_
  rw [hlz, lit_val] at hb
  have bv : bits.val = L + 1 := by (clear * - Lle hlz hb; omega)
  have fit : ∀ v : Std.U128, v.val ≤ m.val → bits.val ≤ 63 → v.val * 2 ^ (63 - bits.val) < 2 ^ 128 :=
    fun v hv h => by
      rw [bv]
      calc v.val * 2 ^ (63 - (L + 1)) < 2 ^ (L + 1) * 2 ^ (63 - (L + 1)) :=
            Nat.mul_lt_mul_of_pos_right (hv.trans_lt hhi) (by positivity)
        _ = 2 ^ 63 := by rw [← pow_add]; congr 1; (clear * - Lle hb bv h; omega)
        _ < 2 ^ 128 := by norm_num
  have mC0 : C0.natAbs ≤ m.val := by rw [hm]; (clear * - dotv hm m0 Lle hlz hb bv; omega)
  have mC1 : C1.natAbs ≤ m.val := by rw [hm]; (clear * - hm m0 Lle hlz hb bv; omega)
  have mC2 : C2.natAbs ≤ m.val := by rw [hm]; (clear * - hm m0 Lle hlz hb bv; omega)
  have mD : dot.val ≤ m.val := by rw [hm]; omega
  have rd : ∀ (k : ℕ) (i : Std.Usize) (v : Std.I128), i.val = k → k < 3 →
      [i8, i11, i14][k]! = v → Array.index_usize (Array.make 3#usize [i8, i11, i14]) i ⦃ x => x = v ⦄ :=
    fun k i v hi hk hv => by
      have hl : i.val < (Array.make 3#usize [i8, i11, i14]).length := by
        show i.val < 3; (clear * - hi hk; omega)
      refine WP.spec_mono (Array.index_usize_spec _ i hl) fun x hx => ?_
      rw [hx, ← hv, getElem!_pos _ k (by show k < 3; exact hk)]
      simp only [Array.make, hi]
      rfl
  refine WP.spec_bind (rd 0 0#usize i8 rfl (by norm_num) rfl) fun v0 hv0 => ?_
  refine WP.spec_bind (I128_unsigned_abs_spec v0) fun u0 hu0 => ?_
  rw [hv0, c0v] at hu0
  refine WP.spec_bind (shift_to_spec u0 bits (by (clear * - Lle hb bv; omega)) (fit u0 (hu0 ▸ mC0))) fun c0' hc0' => ?_
  refine WP.spec_bind (rd 1 1#usize i11 rfl (by norm_num) rfl) fun v1 hv1 => ?_
  refine WP.spec_bind (I128_unsigned_abs_spec v1) fun u1 hu1 => ?_
  rw [hv1, c1v] at hu1
  refine WP.spec_bind (shift_to_spec u1 bits (by (clear * - Lle hb bv; omega)) (fit u1 (hu1 ▸ mC1))) fun c1' hc1' => ?_
  refine WP.spec_bind (rd 2 2#usize i14 rfl (by norm_num) rfl) fun v2 hv2 => ?_
  refine WP.spec_bind (I128_unsigned_abs_spec v2) fun u2 hu2 => ?_
  rw [hv2, c2v] at hu2
  refine WP.spec_bind (shift_to_spec u2 bits (by (clear * - Lle hb bv; omega)) (fit u2 (hu2 ▸ mC2))) fun c2' hc2' => ?_
  rw [bv] at hc0' hc1' hc2'
  have s0 := shift63_props u0.val m.val L (hu0 ▸ mC0) hlo hhi
  have s1 := shift63_props u1.val m.val L (hu1 ▸ mC1) hlo hhi
  have s2 := shift63_props u2.val m.val L (hu2 ▸ mC2) hlo hhi
  have sd := shift63_props dot.val m.val L mD hlo hhi
  dsimp only at s0 s1 s2 sd
  rw [← hc0'] at s0
  rw [← hc1'] at s1
  rw [← hc2'] at s2
  have sq : ∀ v : Std.U128, v.val < 2 ^ 63 → v.val * v.val < 2 ^ 126 := fun v hv => by
    calc v.val * v.val < 2 ^ 63 * 2 ^ 63 := Nat.mul_lt_mul'' hv hv
      _ = 2 ^ 126 := by norm_num
  have q0 := sq c0' s0.2.2.1
  have q1 := sq c1' s1.2.2.1
  have q2 := sq c2' s2.2.2.1
  have u128 : UScalar.max .U128 = 2 ^ 128 - 1 := U128_max_val
  refine WP.spec_bind (UScalar.mul_spec (x := c0') (y := c0') (by rw [u128]; (clear * - q0; omega))) fun i25 h25 => ?_
  refine WP.spec_bind (UScalar.mul_spec (x := c1') (y := c1') (by rw [u128]; (clear * - q1; omega))) fun i26 h26 => ?_
  refine WP.spec_bind (UScalar.add_spec (x := i25) (y := i26) (by rw [u128, h25, h26]; (clear * - q0 q1 h25 h26; omega))) fun i27 h27 => ?_
  refine WP.spec_bind (UScalar.mul_spec (x := c2') (y := c2') (by rw [u128]; (clear * - q2; omega))) fun i28 h28 => ?_
  refine WP.spec_bind (UScalar.add_spec (x := i27) (y := i28) (by rw [u128, h27, h25, h26, h28]; (clear * - q0 q1 q2 h25 h26 h27 h28; omega)))
    fun i29 h29 => ?_
  rw [h27, h25, h26, h28] at h29
  refine WP.spec_bind (k64_isqrt_spec i29 (by rw [h29]; (clear * - q0 q1 q2 h25 h26 h27 h28 h29; omega))) fun n hn => ?_
  rw [h29] at hn
  refine WP.spec_bind (shift_to_spec dot bits (by (clear * - Lle hb bv; omega)) (fit dot mD)) fun d' hd' => ?_
  rw [bv] at hd'
  rw [← hd'] at sd
  have nc : ∀ c : Std.U128, c = c0' ∨ c = c1' ∨ c = c2' → c.val ≤ n.val := fun c hc => by
    rw [hn]; apply Nat.le_sqrt.mpr
    rcases hc with rfl | rfl | rfl <;> (clear * - q1 q2 h26 h27 h28 h25 h29 q0; omega)
  have big : 2 ^ 62 ≤ max n.val d'.val := by
    have : m.val = dot.val ∨ m.val = C0.natAbs ∨ m.val = C1.natAbs ∨ m.val = C2.natAbs := by
      rw [hm]
      rcases max_choice (max (max dot.val C0.natAbs) C1.natAbs) C2.natAbs with e | e <;> rw [e]
      · rcases max_choice (max dot.val C0.natAbs) C1.natAbs with e' | e' <;> rw [e']
        · rcases max_choice dot.val C0.natAbs with e'' | e'' <;> rw [e''] <;> simp
        · simp
      · simp
    rcases this with e | e | e | e
    · exact (sd.2.2.2 e.symm).trans (le_max_right _ _)
    · exact ((s0.2.2.2 (by rw [hu0]; exact e.symm)).trans (nc c0' (Or.inl rfl))).trans (le_max_left _ _)
    · exact ((s1.2.2.2 (by rw [hu1]; exact e.symm)).trans (nc c1' (Or.inr (Or.inl rfl)))).trans (le_max_left _ _)
    · exact ((s2.2.2.2 (by rw [hu2]; exact e.symm)).trans (nc c2' (Or.inr (Or.inr rfl)))).trans (le_max_left _ _)
  have npos : 0 < n.val ∨ 0 < d'.val := by
    rcases le_total n.val d'.val with h | h
    · right; rw [max_eq_right h] at big; (clear * - sd hd' big; omega)
    · left; rw [max_eq_left h] at big; (clear * - hn big; omega)
  refine WP.spec_bind (to_63_bits_spec n d' npos) fun pr ⟨n1l, n1u, d1l, d1u, n1b, d1b, pm⟩ => ?_
  obtain ⟨n1, d1⟩ := pr
  dsimp only at n1l n1u d1l d1u n1b d1b pm ⊢
  have pos1 : 0 < n1.val ∨ 0 < d1.val := by
    rcases le_total n1.val d1.val with h | h
    · right; rw [max_eq_right h] at pm; (clear * - d1b pm; omega)
    · left; rw [max_eq_left h] at pm; (clear * - n1b pm; omega)
  refine WP.spec_bind (atan_ratio_spec n1 d1 (by (clear * - n1b; omega)) (by (clear * - d1b; omega)) pos1) fun a' ha' => ?_
  set κ : ℝ := 2 ^ 62 / 2 ^ L with hκ
  have κ0 : 0 < κ := by positivity
  set! κ2 : ℝ := 2 ^ 62 / 2 ^ Nat.log 2 (max n.val d'.val) with hκ2
  have κ20 : 0 < κ2 := by positivity
  have r2 : ∀ x : ℕ, (x : ℝ) * 2 ^ 62 / 2 ^ Nat.log 2 (max n.val d'.val) = x * κ2 := fun x => by rw [hκ2]; ring
  rw [r2] at n1l n1u d1l d1u
  have r1 : ∀ x : ℕ, (x : ℝ) * 2 ^ 62 / 2 ^ L = x * κ := fun x => by rw [hκ]; ring
  rw [r1] at s0 s1 s2 sd
  have X : ∀ (C : ℤ) (u : Std.U128), u.val = C.natAbs → ((u.val : ℝ) * κ) ^ 2 = ((C : ℝ) * κ) ^ 2 := fun C u hu => by
    rw [hu, mul_pow, mul_pow, Nat.cast_natAbs, Int.cast_abs, sq_abs]
  have rl := root_length_near (u0.val * κ) (u1.val * κ) (u2.val * κ) c0'.val c1'.val c2'.val s0.1 s0.2.1 s1.1 s1.2.1 s2.1 s2.2.1
  rw [X C0 u0 hu0, X C1 u1 hu1, X C2 u2 hu2, sqrt3_scale _ _ _ _ κ0.le, ← hlen, ← hn] at rl
  have hA := arg_two_truncations a'.val n1.val d1.val n.val d'.val dot.val len κ κ2 (Nat.cast_nonneg _)
    (Real.sqrt_nonneg _) κ0 κ20 n1l n1u d1l d1u (by rw [← Nat.cast_max]; exact_mod_cast pm) rl.1
    (by linarith only [rl.2]) sd.1 (by linarith only [sd.2.1]) (by rw [← Nat.cast_max]; exact_mod_cast big) ha'
  have ⟨A0', A1'⟩ := arg_quadrant (dot.val : ℝ) len (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
  refine WP.spec_mono (round_angle_spec a' dn false f hf _ (718 / 100) A0' A1' (by norm_num) hA) fun r hr => ?_
  rcases tgt_ok with e | ⟨d0, l0⟩
  · rw [e]
    exact hr.trans (by gcongr; norm_num)
  · exfalso
    rw [hlen] at l0
    have ⟨z0, z1, z2⟩ := sqrt3_eq_zero C0 C1 C2 l0
    apply m0; rw [hm, d0, z0, z1, z2]; rfl

end Fulcrum

end
