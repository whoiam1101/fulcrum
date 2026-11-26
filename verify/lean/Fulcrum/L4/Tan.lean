module

public import Fulcrum.L4.Radians
public import Fulcrum.Spec
import Fulcrum.L1.ShrRound
import Fulcrum.L4.SinQuarter
import Fulcrum.Lemmas.Int
import Fulcrum.Lemmas.Scalar
import Fulcrum.Math.Cot
import Fulcrum.Math.Round
import Fulcrum.Tables.Trig
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Pi.Irrational

/-!
# L4: `trig::tan` and `frac_2_pi_div` (INTERNALS §3.12)

On the code extracted by Aeneas, with `f ≤ 32`. `frac_2_pi_div(d)` is `⌊C / d⌋` for
`2^64 ≤ d < 2^118` (`frac_2_pi_div_spec`): the top 128 bits by one division,
then the low word of `C` a byte at a time (`longT`, `long_step`).

`tan` takes the quadrant `q` and the 128-bit fraction of `reduce`, the angle
being `j · π/2 + (fr + ε) · π / 2^129` with `|ε| ≤ 3/2` (`angle_split`).

- Away from a pole (`tan_far_case`): at the position `t` the denominator
  position is at least `2^52` (`tanDen_far`), the sines of the quarter are within
  `6.1`, the quotient within `8 · 10^-13` (`tan_quotient_near`) and rounded once
  (`round_quot`); the angle of `t` is within `1.71 · 10^-19` of `raw / 2^f` and
  `|cos| ≥ 7.07 · 10^15 / 2^62`, so the tangents differ by below `8 · 10^-14`
  (`far_ok`).
- Near a pole, `D = d ≥ 2^(126 - f)`: `cotN D` is within `512` units of `2^-64`
  of `cot θ`, `θ = (D ± ε) · π / 2^129`, by `1/θ - θ/3 - θ³/45` (`cot_near`),
  `⌊C / D⌋` and the floors of `θ` and `θ³` (`cotN_near`).
- Closer, `D < 2^(126 - f)`: `|tan| ≥ 2^(f+1)`, beyond `MAX` of every type with `f`
  fractional bits, and `tan` returns `±2^(2f)` (`sat_ok`); `raw / 2^f` is never on a
  pole, since `π` is irrational. The sign of the mark is not proven: within
  `3/2 · 2^-128` quarter turns of a pole, `ε` may put the exact angle on the
  other side.

`tan_spec`: never fails, and `tanOk` — within `½ + 2^f / 10^12` of `tan · 2^f`,
or the mark of saturation.
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace Fulcrum

set_option maxRecDepth 100000

/-- The word `j` of `tables::trig::FRAC_2_PI`, the most significant first. -/
@[irreducible] def fracWord (j : ℕ) : ℕ := (fulcrum.tables.trig.FRAC_2_PI.val[j]!).val

theorem fracWord_lt (j : ℕ) : fracWord j < 2 ^ 64 := by
  unfold fracWord; exact (fulcrum.tables.trig.FRAC_2_PI.val[j]!).bv.isLt

/-- The dividend of `trig::frac_2_pi_div` after `k` bytes of the low word: the
top two words and the first `k` bytes of the third. -/
def longT (k : ℕ) : ℕ := (fracWord 0 * 2 ^ 64 + fracWord 1) * 2 ^ (8 * k) + fracWord 2 / 2 ^ (64 - 8 * k)

theorem longT_zero : longT 0 = fracWord 0 * 2 ^ 64 + fracWord 1 := by
  rw [longT, Nat.div_eq_of_lt (fracWord_lt 2), mul_zero, pow_zero, mul_one, add_zero]

theorem frac2PiN_words : frac2PiN = fracWord 0 * 2 ^ 128 + fracWord 1 * 2 ^ 64 + fracWord 2 := by
  unfold fracWord frac2PiN; rfl

theorem longT_eight : longT 8 = frac2PiN := by
  rw [longT, frac2PiN_words, show 64 - 8 * 8 = 0 from rfl, pow_zero, Nat.div_one]; ring

theorem shift_byte (W P b : ℕ) : W * (P * 2 ^ 8) + b = (W * P + b / 2 ^ 8) * 2 ^ 8 + b % 2 ^ 8 := by
  have := Nat.div_add_mod' b (2 ^ 8); rw [add_mul, ← mul_assoc]; omega

theorem longT_succ (k : ℕ) (hk : k < 8) :
    longT (k + 1) = longT k * 2 ^ 8 + fracWord 2 / 2 ^ (56 - 8 * k) % 2 ^ 8 := by
  have e : fracWord 2 / 2 ^ (64 - 8 * k) = fracWord 2 / 2 ^ (56 - 8 * k) / 2 ^ 8 := by
    rw [Nat.div_div_eq_div_mul, ← pow_add]; congr 2; omega
  rw [longT, longT, e, show 64 - 8 * (k + 1) = 56 - 8 * k by omega, show 8 * (k + 1) = 8 * k + 8 by ring,
    pow_add]
  exact shift_byte _ _ _

theorem words_succ_le (a b : ℕ) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : a * 2 ^ 64 + b + 1 ≤ 2 ^ 128 := by
  calc a * 2 ^ 64 + b + 1 ≤ a * 2 ^ 64 + 2 ^ 64 := by rw [add_assoc]; exact Nat.add_le_add_left hb _
    _ = (a + 1) * 2 ^ 64 := by ring
    _ ≤ 2 ^ 64 * 2 ^ 64 := Nat.mul_le_mul_right _ ha
    _ = 2 ^ 128 := by rw [← pow_add]

theorem longT_lt (k : ℕ) : longT k < 2 ^ (128 + 8 * k) := by
  have h2 : fracWord 2 / 2 ^ (64 - 8 * k) < 2 ^ (8 * k) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add]
    exact (fracWord_lt 2).trans_le (Nat.pow_le_pow_right two_pos (by omega))
  calc longT k < (fracWord 0 * 2 ^ 64 + fracWord 1) * 2 ^ (8 * k) + 2 ^ (8 * k) := by
        rw [longT]; exact Nat.add_lt_add_left h2 _
    _ = (fracWord 0 * 2 ^ 64 + fracWord 1 + 1) * 2 ^ (8 * k) := by ring
    _ ≤ 2 ^ 128 * 2 ^ (8 * k) := Nat.mul_le_mul_right _ (words_succ_le _ _ (fracWord_lt 0) (fracWord_lt 1))
    _ = 2 ^ (128 + 8 * k) := by rw [pow_add]

/-- One step of long division by `d`: with `L = d · q + r`, the next dividend
`L · 2^8 + y` has quotient `q · 2^8 + ⌊(r · 2^8 + y) / d⌋` and remainder
`(r · 2^8 + y) mod d`. -/
theorem long_step (L d y : ℕ) :
    (L * 2 ^ 8 + y) / d = L / d * 2 ^ 8 + (L % d * 2 ^ 8 + y) / d ∧
      (L * 2 ^ 8 + y) % d = (L % d * 2 ^ 8 + y) % d := by
  have e : L * 2 ^ 8 + y = L % d * 2 ^ 8 + y + d * (L / d * 2 ^ 8) := by
    conv_lhs => rw [← Nat.mod_add_div L d]
    ring
  rcases Nat.eq_zero_or_pos d with h | h
  · subst h; simp
  rw [e, Nat.add_mul_div_left _ _ h, Nat.add_mul_mod_self_left]
  exact ⟨add_comm _ _, rfl⟩

theorem i32_min_val : IScalar.min .I32 = -2 ^ 31 := min_eq_neg_pow IScalarTy.I32_numBits_eq
theorem i32_max_val : IScalar.max .I32 = 2 ^ 31 - 1 := max_eq_pow_sub_one IScalarTy.I32_numBits_eq

/-- The loop of `trig::frac_2_pi_div` from byte `k ≤ 8` with the quotient and the
remainder of `longT k` by `d`, `2^64 ≤ d < 2^118`, ends with `⌊C / d⌋`. -/
theorem frac_2_pi_div_loop_spec (d q r : Std.U128) (i : Std.I32) (k : ℕ) (hk : k ≤ 8) (hi : i.val = k)
    (hd1 : 2 ^ 64 ≤ d.val) (hd2 : d.val < 2 ^ 118) (hq : q.val = longT k / d.val)
    (hr : r.val = longT k % d.val) :
    fulcrum.trig.frac_2_pi_div_loop d q r i ⦃ x => x.val = frac2PiN / d.val ⦄ := by
  unfold fulcrum.trig.frac_2_pi_div_loop
  have dpos : 0 < d.val := (Nat.two_pow_pos 64).trans_le hd1
  have n128 : UScalarTy.U128.numBits = 128 := rfl
  refine loop.spec_decr_nat (fun x : Std.U128 × Std.U128 × Std.I32 => (8 - x.2.2.val).toNat)
    (fun x => ∃ k : ℕ, k ≤ 8 ∧ x.2.2.val = (k : ℤ) ∧ x.1.val = longT k / d.val ∧ x.2.1.val = longT k % d.val)
    _ _ _ ?_ ⟨k, hk, hi, hq, hr⟩
  rintro ⟨q, r, i⟩ ⟨k, hk, hi, hq, hr⟩
  dsimp only at hi hq hr ⊢
  unfold fulcrum.trig.frac_2_pi_div_loop.body
  by_cases h8 : i < 8#i32
  · have h8' : k < 8 := by
      have : i.val < 8 := h8
      omega
    rw [ite_eq_left h8]
    have rl : r.val < 2 ^ 118 := (hr ▸ Nat.mod_lt _ dpos).trans hd2
    refine WP.spec_bind (shl_i32_spec r 8#i32 8 rfl (by rw [n128]; norm_num)
      (by rw [n128]; calc r.val * 2 ^ 8 < 2 ^ 118 * 2 ^ 8 := Nat.mul_lt_mul_of_pos_right rl (by positivity)
            _ ≤ 2 ^ 128 := by norm_num)) fun i1 h1 => ?_
    refine WP.spec_bind (frac_2_pi_word_spec 2#usize (by decide)) fun c2 hc2 => ?_
    have hc2' : c2.val = fracWord 2 := by rw [hc2]; unfold fracWord; rfl
    refine WP.spec_bind (IScalar.mul_spec (x := 8#i32) (y := i)
      (by rw [i32_min_val, hi]; norm_num; omega) (by rw [i32_max_val, hi]; norm_num; omega)) fun i3 h3 => ?_
    have e8 : ((8#i32 : Std.I32).val) = 8 := rfl
    rw [e8, hi] at h3
    refine WP.spec_bind (IScalar.sub_spec (x := 56#i32) (y := i3)
      (by rw [i32_min_val, h3]; norm_num; omega) (by rw [i32_max_val, h3]; norm_num; omega)) fun i4 h4 => ?_
    have e56 : ((56#i32 : Std.I32).val) = 56 := rfl
    rw [e56, h3] at h4
    have h4' : i4.val = ((56 - 8 * k : ℕ) : ℤ) := by rw [h4]; omega
    refine WP.spec_bind (shr_i32_spec c2 i4 (56 - 8 * k) h4' (by rw [UScalarTy.U64_numBits_eq]; omega))
      fun i5 h5 => ?_
    rw [lift, bind_ok, lift, bind_ok, lift, bind_ok]
    set y := fracWord 2 / 2 ^ (56 - 8 * k) % 2 ^ 8 with hy
    have yl : y < 2 ^ 8 := Nat.mod_lt _ (by positivity)
    have yv : (UScalar.cast .U128 (i5 &&& 255#u64)).val = y := by
      rw [cast_u128_val, UScalar.val_and, h5, hc2', lit_val, show (255 : ℕ) = 2 ^ 8 - 1 from rfl,
        Nat.and_two_pow_sub_one_eq_mod]
    have r1v : (i1 ||| UScalar.cast .U128 (i5 &&& 255#u64)).val = r.val * 2 ^ 8 + y := by
      rw [UScalar.val_or, yv, h1, mul_comm, Nat.two_pow_add_eq_or_of_lt yl]
    generalize i1 ||| UScalar.cast .U128 (i5 &&& 255#u64) = r1 at r1v ⊢
    have ql : q.val < 2 ^ 120 := by
      rw [hq, Nat.div_lt_iff_lt_mul dpos]
      calc longT k < 2 ^ (128 + 8 * k) := longT_lt k
        _ ≤ 2 ^ 184 := Nat.pow_le_pow_right two_pos (by omega)
        _ = 2 ^ 120 * 2 ^ 64 := by norm_num
        _ ≤ 2 ^ 120 * d.val := Nat.mul_le_mul_left _ hd1
    refine WP.spec_bind (shl_i32_spec q 8#i32 8 rfl (by rw [n128]; norm_num)
      (by rw [n128]; calc q.val * 2 ^ 8 < 2 ^ 120 * 2 ^ 8 := Nat.mul_lt_mul_of_pos_right ql (by positivity)
            _ ≤ 2 ^ 128 := by norm_num)) fun i8 h8q => ?_
    obtain ⟨i9, e9, h9⟩ := UScalar.div_spec r1 (y := d) dpos.ne'
    rw [e9, bind_ok, lift, bind_ok]
    have r1l : r1.val < d.val * 2 ^ 8 := by
      rw [r1v]
      have : r.val < d.val := hr ▸ Nat.mod_lt _ dpos
      calc r.val * 2 ^ 8 + y < r.val * 2 ^ 8 + 2 ^ 8 := by omega
        _ = (r.val + 1) * 2 ^ 8 := by ring
        _ ≤ d.val * 2 ^ 8 := Nat.mul_le_mul_right _ this
    have i9l : i9.val < 2 ^ 8 := by rw [h9, Nat.div_lt_iff_lt_mul dpos, mul_comm]; exact r1l
    refine WP.spec_bind (UScalar.rem_spec r1 (y := d) dpos.ne') fun r2 h2 => ?_
    refine WP.spec_bind (IScalar.add_spec (x := i) (y := 1#i32)
      (by rw [i32_min_val, hi]; norm_num; omega) (by rw [i32_max_val, hi]; norm_num; omega)) fun i10 h10 => ?_
    have e1 : ((1#i32 : Std.I32).val) = 1 := rfl
    rw [e1] at h10
    rw [WP.spec_ok]
    have ⟨sq, sr⟩ := long_step (longT k) d.val y
    rw [← longT_succ k h8'] at sq sr
    refine ⟨⟨k + 1, by omega, ?_, ?_, ?_⟩, ?_⟩
    · rw [h10, hi]; push_cast; rfl
    · dsimp only
      rw [UScalar.val_or, h8q, h9, r1v, mul_comm q.val, ← Nat.two_pow_add_eq_or_of_lt (by rw [← r1v, ← h9]; exact i9l), sq,
        ← hq, ← hr, mul_comm]
    · dsimp only
      rw [h2, r1v, sr, ← hr]
    · dsimp only
      rw [h10, hi]; omega
  · have h8' : k = 8 := by
      have : ¬ i.val < 8 := h8
      omega
    rw [ite_eq_right h8, WP.spec_ok]
    dsimp only
    rw [hq, h8', longT_eight]

/-- On the code: `trig::frac_2_pi_div(d)` with `2^64 ≤ d < 2^118` never fails and
returns `⌊C / d⌋` of the 192 bits `C` of `2/π`. -/
theorem frac_2_pi_div_spec (d : Std.U128) (hd1 : 2 ^ 64 ≤ d.val) (hd2 : d.val < 2 ^ 118) :
    fulcrum.trig.frac_2_pi_div d ⦃ x => x.val = frac2PiN / d.val ⦄ := by
  unfold fulcrum.trig.frac_2_pi_div
  have dpos : 0 < d.val := (Nat.two_pow_pos 64).trans_le hd1
  have n128 : UScalarTy.U128.numBits = 128 := rfl
  refine WP.spec_bind (frac_2_pi_word_spec 0#usize (by decide)) fun c0 hc0 => ?_
  have hc0' : c0.val = fracWord 0 := by rw [hc0]; unfold fracWord; rfl
  rw [lift, bind_ok]
  refine WP.spec_bind (shl_i32_spec (UScalar.cast .U128 c0) 64#i32 64 rfl (by rw [n128]; norm_num)
    (by rw [n128, cast_u128_val]
        calc c0.val * 2 ^ 64 < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul_of_pos_right c0.bv.isLt (by positivity)
          _ = 2 ^ 128 := by norm_num)) fun i2 h2 => ?_
  refine WP.spec_bind (frac_2_pi_word_spec 1#usize (by decide)) fun c1 hc1 => ?_
  have hc1' : c1.val = fracWord 1 := by rw [hc1]; unfold fracWord; rfl
  rw [lift, bind_ok, lift, bind_ok]
  have tv : (i2 ||| UScalar.cast .U128 c1).val = longT 0 := by
    rw [UScalar.val_or, h2, cast_u128_val, cast_u128_val, hc0', hc1', longT_zero, mul_comm,
      Nat.two_pow_add_eq_or_of_lt (fracWord_lt 1)]
  generalize i2 ||| UScalar.cast .U128 c1 = top at tv ⊢
  obtain ⟨q, eq, hq⟩ := UScalar.div_spec top (y := d) dpos.ne'
  rw [eq, bind_ok]
  refine WP.spec_bind (UScalar.rem_spec top (y := d) dpos.ne') fun r hr => ?_
  exact frac_2_pi_div_loop_spec d q r 0#i32 0 (by norm_num) rfl hd1 hd2 (by rw [hq, tv]) (by rw [hr, tv])

/-- The sine of `e / 2^62` of a quarter turn, `2^52 ≤ e ≤ 2^62`, is at least
`7.07 · 10^15` units of `2^-62`: the denominator of `trig::tan` away from a pole. -/
theorem quarter_sin_lower (e : ℝ) (h1 : 2 ^ 52 ≤ e) (h2 : e ≤ 2 ^ 62) :
    7070 * 10 ^ 12 ≤ Real.sin (e / 2 ^ 62 * (Real.pi / 2)) * 2 ^ 62 := by
  have p1 := Real.pi_gt_d2
  have p2 := Real.pi_lt_d2
  have hy : Real.pi / 2 ^ 11 ≤ e / 2 ^ 62 * (Real.pi / 2) := by
    have : Real.pi / 2 ^ 11 = 2 ^ 52 / 2 ^ 62 * (Real.pi / 2) := by ring
    rw [this]; gcongr
  have hy2 : e / 2 ^ 62 * (Real.pi / 2) ≤ Real.pi / 2 := by
    have : e / 2 ^ 62 ≤ 1 := by rw [div_le_one (by positivity)]; exact h2
    nlinarith only [Real.pi_pos, h2, p1]
  have s0 : Real.sin (Real.pi / 2 ^ 11) ≤ Real.sin (e / 2 ^ 62 * (Real.pi / 2)) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith only [Real.pi_pos, p1, p2]) hy2 hy
  have s1 := Real.sin_ge_sub_cube (show 0 ≤ Real.pi / 2 ^ 11 by positivity)
  have c3 : (Real.pi / 2 ^ 11) ^ 3 ≤ (3.15 / 2 ^ 11) ^ 3 := by gcongr
  have : 7070 * 10 ^ 12 ≤ (Real.pi / 2 ^ 11 - (Real.pi / 2 ^ 11) ^ 3 / 6) * 2 ^ 62 := by
    nlinarith only [p1, p2, c3]
  exact this.trans (mul_le_mul_of_nonneg_right (s1.trans s0) (by positivity))

/-- The quotient of two values within `6.1` of `A ≥ 0` and `B ≥ 7.07 · 10^15`,
`A² + B² = 2^124`, is within `8 · 10^-13` of `A / B`. -/
theorem tan_quotient_near (n d A B : ℝ) (hA : 0 ≤ A) (hB : 7070 * 10 ^ 12 ≤ B) (hn : |n - A| ≤ 61 / 10)
    (hd : |d - B| ≤ 61 / 10) (hAB : A ^ 2 + B ^ 2 = 2 ^ 124) : |n / d - A / B| ≤ 8 / 10 ^ 13 := by
  have dl : B - 61 / 10 ≤ d := by linarith only [(abs_le.mp hd).1]
  have Bp : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have dp : 0 < d := lt_of_lt_of_le (by linarith only [hB]) dl
  have sum : A + B ≤ 14143 / 10000 * 2 ^ 62 := by
    nlinarith only [sq_nonneg (A - B), sq_nonneg (A + B - 14143 / 10000 * 2 ^ 62), hAB]
  rw [div_sub_div _ _ dp.ne' Bp.ne', abs_div, abs_of_pos (mul_pos dp Bp)]
  have num : |n * B - d * A| ≤ 61 / 10 * (A + B) := by
    rw [show n * B - d * A = (n - A) * B - (d - B) * A by ring]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_pos Bp, abs_of_nonneg hA]
    nlinarith only [abs_nonneg (n - A), abs_nonneg (d - B), hA, hB, hn, hd]
  have den : (7070 * 10 ^ 12 - 61 / 10) * (7070 * 10 ^ 12) ≤ d * B :=
    mul_le_mul (by linarith only [hB, dl]) hB (by norm_num) dp.le
  rw [div_le_iff₀ (mul_pos dp Bp)]
  calc |n * B - d * A| ≤ 61 / 10 * (14143 / 10000 * 2 ^ 62) := num.trans (by linarith only [sum])
    _ ≤ 8 / 10 ^ 13 * ((7070 * 10 ^ 12 - 61 / 10) * (7070 * 10 ^ 12)) := by norm_num
    _ ≤ 8 / 10 ^ 13 * (d * B) := by gcongr

/-- The tangent at `u = x + e` with `|cos u| ≥ c` and `|e| ≤ η < c` is within
`η / (c · (c - η))` of the tangent at `x`. -/
theorem tan_shift (u x e c η : ℝ) (hu : u = x + e) (hc : c ≤ |Real.cos u|) (he : |e| ≤ η) (hη : η < c) :
    |Real.tan u - Real.tan x| ≤ η / (c * (c - η)) := by
  subst hu
  have η0 : 0 ≤ η := (abs_nonneg _).trans he
  have cx : c - η ≤ |Real.cos x| := by
    have h1 := Real.abs_cos_sub_cos_le (x + e) x
    rw [add_sub_cancel_left] at h1
    have h2 := abs_sub_abs_le_abs_sub (Real.cos (x + e)) (Real.cos x)
    linarith only [he, hc, h1, h2]
  have cp : 0 < c - η := by linarith only [hη]
  have c0 : 0 < c := by linarith only [hη, η0]
  have cu : Real.cos (x + e) ≠ 0 := fun h => by rw [h, abs_zero] at hc; linarith only [hη, hc, η0]
  have cxn : Real.cos x ≠ 0 := fun h => by rw [h, abs_zero] at cx; linarith only [hη, cx]
  rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos, div_sub_div _ _ cu cxn,
    show Real.sin (x + e) * Real.cos x - Real.cos (x + e) * Real.sin x = Real.sin (x + e - x) by
      rw [Real.sin_sub],
    add_sub_cancel_left, abs_div, abs_mul]
  have se : |Real.sin e| ≤ η := by
    have := Real.abs_sin_sub_sin_le e 0
    rw [Real.sin_zero, sub_zero, sub_zero] at this; exact this.trans he
  exact div_le_div₀ η0 se (mul_pos c0 cp) (mul_le_mul hc cx cp.le (abs_nonneg _))

/-- The tangent of `q` quarters plus `φ`: `tan φ` in an even quadrant and
`-cos φ / sin φ` in an odd one. -/
theorem tan_quadrant (q : ℕ) (φ : ℝ) :
    Real.tan (φ + q * (Real.pi / 2)) =
      if q % 2 = 0 then Real.sin φ / Real.cos φ else -(Real.cos φ / Real.sin φ) := by
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' q
  · rw [ite_eq_left (by omega), show φ + ((2 * j : ℕ) : ℝ) * (Real.pi / 2) = φ + ((j : ℤ) : ℝ) * Real.pi by
      push_cast; ring, Real.tan_add_int_mul_pi, Real.tan_eq_sin_div_cos]
  · rw [ite_eq_right (by omega), show φ + ((2 * j + 1 : ℕ) : ℝ) * (Real.pi / 2) =
      (φ + Real.pi / 2) + ((j : ℤ) : ℝ) * Real.pi by push_cast; ring, Real.tan_add_int_mul_pi,
      Real.tan_eq_sin_div_cos, Real.sin_add_pi_div_two, Real.cos_add_pi_div_two, div_neg]

/-- `⌊(⌊n · 2^(k+1) / d⌋ + 1) / 2⌋`, the rounding of `trig::tan` by `shr_round`
of one bit, is within `½` of `n · 2^k / d`. -/
theorem round_quot (n d k : ℕ) (hd : 0 < d) :
    |(((n * 2 ^ (k + 1) / d + 1) / 2 : ℕ) : ℝ) - n * 2 ^ k / d| ≤ 1 / 2 := by
  have e : (n * 2 ^ (k + 1) / d + 1) / 2 = (n * 2 ^ (k + 1) + d) / (d * 2) := by
    rw [← Nat.div_div_eq_div_mul, Nat.add_div_right _ hd]
  rw [e]
  have ⟨l, u⟩ := floor_div_near (n * 2 ^ (k + 1) + d) (d * 2) (by positivity)
  have dp : (0 : ℝ) < d := by exact_mod_cast hd
  have X : ((n * 2 ^ (k + 1) + d : ℕ) : ℝ) / ((d * 2 : ℕ) : ℝ) = n * 2 ^ k / d + 1 / 2 := by
    push_cast; field_simp; ring
  rw [X] at l u
  exact abs_le.mpr ⟨by linarith only [u], by linarith only [l]⟩

/-- The quotient of `trig::tan` away from a pole: `n · 2^(f+1) / d` and one bit of
`shr_round` give `r` within `½ + 2^f · 8 · 10^-13` of `A / B · 2^f` when `n`, `d`
are within `6.1` of `A ≥ 0`, `B ≥ 7.07 · 10^15` with `A² + B² = 2^124`;
`0 ≤ r < 2^44`. Stated for any continuation `k` of `r`. -/
theorem quot_round_spec {α} (n d : Std.U128) (f : Std.U32) (hf : f.val ≤ 32) (A B : ℝ) (hA : 0 ≤ A)
    (hB : 7070 * 10 ^ 12 ≤ B) (hn : |(n.val : ℝ) - A| ≤ 61 / 10) (hd : |(d.val : ℝ) - B| ≤ 61 / 10)
    (hAB : A ^ 2 + B ^ 2 = 2 ^ 124) (k : Std.I128 → Result α) (P : α → Prop)
    (hk : ∀ r : Std.I128, |(r.val : ℝ) - A / B * 2 ^ f.val| ≤ 1 / 2 + 2 ^ f.val * (8 / 10 ^ 13) →
      0 ≤ r.val → r.val < 2 ^ 44 → k r ⦃ P ⦄) :
    (do
      let i10 ← f + 1#u32
      let i11 ← n <<< i10
      let i12 ← i11 / d
      let i13 ← lift (UScalar.hcast .I128 i12)
      let r ← fulcrum.kernel.shr_round i13 1#u32
      k r) ⦃ P ⦄ := by
  have n128 : UScalarTy.U128.numBits = 128 := rfl
  have Bp : (0 : ℝ) < B := lt_of_lt_of_le (by norm_num) hB
  have A1 : A ≤ 2 ^ 62 := by nlinarith only [hA, hAB]
  have nl : n.val ≤ 2 ^ 62 + 7 := by
    have : (n.val : ℝ) ≤ 2 ^ 62 + 7 := by linarith only [(abs_le.mp hn).2, A1]
    exact_mod_cast this
  have dl : (7069 * 10 ^ 12 : ℝ) ≤ d.val := by linarith only [(abs_le.mp hd).1, hB]
  have dl' : 7069 * 10 ^ 12 ≤ d.val := by exact_mod_cast dl
  have dpos : 0 < d.val := lt_of_lt_of_le (by norm_num) dl'
  refine WP.spec_bind (UScalar.add_spec (x := f) (y := 1#u32) (by rw [lit_val, U32_max_val]; omega))
    fun i10 h10 => ?_
  rw [lit_val] at h10
  have big : n.val * 2 ^ (f.val + 1) ≤ (2 ^ 62 + 7) * 2 ^ 33 :=
    Nat.mul_le_mul nl (Nat.pow_le_pow_right two_pos (by omega))
  refine WP.spec_bind (UScalar.ShiftLeft_spec n i10 _ (by rw [h10, n128]; omega) rfl) fun i11 ⟨h11, _⟩ => ?_
  rw [h10, Nat.shiftLeft_eq, UScalar.size_def, n128, Nat.mod_eq_of_lt (big.trans_lt (by norm_num))] at h11
  obtain ⟨i12, e12, h12⟩ := UScalar.div_spec i11 (y := d) dpos.ne'
  rw [e12, bind_ok, lift, bind_ok]
  have ql : i12.val < 2 ^ 44 := by
    rw [h12, h11, Nat.div_lt_iff_lt_mul dpos]
    calc n.val * 2 ^ (f.val + 1) ≤ (2 ^ 62 + 7) * 2 ^ 33 := big
      _ < 2 ^ 44 * (7069 * 10 ^ 12) := by norm_num
      _ ≤ 2 ^ 44 * d.val := Nat.mul_le_mul_left _ dl'
  have hc : (UScalar.hcast .I128 i12).val = (i12.val : ℤ) := by
    rw [UScalar.hcast_val_eq, IScalarTy.I128_numBits_eq]
    exact Int.bmod_eq_of_le ((neg_nonpos.mpr (by positivity)).trans (Int.natCast_nonneg _))
      ((by exact_mod_cast ql : (i12.val : ℤ) < 2 ^ 44).trans_le (by norm_num))
  refine WP.spec_bind (shr_round_spec _ 1#u32) fun r hr => ?_
  rw [hc, lit_val, ← zero_add 1, ← add_half_shr, shr_eq_div, pow_zero, zero_add, pow_one] at hr
  have rv : r.val = (((n.val * 2 ^ (f.val + 1) / d.val + 1) / 2 : ℕ) : ℤ) := by
    rw [hr, h12, h11]; push_cast; rfl
  refine hk r ?_ ?_ ?_
  · have q := round_quot n.val d.val f.val dpos
    have qn := tan_quotient_near n.val d.val A B hA hB hn hd hAB
    rw [rv]
    have e : (((((n.val * 2 ^ (f.val + 1) / d.val + 1) / 2 : ℕ) : ℤ)) : ℝ) =
        (((n.val * 2 ^ (f.val + 1) / d.val + 1) / 2 : ℕ) : ℝ) := by push_cast; rfl
    rw [e]
    have : |(n.val : ℝ) * 2 ^ f.val / d.val - A / B * 2 ^ f.val| ≤ 2 ^ f.val * (8 / 10 ^ 13) := by
      rw [show (n.val : ℝ) * 2 ^ f.val / d.val - A / B * 2 ^ f.val = (n.val / d.val - A / B) * 2 ^ f.val by ring,
        abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ f.val), mul_comm]
      gcongr
    calc _ ≤ |(((n.val * 2 ^ (f.val + 1) / d.val + 1) / 2 : ℕ) : ℝ) - n.val * 2 ^ f.val / d.val| +
          |(n.val : ℝ) * 2 ^ f.val / d.val - A / B * 2 ^ f.val| := abs_sub_le _ _ _
      _ ≤ _ := add_le_add q this
  · rw [rv]; positivity
  · rw [rv]
    have : (n.val * 2 ^ (f.val + 1) / d.val + 1) / 2 < 2 ^ 44 := by
      rw [← h11, ← h12]; omega
    exact_mod_cast this

/-- The denominator position of `trig::tan` away from a pole at the position
`t`: `2^62 - p` in an even quadrant, `p` in an odd one, `p` the low 62 bits. -/
def tanDen (t : ℕ) : ℕ := if t / 2 ^ 62 % 2 = 0 then 2 ^ 62 - t % 2 ^ 62 else t % 2 ^ 62

/-- On the code: the branch of `trig::tan` away from a pole, at the position `t`
whose denominator position is at least `2^52`, never fails and is within
`½ + 2^f · 8 · 10^-13` of `tan (t / 2^62 · π/2) · 2^f`, below `2^44` in magnitude. -/
theorem tan_far_spec (t : Std.U64) (f : Std.U32) (hf : f.val ≤ 32) (hden : 2 ^ 52 ≤ tanDen t.val) :
    (do
      let i3 ← 1#u64 <<< fulcrum.tables.trig.FRAC
      let i4 ← i3 - 1#u64
      let p ← lift (t &&& i4)
      let i5 ← fulcrum.trig.sin_quarter p fulcrum.tables.trig.FRAC
      let a ← lift (UScalar.cast .U128 i5)
      let i6 ← i3 - p
      let i7 ← fulcrum.trig.sin_quarter i6 fulcrum.tables.trig.FRAC
      let b ← lift (UScalar.cast .U128 i7)
      let i8 ← t >>> fulcrum.tables.trig.FRAC
      let i9 ← lift (i8 &&& 1#u64)
      let (n, d1, negative) ←
        if i9 = 0#u64
        then ok (a, b, false)
        else ok (b, a, true)
      let i10 ← f + 1#u32
      let i11 ← n <<< i10
      let i12 ← i11 / d1
      let i13 ← lift (UScalar.hcast .I128 i12)
      let r ← fulcrum.kernel.shr_round i13 1#u32
      if negative
      then -. r
      else ok r) ⦃ r =>
        |(r.val : ℝ) - Real.tan ((t.val : ℝ) / 2 ^ 62 * (Real.pi / 2)) * 2 ^ f.val| ≤
          1 / 2 + 2 ^ f.val * (8 / 10 ^ 13) ∧ |r.val| < 2 ^ 44 ⦄ := by
  refine WP.spec_bind (UScalar.ShiftLeft_spec 1#u64 fulcrum.tables.trig.FRAC _
    (by rw [trig_frac_val, UScalarTy.U64_numBits_eq]; norm_num) rfl) fun i3 ⟨h3, _⟩ => ?_
  rw [lit_val, trig_frac_val, Nat.shiftLeft_eq, one_mul, UScalar.size_def, UScalarTy.U64_numBits_eq,
    Nat.mod_eq_of_lt (by norm_num)] at h3
  refine WP.spec_bind (UScalar.sub_spec (x := i3) (y := 1#u64) (by rw [h3, lit_val]; norm_num))
    fun i4 ⟨h4, _⟩ => ?_
  rw [h3, lit_val] at h4
  rw [lift, bind_ok]
  have pv : (t &&& i4).val = t.val % 2 ^ 62 := by
    rw [UScalar.val_and, h4, Nat.and_two_pow_sub_one_eq_mod]
  generalize t &&& i4 = p at pv ⊢
  have pl : p.val ≤ 2 ^ 62 := pv ▸ (Nat.mod_lt _ (by norm_num)).le
  refine WP.spec_bind (sin_quarter_spec p _ (by rw [trig_frac_val]) (by rw [trig_frac_val]; exact pl))
    fun i5 h5 => ?_
  rw [lift, bind_ok]
  refine WP.spec_bind (UScalar.sub_spec (x := i3) (y := p) (by rw [h3]; exact pl)) fun i6 ⟨h6, _⟩ => ?_
  rw [h3] at h6
  refine WP.spec_bind (sin_quarter_spec i6 _ (by rw [trig_frac_val]) (by rw [trig_frac_val, h6]; omega))
    fun i7 h7 => ?_
  rw [lift, bind_ok]
  refine WP.spec_bind (UScalar.ShiftRight_spec t fulcrum.tables.trig.FRAC
    (by rw [trig_frac_val, UScalarTy.U64_numBits_eq]; norm_num)) fun i8 ⟨h8, _⟩ => ?_
  rw [trig_frac_val, Nat.shiftRight_eq_div_pow] at h8
  rw [lift, bind_ok]
  have i9v : (i8 &&& 1#u64).val = t.val / 2 ^ 62 % 2 := by
    rw [UScalar.val_and, lit_val, Nat.and_one_is_mod, h8]
  generalize i8 &&& 1#u64 = i9 at i9v ⊢
  rw [trig_frac_val] at h5 h7
  set φ : ℝ := (p.val : ℝ) / 2 ^ 62 * (Real.pi / 2) with hφ
  have φ0 : 0 ≤ φ := by positivity
  have φ1 : φ ≤ Real.pi / 2 := by
    have : (p.val : ℝ) / 2 ^ 62 ≤ 1 := by
      rw [div_le_one (by positivity)]; exact_mod_cast pl
    rw [hφ]; nlinarith only [Real.pi_pos, this]
  have e7 : (i6.val : ℝ) / 2 ^ 62 * (Real.pi / 2) = Real.pi / 2 - φ := by
    rw [h6, Nat.cast_sub pl, hφ]; push_cast; field_simp; ring
  rw [e7, Real.sin_pi_div_two_sub] at h7
  set A : ℝ := Real.sin φ * 2 ^ 62
  set B : ℝ := Real.cos φ * 2 ^ 62
  have A0 : 0 ≤ A := mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi φ0 (by linarith only [Real.pi_pos, φ0, φ1])) (by positivity)
  have B0 : 0 ≤ B := mul_nonneg (Real.cos_nonneg_of_mem_Icc ⟨by linarith only [Real.pi_pos, φ0, φ1], φ1⟩) (by positivity)
  have AB : A ^ 2 + B ^ 2 = 2 ^ 124 := by
    have := Real.sin_sq_add_cos_sq φ
    rw [show A ^ 2 + B ^ 2 = (Real.sin φ ^ 2 + Real.cos φ ^ 2) * 2 ^ 124 by ring, this, one_mul]
  have tq : t.val = t.val / 2 ^ 62 * 2 ^ 62 + p.val := by rw [pv]; exact (Nat.div_add_mod' _ _).symm
  have ang : (t.val : ℝ) / 2 ^ 62 * (Real.pi / 2) = φ + ((t.val / 2 ^ 62 : ℕ) : ℝ) * (Real.pi / 2) := by
    rw [show (t.val : ℝ) = ((t.val / 2 ^ 62 * 2 ^ 62 + p.val : ℕ) : ℝ) by rw [← tq], hφ]
    push_cast; field_simp; ring
  rw [ang, tan_quadrant]
  have ca : (UScalar.cast .U128 i5).val = i5.val := cast_u128_val i5
  have cb : (UScalar.cast .U128 i7).val = i7.val := cast_u128_val i7
  by_cases h0 : i9 = 0#u64
  · have ev : t.val / 2 ^ 62 % 2 = 0 := by rw [← i9v, h0]; rfl
    rw [ite_eq_left h0, bind_ok, ite_eq_left ev]
    have den : 2 ^ 52 ≤ i6.val := by rw [h6, pv]; unfold tanDen at hden; rw [ite_eq_left ev] at hden; exact hden
    have Bl : 7070 * 10 ^ 12 ≤ B := by
      have := quarter_sin_lower i6.val (by exact_mod_cast den) (by exact_mod_cast (h6 ▸ Nat.sub_le _ _ : i6.val ≤ 2 ^ 62))
      rwa [e7, Real.sin_pi_div_two_sub] at this
    refine quot_round_spec _ _ f hf A B A0 Bl (by rw [ca]; exact h5) (by rw [cb]; exact h7) AB _ _
      fun r hr r0 rl => ?_
    rw [ite_eq_right Bool.false_ne_true, WP.spec_ok]
    refine ⟨?_, by rw [abs_of_nonneg r0]; exact rl⟩
    rw [show Real.sin φ / Real.cos φ * 2 ^ f.val = A / B * 2 ^ f.val by
      simp only [A, B]; field_simp]
    exact hr
  · have od : ¬ t.val / 2 ^ 62 % 2 = 0 := fun e => h0 (UScalar.eq_of_val_eq (by rw [i9v, e]; rfl))
    rw [ite_eq_right h0, bind_ok, ite_eq_right od]
    have den : 2 ^ 52 ≤ p.val := by rw [pv]; unfold tanDen at hden; rw [ite_eq_right od] at hden; exact hden
    have Al : 7070 * 10 ^ 12 ≤ A := quarter_sin_lower p.val (by exact_mod_cast den) (by exact_mod_cast pl)
    refine quot_round_spec _ _ f hf B A B0 Al (by rw [cb]; exact h7) (by rw [ca]; exact h5)
      (by rw [add_comm]; exact AB) _ _ fun r hr r0 rl => ?_
    rw [ite_eq_left rfl]
    refine WP.spec_mono (IScalar.neg_step _ (fun e => ?_)) fun r' hr' => ?_
    · rw [e, IScalar.min_def, IScalarTy.I128_numBits_eq] at r0; norm_num at r0
    · rw [hr']
      refine ⟨?_, by rw [abs_neg, abs_of_nonneg r0]; exact rl⟩
      rw [show (((-r.val : ℤ)) : ℝ) - -(Real.cos φ / Real.sin φ) * 2 ^ f.val =
        -((r.val : ℝ) - B / A * 2 ^ f.val) by simp only [A, B]; push_cast; field_simp; ring, abs_neg]
      exact hr

/-- `θ` of `trig::tan` near a pole on naturals, at 64 fractional bits:
`⌊⌊D / 2^64⌋ · FRAC_PI_2 / 2^62⌋`. -/
def thetaN (D : ℕ) : ℕ := D / 2 ^ 64 * 7244019458077122842 / 2 ^ 62

/-- `θ³` of `trig::tan` near a pole: `⌊⌊θ² / 2^64⌋ · θ / 2^64⌋`. -/
def theta3N (D : ℕ) : ℕ := thetaN D * thetaN D / 2 ^ 64 * thetaN D / 2 ^ 64

/-- `cot θ · 2^64` of `trig::tan` near a pole: `⌊C / D⌋ - ⌊θ / 3⌋ - ⌊θ³ / 45⌋`. -/
def cotN (D : ℕ) : ℕ := frac2PiN / D - thetaN D / 3 - theta3N D / 45

theorem frac2PiN_ge : 2 ^ 191 ≤ frac2PiN := by
  have h : |(frac2PiN : ℝ) - 2 / Real.pi * 2 ^ 192| ≤ 1 / 2 := frac_2_pi_entry
  have p2 := Real.pi_lt_d2
  have : (2 : ℝ) ^ 191 + 1 ≤ 2 / Real.pi * 2 ^ 192 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ Real.pi_pos]; nlinarith only [p2]
  have : (2 : ℝ) ^ 191 ≤ frac2PiN := by linarith only [(abs_le.mp h).1, this]
  exact_mod_cast this

theorem words3_lt (a b c : ℕ) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hc : c < 2 ^ 64) :
    a * 2 ^ 128 + b * 2 ^ 64 + c < 2 ^ 192 :=
  calc a * 2 ^ 128 + b * 2 ^ 64 + c < a * 2 ^ 128 + b * 2 ^ 64 + 2 ^ 64 := by omega
    _ = (a * 2 ^ 64 + b + 1) * 2 ^ 64 := by ring
    _ ≤ 2 ^ 128 * 2 ^ 64 := Nat.mul_le_mul_right _ (words_succ_le a b ha hb)
    _ = 2 ^ 192 := by rw [← pow_add]

theorem frac2PiN_lt : frac2PiN < 2 ^ 192 := by
  rw [frac2PiN_words]; exact words3_lt _ _ _ (fracWord_lt 0) (fracWord_lt 1) (fracWord_lt 2)

theorem thetaN_lt (D : ℕ) (hD : D < 2 ^ 118) : thetaN D < 2 ^ 55 := by
  unfold thetaN
  rw [Nat.div_lt_iff_lt_mul (by positivity)]
  have : D / 2 ^ 64 < 2 ^ 54 := by rw [Nat.div_lt_iff_lt_mul (by positivity)]; exact hD.trans_le (by norm_num)
  calc D / 2 ^ 64 * 7244019458077122842 < 2 ^ 54 * 7244019458077122842 :=
        Nat.mul_lt_mul_of_pos_right this (by norm_num)
    _ ≤ 2 ^ 55 * 2 ^ 62 := by norm_num

theorem theta3N_lt (D : ℕ) (hD : D < 2 ^ 118) : theta3N D < 2 ^ 37 := by
  have t := thetaN_lt D hD
  unfold theta3N
  have t2 : thetaN D * thetaN D / 2 ^ 64 < 2 ^ 46 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc thetaN D * thetaN D < 2 ^ 55 * 2 ^ 55 := Nat.mul_lt_mul'' t t
      _ = 2 ^ 46 * 2 ^ 64 := by norm_num
  rw [Nat.div_lt_iff_lt_mul (by positivity)]
  calc thetaN D * thetaN D / 2 ^ 64 * thetaN D < 2 ^ 46 * 2 ^ 55 := Nat.mul_lt_mul'' t2 t
    _ ≤ 2 ^ 37 * 2 ^ 64 := by norm_num

/-- On the code: the block of `trig::tan` near a pole, `d < 2^118`, `f ≤ 32`:
`2^(2f)` below `2^(126 - f)`, else `cotN d` rounded to `f` bits; for any
continuation `k` of the result. -/
theorem tan_near_spec {α} (d : Std.U128) (f : Std.U32) (hf : f.val ≤ 32) (hd : d.val < 2 ^ 118)
    (k : Std.I128 → Result α) (P : α → Prop)
    (hk : ∀ r : Std.I128, (d.val < 2 ^ (126 - f.val) → r.val = 2 ^ (2 * f.val)) →
      (2 ^ (126 - f.val) ≤ d.val → r.val = roundHalfUp (exact (64 - f.val) (cotN d.val))) → k r ⦃ P ⦄) :
    (do
      let i3 ← 126#u32 - f
      let i4 ← 1#u128 <<< i3
      let r ←
        if d < i4
        then do
             let i5 ← 2#u32 * f
             1#i128 <<< i5
        else
          do
          let i5 ← d >>> 64#i32
          let i6 ← lift (UScalar.cast .U128 fulcrum.tables.trig.FRAC_PI_2)
          let i7 ← i5 * i6
          let theta ← i7 >>> fulcrum.tables.trig.FRAC
          let i8 ← theta * theta
          let theta2 ← i8 >>> 64#i32
          let i9 ← theta2 * theta
          let theta3 ← i9 >>> 64#i32
          let i10 ← fulcrum.trig.frac_2_pi_div d
          let i11 ← theta / 3#u128
          let i12 ← i10 - i11
          let i13 ← theta3 / 45#u128
          let cot ← i12 - i13
          let i14 ← lift (UScalar.hcast .I128 cot)
          let i15 ← 64#u32 - f
          fulcrum.kernel.shr_round i14 i15
      k r) ⦃ P ⦄ := by
  have n128 : UScalarTy.U128.numBits = 128 := rfl
  refine WP.spec_bind (UScalar.sub_spec (x := 126#u32) (y := f) (by rw [lit_val]; omega)) fun i3 ⟨h3, _⟩ => ?_
  rw [lit_val] at h3
  refine WP.spec_bind (UScalar.ShiftLeft_spec 1#u128 i3 _ (by rw [h3, n128]; omega) rfl) fun i4 ⟨h4, _⟩ => ?_
  rw [lit_val, h3, Nat.shiftLeft_eq, one_mul, UScalar.size_def, n128,
    Nat.mod_eq_of_lt (Nat.pow_lt_pow_right one_lt_two (by omega))] at h4
  by_cases hs : d < i4
  · have hs' : d.val < 2 ^ (126 - f.val) := h4 ▸ hs
    rw [ite_eq_left hs]
    refine WP.spec_bind (Pₘ := fun z : Std.I128 => z.val = 2 ^ (2 * f.val)) ?_ fun r hr => ?_
    · refine WP.spec_bind (UScalar.mul_spec (x := 2#u32) (y := f) (by rw [lit_val, U32_max_val]; omega))
        fun i5 h5 => ?_
      rw [lit_val] at h5
      refine WP.spec_mono (IScalar.ShiftLeft_spec 1#i128 i5 (by rw [h5, IScalarTy.I128_numBits_eq]; omega))
        fun z ⟨hz, _⟩ => ?_
      rw [hz, h5, show ((1#i128 : Std.I128).val) = 1 from rfl, Int.shiftLeft_eq, one_mul,
        IScalarTy.I128_numBits_eq]
      refine Int.bmod_eq_of_le ?_ ?_
      · have : (0 : ℤ) ≤ 2 ^ (2 * f.val) := by positivity
        exact (neg_nonpos.mpr (by positivity)).trans this
      · exact (pow_lt_pow_right₀ (by norm_num) (by omega : 2 * f.val < 127)).trans_le (by norm_num)
    · exact hk r (fun _ => hr) (fun h => absurd h (not_le.mpr hs'))
  · have hs' : 2 ^ (126 - f.val) ≤ d.val := by
      have : ¬ d.val < i4.val := hs
      rw [h4] at this; omega
    have d94 : 2 ^ 94 ≤ d.val := (Nat.pow_le_pow_right two_pos (by omega)).trans hs'
    rw [ite_eq_right hs]
    refine WP.spec_bind (Pₘ := fun z : Std.I128 => z.val = roundHalfUp (exact (64 - f.val) (cotN d.val)))
      ?_ fun r hr => hk r (fun h => absurd hs' (not_le.mpr h)) (fun _ => hr)
    refine WP.spec_bind (shr_i32_spec d 64#i32 64 rfl (by rw [n128]; norm_num)) fun i5 h5 => ?_
    rw [lift, bind_ok]
    have i5l : i5.val < 2 ^ 54 := by
      rw [h5, Nat.div_lt_iff_lt_mul (by positivity)]; exact hd.trans_le (by norm_num)
    have c6 : (UScalar.cast .U128 fulcrum.tables.trig.FRAC_PI_2).val = 7244019458077122842 := by
      rw [cast_u128_val, frac_pi_2_val]
    refine WP.spec_bind (UScalar.mul_spec (x := i5) (y := UScalar.cast .U128 fulcrum.tables.trig.FRAC_PI_2)
      (by rw [c6, U128_max_val]
          calc i5.val * 7244019458077122842 ≤ 2 ^ 54 * 7244019458077122842 := Nat.mul_le_mul_right _ i5l.le
            _ ≤ 2 ^ 128 - 1 := by norm_num)) fun i7 h7 => ?_
    rw [c6] at h7
    refine WP.spec_bind (UScalar.ShiftRight_spec i7 fulcrum.tables.trig.FRAC
      (by rw [trig_frac_val, n128]; norm_num)) fun th ⟨hth, _⟩ => ?_
    have tv : th.val = thetaN d.val := by
      rw [hth, trig_frac_val, Nat.shiftRight_eq_div_pow, h7, h5]; rfl
    have tl : th.val < 2 ^ 55 := tv ▸ thetaN_lt _ hd
    refine WP.spec_bind (UScalar.mul_spec (x := th) (y := th)
      (by rw [U128_max_val]
          calc th.val * th.val ≤ 2 ^ 55 * 2 ^ 55 := Nat.mul_le_mul tl.le tl.le
            _ ≤ 2 ^ 128 - 1 := by norm_num)) fun i8 h8 => ?_
    refine WP.spec_bind (shr_i32_spec i8 64#i32 64 rfl (by rw [n128]; norm_num)) fun th2 hth2 => ?_
    have t2l : th2.val < 2 ^ 46 := by
      rw [hth2, h8, Nat.div_lt_iff_lt_mul (by positivity)]
      calc th.val * th.val < 2 ^ 55 * 2 ^ 55 := Nat.mul_lt_mul'' tl tl
        _ = 2 ^ 46 * 2 ^ 64 := by norm_num
    refine WP.spec_bind (UScalar.mul_spec (x := th2) (y := th)
      (by rw [U128_max_val]
          calc th2.val * th.val ≤ 2 ^ 46 * 2 ^ 55 := Nat.mul_le_mul t2l.le tl.le
            _ ≤ 2 ^ 128 - 1 := by norm_num)) fun i9 h9 => ?_
    refine WP.spec_bind (shr_i32_spec i9 64#i32 64 rfl (by rw [n128]; norm_num)) fun th3 hth3 => ?_
    have t3v : th3.val = theta3N d.val := by
      rw [hth3, h9, hth2, h8, tv]; rfl
    refine WP.spec_bind (frac_2_pi_div_spec d ((Nat.pow_le_pow_right two_pos (by norm_num)).trans d94) hd)
      fun i10 h10 => ?_
    have Cd : 2 ^ 73 ≤ frac2PiN / d.val := by
      rw [Nat.le_div_iff_mul_le (by omega)]
      calc 2 ^ 73 * d.val ≤ 2 ^ 73 * 2 ^ 118 := Nat.mul_le_mul_left _ hd.le
        _ = 2 ^ 191 := by norm_num
        _ ≤ frac2PiN := frac2PiN_ge
    obtain ⟨i11, e11, h11⟩ := UScalar.div_spec th (y := 3#u128) (by decide)
    rw [e11, bind_ok]
    rw [show ((3#u128 : Std.U128).val) = 3 from rfl] at h11
    refine WP.spec_bind (UScalar.sub_spec (x := i10) (y := i11) (by rw [h10, h11]; omega)) fun i12 ⟨h12, _⟩ => ?_
    obtain ⟨i13, e13, h13⟩ := UScalar.div_spec th3 (y := 45#u128) (by decide)
    rw [e13, bind_ok]
    rw [show ((45#u128 : Std.U128).val) = 45 from rfl] at h13
    have t3l : th3.val < 2 ^ 37 := t3v ▸ theta3N_lt _ hd
    refine WP.spec_bind (UScalar.sub_spec (x := i12) (y := i13) (by rw [h12, h10, h11, h13]; omega))
      fun cot ⟨hcot, _⟩ => ?_
    have cv : cot.val = cotN d.val := by
      rw [hcot, h12, h10, h11, h13, tv, t3v]; rfl
    have cl : cot.val < 2 ^ 98 := by
      rw [hcot, h12, h10]
      have : frac2PiN / d.val < 2 ^ 98 := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]
        calc frac2PiN < 2 ^ 192 := frac2PiN_lt
          _ = 2 ^ 98 * 2 ^ 94 := by norm_num
          _ ≤ 2 ^ 98 * d.val := Nat.mul_le_mul_left _ d94
      omega
    rw [lift, bind_ok]
    have hc : (UScalar.hcast .I128 cot).val = (cot.val : ℤ) := by
      rw [UScalar.hcast_val_eq, IScalarTy.I128_numBits_eq]
      exact Int.bmod_eq_of_le ((neg_nonpos.mpr (by positivity)).trans (Int.natCast_nonneg _))
        ((by exact_mod_cast cl : (cot.val : ℤ) < 2 ^ 98).trans_le (by norm_num))
    refine WP.spec_bind (UScalar.sub_spec (x := 64#u32) (y := f) (by rw [lit_val]; omega)) fun i15 ⟨h15, _⟩ => ?_
    rw [lit_val] at h15
    refine WP.spec_mono (shr_round_spec _ i15) fun r hr => ?_
    rw [hr, hc, h15, cv]

/-- `thetaN D` is within `2.58` of `D · π / 2^65`, `θ` of the distance `D` at 64
fractional bits: the floor of `D / 2^64` loses below `π/2`, `FRAC_PI_2` half a
unit, the last floor one. -/
theorem thetaN_near (D : ℕ) (hD : D < 2 ^ 118) : |(thetaN D : ℝ) - D * Real.pi / 2 ^ 65| ≤ 258 / 100 := by
  have hF : |(7244019458077122842 : ℝ) - Real.pi / 2 * 2 ^ 62| ≤ 1 / 2 := by
    have := frac_pi_2_entry; rw [frac_pi_2_val] at this; exact_mod_cast this
  have p2 := Real.pi_lt_d2
  have ⟨l1, u1⟩ := floor_div_near D (2 ^ 64) (by positivity)
  have ⟨l2, u2⟩ := floor_div_near (D / 2 ^ 64 * 7244019458077122842) (2 ^ 62) (by positivity)
  unfold thetaN
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at l1 u1 l2 u2 ⊢
  set D1 : ℝ := ((D / 2 ^ 64 : ℕ) : ℝ)
  have Dl : (D : ℝ) < 2 ^ 118 := by exact_mod_cast hD
  have D0 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have ⟨hF1, hF2⟩ := abs_le.mp hF
  have e : D1 * 7244019458077122842 / 2 ^ 62 - D * Real.pi / 2 ^ 65 =
      (D1 - D / 2 ^ 64) * (7244019458077122842 / 2 ^ 62) +
        D / 2 ^ 64 * ((7244019458077122842 - Real.pi / 2 * 2 ^ 62) / 2 ^ 62) := by ring
  have b1 : |(D1 - D / 2 ^ 64) * (7244019458077122842 / 2 ^ 62)| ≤ 1576 / 1000 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 7244019458077122842 / 2 ^ 62)]
    have : |D1 - D / 2 ^ 64| ≤ 1 := abs_le.mpr ⟨by linarith only [u1], by linarith only [p2, l1, hF2]⟩
    calc |D1 - D / 2 ^ 64| * (7244019458077122842 / 2 ^ 62) ≤ 1 * (7244019458077122842 / 2 ^ 62) := by gcongr
      _ ≤ 1576 / 1000 := by norm_num
  have b2 : |D / 2 ^ 64 * ((7244019458077122842 - Real.pi / 2 * 2 ^ 62) / 2 ^ 62)| ≤ 1 / 500 := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ D / 2 ^ 64), abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 62)]
    calc (D : ℝ) / 2 ^ 64 * (|(7244019458077122842 : ℝ) - Real.pi / 2 * 2 ^ 62| / 2 ^ 62)
        ≤ 2 ^ 54 * ((1 / 2) / 2 ^ 62) := by
          gcongr
          rw [div_le_iff₀ (by positivity)]; linarith only [Dl]
      _ ≤ 1 / 500 := by norm_num
  have h3 := (abs_add_le _ _).trans (add_le_add b1 b2)
  rw [← e] at h3
  have := abs_le.mp h3
  exact abs_le.mpr ⟨by linarith only [p2, u2, hF2, this], by linarith only [p2, l2, hF2, this]⟩

/-- `theta3N D` is within `1.02` of `T³ / 2^128` when `thetaN D` is within `2.6`
of `T ∈ [0, 2^55]`. -/
theorem theta3N_near (D : ℕ) (T : ℝ) (hD : D < 2 ^ 118) (hT : |(thetaN D : ℝ) - T| ≤ 26 / 10) (T0 : 0 ≤ T)
    (Tl : T ≤ 2 ^ 55) : |(theta3N D : ℝ) - T ^ 3 / 2 ^ 128| ≤ 102 / 100 := by
  have ul : (thetaN D : ℝ) < 2 ^ 55 := by exact_mod_cast thetaN_lt D hD
  unfold theta3N
  have ⟨l1, u1⟩ := floor_div_near (thetaN D * thetaN D) (2 ^ 64) (by positivity)
  have ⟨l2, u2⟩ := floor_div_near (thetaN D * thetaN D / 2 ^ 64 * thetaN D) (2 ^ 64) (by positivity)
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at l1 u1 l2 u2 ⊢
  set u : ℝ := (thetaN D : ℝ)
  set v : ℝ := ((thetaN D * thetaN D / 2 ^ 64 : ℕ) : ℝ)
  have u0 : 0 ≤ u := Nat.cast_nonneg _
  have b1 : |v * u / 2 ^ 64 - u ^ 3 / 2 ^ 128| ≤ 1 / 500 := by
    rw [show v * u / 2 ^ 64 - u ^ 3 / 2 ^ 128 = (v - u * u / 2 ^ 64) * (u / 2 ^ 64) by ring, abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ u / 2 ^ 64)]
    have : |v - u * u / 2 ^ 64| ≤ 1 := abs_le.mpr ⟨by linarith only [u1], by linarith only [l1]⟩
    calc |v - u * u / 2 ^ 64| * (u / 2 ^ 64) ≤ 1 * (2 ^ 55 / 2 ^ 64) := by gcongr
      _ ≤ 1 / 500 := by norm_num
  have b2 : |u ^ 3 / 2 ^ 128 - T ^ 3 / 2 ^ 128| ≤ 1 / 5000 := by
    rw [← sub_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 128),
      show u ^ 3 - T ^ 3 = (u - T) * (u ^ 2 + u * T + T ^ 2) by ring, abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ u ^ 2 + u * T + T ^ 2), div_le_iff₀ (by positivity)]
    have : u ^ 2 + u * T + T ^ 2 ≤ 3 * 2 ^ 110 := by nlinarith only [T0, Tl, ul, u0]
    calc |u - T| * (u ^ 2 + u * T + T ^ 2) ≤ 26 / 10 * (3 * 2 ^ 110) := by gcongr
      _ ≤ 1 / 5000 * 2 ^ 128 := by norm_num
  have b3 := (abs_sub_le (v * u / 2 ^ 64) (u ^ 3 / 2 ^ 128) (T ^ 3 / 2 ^ 128)).trans (add_le_add b1 b2)
  have := abs_le.mp b3
  exact abs_le.mpr ⟨by linarith only [u2, this], by linarith only [l2, this]⟩

/-- `cotN D` is within `512` of `2^64 · cot θ`, `θ = (D + ε) · π / 2^129` the
distance `D + ε` to the pole in radians, for `2^94 ≤ D < 2^118` and `|ε| ≤ 3/2`:
the first three terms of the cotangent lose below `408` (`cot_near`), `⌊C / D⌋`
below `27` with the error of `D`, `θ` and `θ³` below `2` and `1.03`. -/
theorem cotN_near (D : ℕ) (ε : ℝ) (h1 : 2 ^ 94 ≤ D) (h2 : D < 2 ^ 118) (he : |ε| ≤ 3 / 2) :
    |(cotN D : ℝ) - 2 ^ 64 * (Real.cos ((D + ε) * Real.pi / 2 ^ 129) /
      Real.sin ((D + ε) * Real.pi / 2 ^ 129))| ≤ 512 := by
  have p1 := Real.pi_gt_d2
  have p2 := Real.pi_lt_d2
  have D1 : (2 : ℝ) ^ 94 ≤ D := by exact_mod_cast h1
  have D2 : (D : ℝ) < 2 ^ 118 := by exact_mod_cast h2
  have ⟨e1, e2⟩ := abs_le.mp he
  set θ : ℝ := (D + ε) * Real.pi / 2 ^ 129 with hθ
  set! T : ℝ := (D + ε) * Real.pi / 2 ^ 65 with hT
  set! K : ℝ := 2 / Real.pi * 2 ^ 192 with hK
  have Dε : (2 : ℝ) ^ 94 - 3 / 2 ≤ D + ε := by linarith only [D1, e1]
  have θ0 : 0 < θ := by
    have : (0 : ℝ) < D + ε := by linarith only [p1, p2, D1, e1]
    rw [hθ]; exact div_pos (mul_pos this Real.pi_pos) (by positivity)
  have θ1 : θ ≤ 1 / 650 := by
    rw [hθ, div_le_iff₀ (by positivity)]; nlinarith only [p1, p2, D2, e2, hθ, θ0]
  have cn := cot_near θ θ0 (θ1.trans (by norm_num))
  have hTθ : T = 2 ^ 64 * θ := by rw [hT, hθ]; ring
  have hKθ : K / (D + ε) = 2 ^ 64 * (1 / θ) := by
    rw [hK, hθ]; field_simp
  have R : |2 ^ 64 * (Real.cos θ / Real.sin θ) - (K / (D + ε) - T / 3 - T ^ 3 / (45 * 2 ^ 128))| ≤ 408 := by
    rw [hKθ, hTθ, show 2 ^ 64 * (Real.cos θ / Real.sin θ) - (2 ^ 64 * (1 / θ) - 2 ^ 64 * θ / 3 -
      (2 ^ 64 * θ) ^ 3 / (45 * 2 ^ 128)) = 2 ^ 64 * (Real.cos θ / Real.sin θ - (1 / θ - θ / 3 - θ ^ 3 / 45)) by ring,
      abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 64)]
    calc 2 ^ 64 * |Real.cos θ / Real.sin θ - (1 / θ - θ / 3 - θ ^ 3 / 45)| ≤ 2 ^ 64 * (θ ^ 5 / 390) := by gcongr
      _ ≤ 2 ^ 64 * ((1 / 650) ^ 5 / 390) := by gcongr
      _ ≤ 408 := by norm_num
  have hC : |(frac2PiN : ℝ) - K| ≤ 1 / 2 := frac_2_pi_entry
  have Kl : K ≤ 2 ^ 192 := by
    rw [hK]; have : 2 / Real.pi ≤ 1 := by rw [div_le_one Real.pi_pos]; linarith only [p1, θ0, θ1]
    nlinarith only [this]
  have K0 : 0 ≤ K := by positivity
  have a1 := div_near frac2PiN D K (1 / 2) (by (clear * - h1 h2; omega)) hC
  have a2 : |K / D - K / (D + ε)| ≤ 25 := by
    rw [div_sub_div _ _ (ne_of_gt (by linarith only [D1, θ0, θ1])) (ne_of_gt (by linarith only [D1, e1, θ0, θ1])), abs_div,
      show K * (D + ε) - D * K = K * ε by ring, abs_mul, abs_of_nonneg K0,
      abs_of_pos (by nlinarith only [D1, e1, θ0, θ1] : (0 : ℝ) < D * (D + ε)), div_le_iff₀ (by nlinarith only [D1, e1, θ0, θ1])]
    calc K * |ε| ≤ 2 ^ 192 * (3 / 2) := mul_le_mul Kl he (abs_nonneg _) (by positivity)
      _ ≤ 25 * (2 ^ 94 * (2 ^ 94 - 3 / 2)) := by norm_num
      _ ≤ 25 * (D * (D + ε)) := by gcongr
  have A : |((frac2PiN / D : ℕ) : ℝ) - K / (D + ε)| ≤ 27 := by
    have : (1 / 2 : ℝ) / D ≤ 1 / 2 := div_le_self (by norm_num) (by linarith only [D1, θ0, θ1])
    have := (abs_sub_le _ (K / D) _).trans (add_le_add a1 a2)
    linarith
  have tn := thetaN_near D h2
  have tT : |(thetaN D : ℝ) - T| ≤ 26 / 10 := by
    have : |(D : ℝ) * Real.pi / 2 ^ 65 - T| ≤ 1 / 50 := by
      rw [hT, ← sub_div, show (D : ℝ) * Real.pi - (D + ε) * Real.pi = -(ε * Real.pi) by ring, abs_div, abs_neg,
        abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 65), div_le_iff₀ (by positivity)]
      nlinarith only [abs_nonneg ε, he, p1, p2, θ0, θ1]
    have := (abs_sub_le _ _ _).trans (add_le_add tn this)
    linarith only [this]
  have T0 : 0 ≤ T := by rw [hTθ]; positivity
  have Tl : T ≤ 2 ^ 55 := by rw [hTθ]; nlinarith only [θ0, θ1]
  have B := div_near (thetaN D) 3 T (26 / 10) (by norm_num) tT
  have w := theta3N_near D T h2 tT T0 Tl
  have Cw := div_near (theta3N D) 45 (T ^ 3 / 2 ^ 128) (102 / 100) (by norm_num) w
  have tl : thetaN D / 3 < 2 ^ 55 := (Nat.div_le_self _ _).trans_lt (thetaN_lt D h2)
  have t3l : theta3N D / 45 < 2 ^ 37 := (Nat.div_le_self _ _).trans_lt (theta3N_lt D h2)
  have Cd : 2 ^ 73 ≤ frac2PiN / D := by
    rw [Nat.le_div_iff_mul_le (by (clear * - h1 h2; omega))]
    calc 2 ^ 73 * D ≤ 2 ^ 73 * 2 ^ 118 := Nat.mul_le_mul_left _ h2.le
      _ = 2 ^ 191 := by norm_num
      _ ≤ frac2PiN := frac2PiN_ge
  have cast : (cotN D : ℝ) = ((frac2PiN / D : ℕ) : ℝ) - ((thetaN D / 3 : ℕ) : ℝ) - ((theta3N D / 45 : ℕ) : ℝ) := by
    unfold cotN
    rw [Nat.cast_sub (by (clear * - tl t3l Cd; omega)), Nat.cast_sub (by (clear * - tl Cd; omega))]
  rw [cast]
  push_cast at B Cw
  have := abs_le.mp A
  have := abs_le.mp B
  have := abs_le.mp Cw
  have := abs_le.mp R
  refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith

/-- Away from a pole the denominator position is at least `2^52`: the quarter
turns `q + fr / 2^128` are at least `2^-10` above an odd `q`, or at most
`1 - 2^-10` above an even one, and rounding to 62 bits keeps `2^52` units. -/
theorem tanDen_far (q fr : ℕ) (hq : q < 4) (hfr : fr < 2 ^ 128)
    (h : (q % 2 = 1 ∧ 2 ^ 118 ≤ fr) ∨ (q % 2 = 0 ∧ fr ≤ 2 ^ 128 - 2 ^ 118)) :
    2 ^ 52 ≤ tanDen ((q * 2 ^ 128 + fr + 2 ^ 65) / 2 ^ 66 % 2 ^ 64) := by
  unfold tanDen
  split_ifs <;> interval_cases q <;> omega

/-- `u128::wrapping_neg` is `(2^128 - x) mod 2^128`. -/
theorem u128_wrapping_neg_spec (x : Std.U128) :
    core.num.U128.wrapping_neg x ⦃ y => y.val = (2 ^ 128 - x.val) % 2 ^ 128 ⦄ := by
  unfold core.num.U128.wrapping_neg
  rw [WP.spec_ok]
  show (-x.bv).toNat = _
  rw [BitVec.toNat_neg]; rfl

/-- The quarter turns of `m / 2^f` at 128 fractional bits are within `3/2` of
`N = ⌊m · C / 2^(64 + f)⌋` of `trig::reduce`. -/
theorem quarters_near (m f : ℕ) (hm : m < 2 ^ 64) :
    |(m : ℝ) / 2 ^ f * (2 / Real.pi) * 2 ^ 128 - (m * frac2PiN / 2 ^ (f + 64) : ℕ)| ≤ 3 / 2 := by
  have hC : |(frac2PiN : ℝ) - 2 / Real.pi * 2 ^ 192| ≤ 1 / 2 := frac_2_pi_entry
  have ⟨l, u⟩ := floor_div_near (m * frac2PiN) (2 ^ (f + 64)) (by positivity)
  push_cast at l u
  have mR : (m : ℝ) < 2 ^ 64 := by exact_mod_cast hm
  have e : (m : ℝ) / 2 ^ f * (2 / Real.pi) * 2 ^ 128 =
      m * frac2PiN / 2 ^ (f + 64) - m * (frac2PiN - 2 / Real.pi * 2 ^ 192) / 2 ^ (f + 64) := by
    rw [pow_add]; field_simp; ring
  have b : |(m : ℝ) * (frac2PiN - 2 / Real.pi * 2 ^ 192) / 2 ^ (f + 64)| ≤ 1 / 2 := by
    rw [abs_div, abs_mul, Nat.abs_cast, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (f + 64)),
      div_le_iff₀ (by positivity)]
    calc (m : ℝ) * |(frac2PiN : ℝ) - 2 / Real.pi * 2 ^ 192| ≤ 2 ^ 64 * (1 / 2) :=
          mul_le_mul mR.le hC (abs_nonneg _) (by positivity)
      _ = 1 / 2 * 2 ^ 64 := by ring
      _ ≤ 1 / 2 * 2 ^ (f + 64) := by gcongr; exact one_le_two; omega
  rw [e]
  have := abs_le.mp b
  exact abs_le.mpr ⟨by linarith only [l, this], by linarith only [u, this]⟩

/-- `|cot Δ| ≥ 2^(f+1)` for `0 < |Δ| ≤ 0.4 / 2^f`: the saturation of `trig::tan`. -/
theorem cot_big (Δ : ℝ) (f : ℕ) (h0 : Δ ≠ 0) (h : |Δ| ≤ 4 / 10 / 2 ^ f) :
    2 ^ (f + 1) ≤ |Real.cos Δ / Real.sin Δ| := by
  set a := |Δ|
  have a0 : 0 < a := abs_pos.mpr h0
  have a4 : a ≤ 4 / 10 := h.trans (div_le_self (by norm_num) (one_le_pow₀ one_le_two))
  have sn : 0 ≤ Real.sin a := Real.sin_nonneg_of_nonneg_of_le_pi a0.le (by linarith only [Real.pi_gt_three, a0, a4])
  have sa : |Real.sin Δ| = Real.sin a := by
    rcases le_or_gt 0 Δ with hd | hd
    · have ha : a = Δ := abs_of_nonneg hd
      rw [← ha, abs_of_nonneg sn]
    · have ha : a = -Δ := abs_of_neg hd
      rw [show Real.sin Δ = -Real.sin a by rw [ha, Real.sin_neg, neg_neg], abs_neg, abs_of_nonneg sn]
  have ca : |Real.cos Δ| = Real.cos a := by
    rw [show Real.cos a = Real.cos Δ from Real.cos_abs Δ]
    exact abs_of_nonneg (Real.cos_nonneg_of_mem_Icc ⟨by linarith only [Real.pi_gt_three, neg_abs_le Δ, a0, a4],
      by linarith only [Real.pi_gt_three, le_abs_self Δ, a0, a4]⟩)
  have s1 : Real.sin a ≤ a := Real.sin_le a0.le
  have s0 : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi a0 (by linarith only [Real.pi_gt_three, a0, a4])
  have c1 : 92 / 100 ≤ Real.cos a := by nlinarith only [Real.one_sub_sq_div_two_le_cos (x := a), a0, a4]
  rw [abs_div, sa, ca, le_div_iff₀ s0]
  have : 2 ^ (f + 1) * a ≤ 92 / 100 := by
    rw [pow_succ]
    have : (2 : ℝ) ^ f * a ≤ 4 / 10 := by rw [le_div_iff₀ (by positivity)] at h; linarith only [h]
    linarith only [a0, a4, this]
  nlinarith only [pow_pos (two_pos : (0 : ℝ) < 2) (f + 1), a0, sn, s1, c1, this]

/-- `Δ` with `m / 2^f = j · π/2 + Δ`, `j` odd, is not zero: `π` is irrational. -/
theorem pole_offset_ne (m f j : ℕ) (Δ : ℝ) (hj : j % 2 = 1) (h : (m : ℝ) / 2 ^ f = j * (Real.pi / 2) + Δ) :
    Δ ≠ 0 := by
  intro e
  rw [e, add_zero] at h
  have j0 : (j : ℝ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
  rw [div_eq_iff (by positivity)] at h
  apply irrational_pi.ne_rat (2 * m / (j * 2 ^ f))
  push_cast
  rw [eq_div_iff (mul_ne_zero j0 (by positivity)), h]
  ring

/-- The rounding of `cotN D` to `f ≤ 32` bits is within `½ + 2^f / 10^12` of
`cot θ · 2^f`, `θ` as in `cotN_near`. -/
theorem cot_round_near (D f : ℕ) (ε : ℝ) (hf : f ≤ 32) (h1 : 2 ^ 94 ≤ D) (h2 : D < 2 ^ 118) (he : |ε| ≤ 3 / 2) :
    |((roundHalfUp (exact (64 - f) (cotN D)) : ℤ) : ℝ) -
      Real.cos ((D + ε) * Real.pi / 2 ^ 129) / Real.sin ((D + ε) * Real.pi / 2 ^ 129) * 2 ^ f| ≤
        1 / 2 + 2 ^ f / 10 ^ 12 := by
  have r := roundHalfUp_near (exact (64 - f) (cotN D))
  have r' : |((roundHalfUp (exact (64 - f) (cotN D)) : ℤ) : ℝ) - (cotN D : ℝ) / 2 ^ (64 - f)| ≤ 1 / 2 := by
    have hq : ((exact (64 - f) (cotN D) : ℚ) : ℝ) = (cotN D : ℝ) / 2 ^ (64 - f) := by
      unfold exact; push_cast; rfl
    rw [← hq]
    have h := (Rat.cast_le (K := ℝ)).mpr r
    rwa [Rat.cast_abs, Rat.cast_sub, Rat.cast_intCast, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at h
  have c := cotN_near D ε h1 h2 he
  have p : (2 : ℝ) ^ 64 = 2 ^ (64 - f) * 2 ^ f := by rw [← pow_add, Nat.sub_add_cancel (by omega)]
  have d : |(cotN D : ℝ) / 2 ^ (64 - f) - Real.cos ((D + ε) * Real.pi / 2 ^ 129) /
      Real.sin ((D + ε) * Real.pi / 2 ^ 129) * 2 ^ f| ≤ 2 ^ f / 10 ^ 12 := by
    rw [show (cotN D : ℝ) / 2 ^ (64 - f) - Real.cos ((D + ε) * Real.pi / 2 ^ 129) /
      Real.sin ((D + ε) * Real.pi / 2 ^ 129) * 2 ^ f = ((cotN D : ℝ) - 2 ^ 64 * (Real.cos ((D + ε) * Real.pi / 2 ^ 129) /
      Real.sin ((D + ε) * Real.pi / 2 ^ 129))) / 2 ^ (64 - f) by rw [p]; field_simp,
      abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (64 - f)), div_le_iff₀ (by positivity)]
    calc _ ≤ (512 : ℝ) := c
      _ ≤ 2 ^ f / 10 ^ 12 * 2 ^ (64 - f) := by
        rw [div_mul_eq_mul_div, mul_comm, ← p]; norm_num
  exact (abs_sub_le _ _ _).trans (add_le_add r' d)

/-- What `trig::tan` returns for the angle `x` and `f` fractional bits: within
`½ + 2^f / 10^12` of `tan x · 2^f`, or the mark `±2^(2f)` of saturation when
`|tan x| ≥ 2^(f+1)`, beyond `MAX` of every type with `f` fractional bits. -/
def tanOk (f : ℕ) (x : ℝ) (r : ℤ) : Prop :=
  |(r : ℝ) - Real.tan x * 2 ^ f| ≤ 1 / 2 + 2 ^ f / 10 ^ 12 ∨
    (r.natAbs = 2 ^ (2 * f) ∧ 2 ^ (f + 1) ≤ |Real.tan x|)

theorem tanOk_neg (f : ℕ) (x : ℝ) (r : ℤ) (h : tanOk f x r) : tanOk f (-x) (-r) := by
  rcases h with h | ⟨h1, h2⟩
  · left
    rw [Real.tan_neg, Int.cast_neg, show -(r : ℝ) - -Real.tan x * 2 ^ f = -((r : ℝ) - Real.tan x * 2 ^ f) by ring,
      abs_neg]
    exact h
  · right; rw [Int.natAbs_neg, Real.tan_neg, abs_neg]; exact ⟨h1, h2⟩

/-- Away from a pole the cosine at the position `t` is at least `7.07 · 10^15 / 2^62`. -/
theorem cos_quadrant_lower (t : ℕ) (hden : 2 ^ 52 ≤ tanDen t) :
    7070 * 10 ^ 12 / 2 ^ 62 ≤ |Real.cos ((t : ℝ) / 2 ^ 62 * (Real.pi / 2))| := by
  set! p := t % 2 ^ 62
  set! q := t / 2 ^ 62
  have pl : p < 2 ^ 62 := Nat.mod_lt _ (by norm_num)
  have tq : t = q * 2 ^ 62 + p := (Nat.div_add_mod' t _).symm
  set! φ : ℝ := (p : ℝ) / 2 ^ 62 * (Real.pi / 2) with hφ
  have ang : (t : ℝ) / 2 ^ 62 * (Real.pi / 2) = φ + q * (Real.pi / 2) := by
    rw [show (t : ℝ) = ((q * 2 ^ 62 + p : ℕ) : ℝ) by rw [← tq], hφ]; push_cast; field_simp; ring
  have e7 : ((2 ^ 62 - p : ℕ) : ℝ) / 2 ^ 62 * (Real.pi / 2) = Real.pi / 2 - φ := by
    rw [Nat.cast_sub pl.le, hφ]; push_cast; field_simp; ring
  rw [ang, div_le_iff₀ (by positivity)]
  have φ0 : 0 ≤ φ := by positivity
  have φ1 : φ ≤ Real.pi / 2 := by
    have : (p : ℝ) / 2 ^ 62 ≤ 1 := by rw [div_le_one (by positivity)]; exact_mod_cast pl.le
    rw [hφ]; nlinarith only [Real.pi_pos, this]
  unfold tanDen at hden
  have one : ∀ j : ℕ, |((-1 : ℝ)) ^ ((j : ℤ))| = 1 := fun j => by rw [abs_zpow, abs_neg, abs_one, one_zpow]
  obtain ⟨j, hj | hj⟩ := Nat.even_or_odd' q
  · rw [ite_eq_left (show t / 2 ^ 62 % 2 = 0 by rw [← show q = t / 2 ^ 62 from rfl, hj]; omega)] at hden
    have L := quarter_sin_lower ((2 ^ 62 - p : ℕ) : ℝ) (by exact_mod_cast hden)
      (by exact_mod_cast Nat.sub_le _ _)
    rw [e7, Real.sin_pi_div_two_sub] at L
    rw [hj, show φ + ((2 * j : ℕ) : ℝ) * (Real.pi / 2) = φ + ((j : ℤ) : ℝ) * Real.pi by push_cast; ring,
      Real.cos_add_int_mul_pi, abs_mul, one, one_mul,
      abs_of_nonneg (Real.cos_nonneg_of_mem_Icc ⟨by linarith only [Real.pi_pos, φ0, φ1], φ1⟩)]
    exact L
  · rw [ite_eq_right (show ¬ t / 2 ^ 62 % 2 = 0 by rw [← show q = t / 2 ^ 62 from rfl, hj]; omega)] at hden
    have L := quarter_sin_lower (p : ℝ) (by exact_mod_cast hden) (by exact_mod_cast pl.le)
    rw [hj, show φ + ((2 * j + 1 : ℕ) : ℝ) * (Real.pi / 2) = (φ + Real.pi / 2) + ((j : ℤ) : ℝ) * Real.pi by
      push_cast; ring, Real.cos_add_int_mul_pi, Real.cos_add_pi_div_two, abs_mul, one, one_mul, abs_neg,
      abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi φ0 (by linarith only [φ0, φ1]))]
    exact L

/-- The bound of `tan_far_spec` at the position `t = posN m f` carries over to
the angle `m / 2^f`: the two differ by below `1.71 · 10^-19` radians mod `2π`
(`position_angle`), and with `|cos| ≥ 7.07 · 10^15 / 2^62` the tangents by
below `8 · 10^-14` (`tan_shift`). -/
theorem far_ok (m f : ℕ) (r : ℤ) (hm : m < 2 ^ 64) (hden : 2 ^ 52 ≤ tanDen (posN m f))
    (hr : |(r : ℝ) - Real.tan ((posN m f : ℝ) / 2 ^ 62 * (Real.pi / 2)) * 2 ^ f| ≤ 1 / 2 + 2 ^ f * (8 / 10 ^ 13)) :
    |(r : ℝ) - Real.tan ((m : ℝ) / 2 ^ f) * 2 ^ f| ≤ 1 / 2 + 2 ^ f / 10 ^ 12 := by
  obtain ⟨K, δ, bδ, angle⟩ := position_angle m f 0 hm
  rw [add_zero, show posN m f % 2 ^ 64 = posN m f by unfold posN; exact Nat.mod_mod _ _,
    Nat.cast_zero, zero_div, zero_mul, add_zero] at angle
  set u : ℝ := (m : ℝ) / 2 ^ f + δ * Real.pi / 2 ^ 63
  have tu : Real.tan ((posN m f : ℝ) / 2 ^ 62 * (Real.pi / 2)) = Real.tan u := by
    rw [angle]
    have := Real.tan_add_int_mul_pi u (-(2 * K : ℤ))
    rw [← this]; congr 1; push_cast; ring
  have cu : Real.cos ((posN m f : ℝ) / 2 ^ 62 * (Real.pi / 2)) = Real.cos u := by
    rw [angle, Real.cos_sub_nat_mul_two_pi]
  have cl := cos_quadrant_lower (posN m f) hden
  rw [cu] at cl
  have p2 := Real.pi_lt_d2
  have he : |δ * Real.pi / 2 ^ 63| ≤ 171 / 10 ^ 21 := by
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 63),
      div_le_iff₀ (by positivity)]
    calc |δ| * Real.pi ≤ (1 / 2 + 1 / 2 ^ 66 + 1 / 2 ^ 67) * 3.15 :=
          mul_le_mul bδ p2.le Real.pi_pos.le (by positivity)
      _ ≤ 171 / 10 ^ 21 * 2 ^ 63 := by norm_num
  have sh := tan_shift u (m / 2 ^ f) (δ * Real.pi / 2 ^ 63) _ _ rfl cl he (by norm_num)
  have sh' : |Real.tan u - Real.tan ((m : ℝ) / 2 ^ f)| ≤ 8 / 10 ^ 14 :=
    sh.trans (by norm_num)
  rw [tu] at hr
  have : |Real.tan u * 2 ^ f - Real.tan ((m : ℝ) / 2 ^ f) * 2 ^ f| ≤ 2 ^ f * (8 / 10 ^ 14) := by
    rw [← sub_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ f), mul_comm]; gcongr
  calc _ ≤ |(r : ℝ) - Real.tan u * 2 ^ f| + |Real.tan u * 2 ^ f - Real.tan ((m : ℝ) / 2 ^ f) * 2 ^ f| :=
        abs_sub_le _ _ _
    _ ≤ 1 / 2 + 2 ^ f * (8 / 10 ^ 13) + 2 ^ f * (8 / 10 ^ 14) := add_le_add hr this
    _ ≤ 1 / 2 + 2 ^ f / 10 ^ 12 := by
        have : (0 : ℝ) ≤ 2 ^ f := by positivity
        nlinarith only [this]

/-- The angle `m / 2^f` is `j · π/2` plus `(fr + ε) · π / 2^129`, `j` and `fr` the
quarter turns `⌊N / 2^128⌋` and the fraction `N mod 2^128` of `trig::reduce`,
`|ε| ≤ 3/2` (`quarters_near`). -/
theorem angle_split (m f : ℕ) (hm : m < 2 ^ 64) :
    ∃ ε : ℝ, |ε| ≤ 3 / 2 ∧ (m : ℝ) / 2 ^ f =
      ((m * frac2PiN / 2 ^ (f + 64) / 2 ^ 128 : ℕ) : ℝ) * (Real.pi / 2) +
        (((m * frac2PiN / 2 ^ (f + 64) % 2 ^ 128 : ℕ) : ℝ) + ε) * Real.pi / 2 ^ 129 := by
  have h := quarters_near m f hm
  set N := m * frac2PiN / 2 ^ (f + 64)
  refine ⟨(m : ℝ) / 2 ^ f * (2 / Real.pi) * 2 ^ 128 - N, h, ?_⟩
  have e : (N : ℝ) = ((N / 2 ^ 128 : ℕ) : ℝ) * 2 ^ 128 + ((N % 2 ^ 128 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod' N (2 ^ 128)).symm
  have hX : (m : ℝ) / 2 ^ f * (2 / Real.pi) * 2 ^ 128 * Real.pi / 2 ^ 129 = m / 2 ^ f := by
    field_simp
  linear_combination (-1 : ℝ) * hX + (Real.pi / 2 ^ 129) * e

/-- Saturation near a pole: with `m / 2^f = j · π/2 + Δ`, `j` odd and
`|Δ| ≤ 0.4 / 2^f`, the mark `±2^(2f)` is what `tanOk` allows. -/
theorem sat_ok (m f j : ℕ) (Δ : ℝ) (r : ℤ) (hj : j % 2 = 1) (hx : (m : ℝ) / 2 ^ f = j * (Real.pi / 2) + Δ)
    (hΔ : |Δ| ≤ 4 / 10 / 2 ^ f) (hr : r.natAbs = 2 ^ (2 * f)) : tanOk f ((m : ℝ) / 2 ^ f) r := by
  right
  refine ⟨hr, ?_⟩
  rw [hx, show (j : ℝ) * (Real.pi / 2) + Δ = Δ + j * (Real.pi / 2) by ring, tan_quadrant,
    ite_eq_right (by omega), abs_neg]
  exact cot_big Δ f (pole_offset_ne m f j Δ hj hx) hΔ

/-- `|(D + ε) · π / 2^129| ≤ 0.4 / 2^f` for `D < 2^(126-f)`, `|ε| ≤ 3/2`, `f ≤ 32`. -/
theorem sat_offset (D f : ℕ) (ε : ℝ) (hf : f ≤ 32) (hD : D < 2 ^ (126 - f)) (he : |ε| ≤ 3 / 2) :
    |((D : ℝ) + ε) * Real.pi / 2 ^ 129| ≤ 4 / 10 / 2 ^ f := by
  have p2 := Real.pi_lt_d2
  have Dl : (D : ℝ) + 1 ≤ 2 ^ (126 - f) := by exact_mod_cast hD
  have P : (2 : ℝ) ^ 129 = 2 ^ (126 - f) * 2 ^ f * 8 := by
    rw [← pow_add, Nat.sub_add_cancel (by omega)]; norm_num
  have pf : (2 : ℝ) ^ f ≤ 2 ^ 32 := pow_le_pow_right₀ one_le_two hf
  have ⟨e1, e2⟩ := abs_le.mp he
  rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 129),
    div_le_div_iff₀ (by positivity) (by positivity), P]
  have hDe : |(D : ℝ) + ε| ≤ 2 ^ (126 - f) + 1 / 2 := by
    have : (0 : ℝ) ≤ D := Nat.cast_nonneg _
    exact abs_le.mpr ⟨by linarith only [Dl, e1], by linarith only [Dl, e2]⟩
  have A : (0 : ℝ) < 2 ^ (126 - f) := by positivity
  have : (2 : ℝ) ^ 94 ≤ 2 ^ (126 - f) := pow_le_pow_right₀ one_le_two (by omega)
  calc |(D : ℝ) + ε| * Real.pi * 2 ^ f ≤ (2 ^ (126 - f) + 1 / 2) * 3.15 * 2 ^ f := by gcongr
    _ ≤ 4 / 10 * (2 ^ (126 - f) * 2 ^ f * 8) := by nlinarith only [P, pf]

/-- The cotangent branch in an odd quadrant: `m / 2^f = j · π/2 + θ`,
`θ = (D + ε) · π / 2^129`, `tan = -cot θ`, and `trig::tan` returns `-r`. -/
theorem cot_ok_odd (m f j D : ℕ) (ε : ℝ) (r : ℤ) (hf : f ≤ 32) (hj : j % 2 = 1) (h1 : 2 ^ 94 ≤ D)
    (h2 : D < 2 ^ 118) (he : |ε| ≤ 3 / 2)
    (hx : (m : ℝ) / 2 ^ f = j * (Real.pi / 2) + ((D : ℝ) + ε) * Real.pi / 2 ^ 129)
    (hr : r = roundHalfUp (exact (64 - f) (cotN D))) : tanOk f ((m : ℝ) / 2 ^ f) (-r) := by
  left
  rw [hx, show (j : ℝ) * (Real.pi / 2) + ((D : ℝ) + ε) * Real.pi / 2 ^ 129 =
      ((D : ℝ) + ε) * Real.pi / 2 ^ 129 + j * (Real.pi / 2) by ring, tan_quadrant, ite_eq_right (by omega),
    Int.cast_neg,
    show -(r : ℝ) - -(Real.cos (((D : ℝ) + ε) * Real.pi / 2 ^ 129) / Real.sin (((D : ℝ) + ε) * Real.pi / 2 ^ 129)) * 2 ^ f =
      -((r : ℝ) - Real.cos (((D : ℝ) + ε) * Real.pi / 2 ^ 129) / Real.sin (((D : ℝ) + ε) * Real.pi / 2 ^ 129) * 2 ^ f) by
      ring, abs_neg, hr]
  exact cot_round_near D f ε hf h1 h2 he

/-- The cotangent branch in an even quadrant: `m / 2^f = j · π/2 - θ`,
`θ = (D + ε) · π / 2^129`, `tan = cot θ`, and `trig::tan` returns `r`. -/
theorem cot_ok_even (m f j D : ℕ) (ε : ℝ) (r : ℤ) (hf : f ≤ 32) (hj : j % 2 = 1) (h1 : 2 ^ 94 ≤ D)
    (h2 : D < 2 ^ 118) (he : |ε| ≤ 3 / 2)
    (hx : (m : ℝ) / 2 ^ f = j * (Real.pi / 2) - ((D : ℝ) + ε) * Real.pi / 2 ^ 129)
    (hr : r = roundHalfUp (exact (64 - f) (cotN D))) : tanOk f ((m : ℝ) / 2 ^ f) r := by
  left
  rw [hx, show (j : ℝ) * (Real.pi / 2) - ((D : ℝ) + ε) * Real.pi / 2 ^ 129 =
      -(((D : ℝ) + ε) * Real.pi / 2 ^ 129) + j * (Real.pi / 2) by ring, tan_quadrant, ite_eq_right (by omega),
    Real.cos_neg, Real.sin_neg,
    div_neg, neg_neg, hr]
  exact cot_round_near D f ε hf h1 h2 he

/-- `trig::NEAR_POLE` is `2^118`. -/
theorem near_pole_spec : fulcrum.trig.NEAR_POLE ⦃ x => x.val = 2 ^ 118 ⦄ := by
  unfold fulcrum.trig.NEAR_POLE
  refine WP.spec_mono (shl_i32_spec 1#u128 118#i32 118 rfl (by rw [show UScalarTy.U128.numBits = 128 from rfl]; norm_num)
    (by rw [show UScalarTy.U128.numBits = 128 from rfl, lit_val]; norm_num)) fun x hx => ?_
  rw [hx, lit_val, one_mul]

/-- On the code: the branch of `trig::tan` away from a pole, from the quadrant and
the fraction of `trig::reduce` of `m`, when they are at least `2^-10` quarter
turns from a pole: `tanOk` for `m / 2^f`, below `2^100`. -/
theorem tan_far_case (m q : Std.U64) (fr : Std.U128) (f : Std.U32) (hf : f.val ≤ 32)
    (hq : q.val = m.val * frac2PiN / 2 ^ (f.val + 64) / 2 ^ 128 % 4)
    (hfr : fr.val = m.val * frac2PiN / 2 ^ (f.val + 64) % 2 ^ 128)
    (hc : (q.val % 2 = 1 ∧ 2 ^ 118 ≤ fr.val) ∨ (q.val % 2 = 0 ∧ fr.val ≤ 2 ^ 128 - 2 ^ 118)) :
    (do
      let t ← fulcrum.trig.position q fr
      let i3 ← 1#u64 <<< fulcrum.tables.trig.FRAC
      let i4 ← i3 - 1#u64
      let p ← lift (t &&& i4)
      let i5 ← fulcrum.trig.sin_quarter p fulcrum.tables.trig.FRAC
      let a ← lift (UScalar.cast .U128 i5)
      let i6 ← i3 - p
      let i7 ← fulcrum.trig.sin_quarter i6 fulcrum.tables.trig.FRAC
      let b ← lift (UScalar.cast .U128 i7)
      let i8 ← t >>> fulcrum.tables.trig.FRAC
      let i9 ← lift (i8 &&& 1#u64)
      let (n, d1, negative) ←
        if i9 = 0#u64
        then ok (a, b, false)
        else ok (b, a, true)
      let i10 ← f + 1#u32
      let i11 ← n <<< i10
      let i12 ← i11 / d1
      let i13 ← lift (UScalar.hcast .I128 i12)
      let r ← fulcrum.kernel.shr_round i13 1#u32
      if negative
      then -. r
      else ok r) ⦃ r => tanOk f.val ((m.val : ℝ) / 2 ^ f.val) r.val ∧ |r.val| < 2 ^ 100 ⦄ := by
  have q4 : q.val < 4 := by rw [hq]; exact Nat.mod_lt _ (by norm_num)
  refine WP.spec_bind (position_spec q fr q4) fun t ht => ?_
  have tp : t.val = posN m.val f.val := by
    rw [ht, hq, hfr, posN, show (2 : ℕ) ^ 130 = 2 ^ 128 * 4 by norm_num, Nat.mod_mul, mul_comm (2 ^ 128),
      add_comm (_ * 2 ^ 128)]
  have hden : 2 ^ 52 ≤ tanDen t.val := by
    rw [ht]; exact tanDen_far q.val fr.val q4 (by rw [hfr]; exact Nat.mod_lt _ (by norm_num)) hc
  refine WP.spec_mono (tan_far_spec t f hf hden) fun r ⟨hr, hl⟩ => ⟨?_, hl.trans (by norm_num)⟩
  left
  rw [tp] at hr hden
  exact (far_ok m.val f.val r.val m.bv.isLt hden (hr.trans_eq (by ring))).trans_eq (by ring)

/-- The rounded cotangent of `trig::tan` near a pole is in `[0, 2^98]`. -/
theorem round_cot_bounds (D f : ℕ) (h1 : 2 ^ 94 ≤ D) :
    0 ≤ roundHalfUp (exact (64 - f) (cotN D)) ∧ roundHalfUp (exact (64 - f) (cotN D)) ≤ 2 ^ 98 := by
  have cl : cotN D < 2 ^ 98 := by
    unfold cotN
    have : frac2PiN / D < 2 ^ 98 := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      calc frac2PiN < 2 ^ 192 := frac2PiN_lt
        _ = 2 ^ 98 * 2 ^ 94 := by norm_num
        _ ≤ 2 ^ 98 * D := Nat.mul_le_mul_left _ h1
    omega
  have e0 : (0 : ℚ) ≤ exact (64 - f) (cotN D) := by unfold exact; positivity
  have e1 : exact (64 - f) (cotN D) ≤ 2 ^ 98 - 1 := by
    unfold exact
    rw [div_le_iff₀ (by positivity)]
    have : ((cotN D : ℤ) : ℚ) ≤ 2 ^ 98 - 1 := by
      have : cotN D + 1 ≤ 2 ^ 98 := cl
      have : ((cotN D : ℕ) : ℚ) + 1 ≤ 2 ^ 98 := by exact_mod_cast this
      push_cast; linarith only [this]
    nlinarith only [one_le_pow₀ (one_le_two : (1 : ℚ) ≤ 2) (n := 64 - f), this]
  unfold roundHalfUp
  constructor
  · exact Int.floor_nonneg.mpr (by linarith only [e0])
  · have := Int.floor_le (exact (64 - f) (cotN D) + 1 / 2)
    have : ((⌊exact (64 - f) (cotN D) + 1 / 2⌋ : ℤ) : ℚ) < 2 ^ 98 + 1 := by linarith only [e1, this]
    have : ⌊exact (64 - f) (cotN D) + 1 / 2⌋ < 2 ^ 98 + 1 := by exact_mod_cast this
    omega

/-- L4 on the code: `trig::tan` with `f ≤ 32` never fails and returns, for the
angle `raw / 2^f`, a value within `½ + 2^f / 10^12` of `tan · 2^f`, or the mark
`±2^(2f)` of saturation when `|tan| ≥ 2^(f+1)` (`tanOk`). -/
theorem tan_spec (raw : Std.I64) (f : Std.U32) (hf : f.val ≤ 32) :
    fulcrum.trig.tan raw f ⦃ r => tanOk f.val ((raw.val : ℝ) / 2 ^ f.val) r.val ⦄ := by
  unfold fulcrum.trig.tan
  refine WP.spec_bind (I64_unsigned_abs_spec raw) fun m hm => ?_
  refine WP.spec_bind (reduce_spec m f (by omega)) fun qr ⟨hq, hfr⟩ => ?_
  obtain ⟨q, fr⟩ := qr
  dsimp only at hq hfr
  obtain ⟨ε, he, hx⟩ := angle_split m.val f.val m.bv.isLt
  set N := m.val * frac2PiN / 2 ^ (f.val + 64) with hN
  rw [← hfr] at hx
  refine WP.spec_bind (Pₘ := fun i1 : Std.U64 => i1.val = q.val % 2)
    ((WP.spec_ok _).mpr (by rw [UScalar.val_and, lit_val, Nat.and_one_is_mod])) fun i1 i1v => ?_
  have jq : N / 2 ^ 128 % 2 = q.val % 2 := by rw [hq]; omega
  have frl : fr.val < 2 ^ 128 := fr.bv.isLt
  refine WP.spec_bind (Pₘ := fun d : Std.U128 =>
    d.val = if q.val % 2 = 1 then fr.val else (2 ^ 128 - fr.val) % 2 ^ 128) ?_ fun d hd => ?_
  · by_cases h1 : i1 = 1#u64
    · have : q.val % 2 = 1 := by rw [← i1v, h1]; rfl
      rw [ite_eq_left h1, WP.spec_ok, ite_eq_left this]
    · have : ¬ q.val % 2 = 1 := fun e => h1 (UScalar.eq_of_val_eq (by rw [i1v, e]; rfl))
      rw [ite_eq_right h1, ite_eq_right this]
      exact u128_wrapping_neg_spec fr
  refine WP.spec_bind near_pole_spec fun i2 h2 => ?_
  refine WP.spec_bind (Pₘ := fun mm : Std.I128 =>
    tanOk f.val ((m.val : ℝ) / 2 ^ f.val) mm.val ∧ |mm.val| < 2 ^ 100) ?_ fun mm ⟨hok, hl⟩ => ?_
  · have pf : (2 : ℤ) ^ (2 * f.val) ≤ 2 ^ 64 := pow_le_pow_right₀ (by norm_num) (by omega)
    have sat_abs : ∀ r : Std.I128, r.val = 2 ^ (2 * f.val) → |r.val| < 2 ^ 100 := fun r hr => by
      rw [hr, abs_of_nonneg (by positivity)]; exact pf.trans_lt (by norm_num)
    by_cases hnear : d < i2
    · have hd2 : d.val < 2 ^ 118 := h2 ▸ hnear
      rw [ite_eq_left hnear]
      by_cases h1 : i1 = 1#u64
      · have qo : q.val % 2 = 1 := by rw [← i1v, h1]; rfl
        rw [ite_eq_left qo] at hd
        rw [ite_eq_left h1]
        refine tan_near_spec d f hf hd2 _ _ fun r hsat hcot => ?_
        rw [ite_eq_left h1]
        have jo : N / 2 ^ 128 % 2 = 1 := by rw [jq, qo]
        by_cases hs : d.val < 2 ^ (126 - f.val)
        · have hr := hsat hs
          refine WP.spec_mono (IScalar.neg_step _ (fun e => ?_)) fun r' hr' => ?_
          · rw [e, IScalar.min_def, IScalarTy.I128_numBits_eq] at hr
            have : (0 : ℤ) ≤ 2 ^ (2 * f.val) := by positivity
            omega
          · rw [hr']
            refine ⟨sat_ok m.val f.val _ (((fr.val : ℝ) + ε) * Real.pi / 2 ^ 129) _ jo hx ?_
              (by rw [Int.natAbs_neg, hr]; rfl), ?_⟩
            · rw [hd] at hs; exact sat_offset fr.val f.val ε hf hs he
            · rw [abs_neg]; exact sat_abs r hr
        · have hr := hcot (not_lt.mp hs)
          have d94 : 2 ^ 94 ≤ d.val := (Nat.pow_le_pow_right two_pos (by omega)).trans (not_lt.mp hs)
          have ⟨r0, r1⟩ := round_cot_bounds d.val f.val d94
          rw [← hr] at r0 r1
          refine WP.spec_mono (IScalar.neg_step _ (fun e => ?_)) fun r' hr' => ?_
          · rw [e, IScalar.min_def, IScalarTy.I128_numBits_eq] at r0; norm_num at r0
          · rw [hr']
            refine ⟨?_, by rw [abs_neg, abs_of_nonneg r0]; exact r1.trans_lt (by norm_num)⟩
            rw [hd] at hr d94 hd2
            exact cot_ok_odd m.val f.val _ fr.val ε r.val hf jo d94 hd2 he hx hr
      · have qe : ¬ q.val % 2 = 1 := fun e => h1 (UScalar.eq_of_val_eq (by rw [i1v, e]; rfl))
        rw [ite_eq_right qe] at hd
        rw [ite_eq_right h1]
        by_cases hz : (fr != 0#u128) = true
        · have fz : fr.val ≠ 0 := fun e => (bne_iff_ne.mp hz) (UScalar.eq_of_val_eq (by rw [e]; rfl))
          rw [Nat.mod_eq_of_lt (by omega)] at hd
          rw [ite_eq_left hz]
          refine tan_near_spec d f hf hd2 _ _ fun r hsat hcot => ?_
          rw [ite_eq_right h1, WP.spec_ok]
          have jo : (N / 2 ^ 128 + 1) % 2 = 1 := by rw [Nat.add_mod, jq]; omega
          have hx' : (m.val : ℝ) / 2 ^ f.val = ((N / 2 ^ 128 + 1 : ℕ) : ℝ) * (Real.pi / 2) -
              ((d.val : ℝ) + -ε) * Real.pi / 2 ^ 129 := by
            rw [hx, hd, Nat.cast_sub frl.le]; push_cast; ring
          by_cases hs : d.val < 2 ^ (126 - f.val)
          · have hr := hsat hs
            refine ⟨sat_ok m.val f.val _ (-(((d.val : ℝ) + -ε) * Real.pi / 2 ^ 129)) _ jo (hx'.trans (by ring)) ?_
              (by rw [hr]; rfl), sat_abs r hr⟩
            rw [abs_neg]; exact sat_offset d.val f.val (-ε) hf hs (by rw [abs_neg]; exact he)
          · have hr := hcot (not_lt.mp hs)
            have d94 : 2 ^ 94 ≤ d.val := (Nat.pow_le_pow_right two_pos (by omega)).trans (not_lt.mp hs)
            have ⟨r0, r1⟩ := round_cot_bounds d.val f.val d94
            rw [← hr] at r0 r1
            exact ⟨cot_ok_even m.val f.val _ d.val (-ε) r.val hf jo d94 hd2 (by rw [abs_neg]; exact he) hx' hr,
              by rw [abs_of_nonneg r0]; exact r1.trans_lt (by norm_num)⟩
        · have fz : fr.val = 0 := by
            by_contra hc; exact hz (bne_iff_ne.mpr fun e => hc (by rw [e]; rfl))
          rw [ite_eq_right hz]
          exact tan_far_case m q fr f hf hq hfr (Or.inr ⟨by omega, by rw [fz]; norm_num⟩)
    · have hd2 : ¬ d.val < 2 ^ 118 := h2 ▸ hnear
      rw [ite_eq_right hnear]
      refine tan_far_case m q fr f hf hq hfr ?_
      by_cases qo : q.val % 2 = 1
      · rw [ite_eq_left qo] at hd; exact Or.inl ⟨qo, by omega⟩
      · rw [ite_eq_right qo] at hd
        refine Or.inr ⟨by omega, ?_⟩
        rcases Nat.eq_zero_or_pos fr.val with h0 | h0
        · rw [h0] at hd; norm_num at hd; omega
        · rw [Nat.mod_eq_of_lt (by omega)] at hd; omega
  · have mr := natAbs_real raw.val
    rw [← hm] at mr
    by_cases hn : raw < 0#i64
    · have hn' : raw.val < 0 := hn
      rw [ite_eq_left hn]
      refine WP.spec_mono (IScalar.neg_step _ (fun e => ?_)) fun r hr => ?_
      · rw [e, IScalar.min_def, IScalarTy.I128_numBits_eq] at hl; norm_num at hl
      · rw [hr]
        rw [ite_eq_left hn'] at mr
        have : (raw.val : ℝ) / 2 ^ f.val = -((m.val : ℝ) / 2 ^ f.val) := by rw [mr]; ring
        rw [this]
        exact tanOk_neg _ _ _ hok
    · have hn' : ¬ raw.val < 0 := hn
      rw [ite_eq_right hn, WP.spec_ok]
      rw [ite_eq_right hn'] at mr
      rw [← mr]
      exact hok

end Fulcrum

end
