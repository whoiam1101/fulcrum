module

public import Fulcrum.L4.Turns

/-!
# L4: `trig::reduce`, `position`, `sin`, `cos`, `sin_cos` (INTERNALS §3.12)

On the code extracted by Aeneas: `reduce(m, f)` multiplies `m` exactly by the
192 bits `C` of `2/π` in three `u64 × u64 → u128` products with carries and
returns `N = ⌊m · C / 2^(64 + f)⌋`, the quarter turns at 128 fractional bits,
as the quadrant `⌊N / 2^128⌋ mod 4` and the fraction `N mod 2^128`
(`reduce_spec`); `position` rounds them to 62 bits, wrapping mod 4
(`position_spec`). The position differs from `m / 2^f` radians, mod `2π`, by
less than `½ · 2^-62` quarters of rounding, `2^-66` of the floor and `2^-67` of
`C`, below `0.79 · 2^-62` in the sine (`position_near`). With the `6.1` units of
`sin_position` (`Turns.lean`), `sin`, `cos` and `sin_cos` with `f ≤ 62` never fail
and are within `½ + 6.9 / 2^(62 - f)` of the sine and cosine of `raw / 2^f`,
under `½ + 2^-27` ulp for `f ≤ 32`: `cos` reads a quarter turn further, and the
sign of `sin` is set after the rounding of `|raw|`.
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace Fulcrum

set_option maxRecDepth 10000

/-- `2/π · 2^192` rounded to nearest, the three words of `tables::trig::FRAC_2_PI`. -/
def frac2PiN : ℕ :=
  (fulcrum.tables.trig.FRAC_2_PI.val[0]!).val * 2 ^ 128 +
    (fulcrum.tables.trig.FRAC_2_PI.val[1]!).val * 2 ^ 64 + (fulcrum.tables.trig.FRAC_2_PI.val[2]!).val

/-- A word `i < 3` of `FRAC_2_PI`, read by `index_usize`. -/
theorem frac_2_pi_word_spec (i : Std.Usize) (hi : i.val < 3) :
    Array.index_usize fulcrum.tables.trig.FRAC_2_PI i ⦃ x =>
      x.val = (fulcrum.tables.trig.FRAC_2_PI.val[i.val]!).val ⦄ := by
  have hl : i.val < fulcrum.tables.trig.FRAC_2_PI.length := by
    rw [Array.length, fulcrum.tables.trig.FRAC_2_PI.property]; exact hi
  refine WP.spec_mono (Array.index_usize_spec _ i hl) fun x hx => ?_
  rw [hx, getElem!_pos fulcrum.tables.trig.FRAC_2_PI.val i.val
    (show i.val < fulcrum.tables.trig.FRAC_2_PI.val.length from hl)]

/-- The words of the exact product `m · (a · 2^128 + b · 2^64 + c)` as `trig::reduce`
adds them: `t1`, `t2` and `hi` give the top 128 bits and the next word. -/
theorem reduce_words (m a b c : ℕ) (hm : m < 2 ^ 64) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hc : c < 2 ^ 64) :
    let t1 := m * c / 2 ^ 64 + m * b % 2 ^ 64
    let t2 := t1 / 2 ^ 64 + m * b / 2 ^ 64 + m * a % 2 ^ 64
    let hi := t2 / 2 ^ 64 + m * a / 2 ^ 64
    m * (a * 2 ^ 128 + b * 2 ^ 64 + c) / 2 ^ 128 = hi * 2 ^ 64 + t2 % 2 ^ 64 ∧
      m * (a * 2 ^ 128 + b * 2 ^ 64 + c) / 2 ^ 64 % 2 ^ 64 = t1 % 2 ^ 64 ∧ hi < 2 ^ 64 := by
  intro t1 t2 hi
  simp only [t1, t2, hi]
  have e : m * (a * 2 ^ 128 + b * 2 ^ 64 + c) = m * a * 2 ^ 128 + m * b * 2 ^ 64 + m * c := by ring
  have top : m * (a * 2 ^ 128 + b * 2 ^ 64 + c) < 2 ^ 256 := by
    calc m * (a * 2 ^ 128 + b * 2 ^ 64 + c) < 2 ^ 64 * 2 ^ 192 :=
          Nat.mul_lt_mul_of_lt_of_le hm (by omega) (by positivity)
      _ = 2 ^ 256 := by norm_num
  rw [e] at top ⊢
  generalize m * a = w2 at *
  generalize m * b = w1 at *
  generalize m * c = w0 at *
  norm_num at top ⊢
  omega

/-- The product of two values below `2^64` fits `u128`. -/
theorem mul_le_u128 {a b : ℕ} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : a * b ≤ UScalar.max .U128 := by
  rw [U128_max_val]
  calc a * b ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (Nat.le_pred_of_lt ha) (Nat.le_pred_of_lt hb)
    _ ≤ 2 ^ 128 - 1 := by norm_num

/-- A `u64` widened to `u128` keeps its value. -/
theorem cast_u128_val (x : Std.U64) : (UScalar.cast .U128 x).val = x.val :=
  UScalar.cast_val_mod_pow_greater_numBits_eq _ _ (Nat.le_of_ble_eq_true rfl)

/-- A `u128` narrowed to `u64` keeps its low word. -/
theorem cast_u64_val (x : Std.U128) : (UScalar.cast .U64 x).val = x.val % 2 ^ 64 := by
  rw [UScalar.cast_val_eq, UScalarTy.U64_numBits_eq]

/-- `(a · c + y) mod (b · c) = (a mod b) · c + y` for `y < c`. -/
theorem mul_add_mod_mul (a b c y : ℕ) (hy : y < c) : (a * c + y) % (b * c) = a % b * c + y := by
  rcases Nat.eq_zero_or_pos b with hb | hb
  · rw [hb, Nat.mod_zero, zero_mul, Nat.mod_zero]
  have e : a * c + y = b * c * (a / b) + (a % b * c + y) := by
    conv_lhs => rw [← Nat.div_add_mod a b]
    ring
  have lt : a % b * c + y < b * c :=
    calc a % b * c + y < a % b * c + c := by omega
      _ = (a % b + 1) * c := by ring
      _ ≤ b * c := Nat.mul_le_mul_right _ (Nat.mod_lt a hb)
  rw [e, Nat.mul_add_mod, Nat.mod_eq_of_lt lt]

/-- The fraction of `trig::reduce` on naturals: the top 128 bits `P / 2^128`
shifted left by `64 - f`, wrapping, and the next word shifted right by `f` are
`⌊P / 2^(64 + f)⌋ mod 2^128`. -/
theorem frac_words (P f : ℕ) (hf : f ≤ 64) :
    (P / 2 ^ 128 * 2 ^ (64 - f)) % 2 ^ 128 ||| P / 2 ^ 64 % 2 ^ 64 / 2 ^ f = P / 2 ^ (f + 64) % 2 ^ 128 := by
  have e1 : P / 2 ^ 64 = P / 2 ^ 128 * 2 ^ 64 + P / 2 ^ 64 % 2 ^ 64 := by
    rw [show (2 : ℕ) ^ 128 = 2 ^ 64 * 2 ^ 64 by norm_num, ← Nat.div_div_eq_div_mul]
    exact (Nat.div_add_mod' _ _).symm
  rw [show (2 : ℕ) ^ (f + 64) = 2 ^ 64 * 2 ^ f by rw [← pow_add, add_comm], ← Nat.div_div_eq_div_mul]
  have rl := Nat.mod_lt (P / 2 ^ 64) (Nat.two_pow_pos 64)
  generalize P / 2 ^ 64 % 2 ^ 64 = r at e1 rl ⊢
  generalize P / 2 ^ 128 = A at e1 ⊢
  rw [e1]
  have yl : r / 2 ^ f < 2 ^ (64 - f) := by
    rwa [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add, Nat.sub_add_cancel hf]
  have q : (A * 2 ^ 64 + r) / 2 ^ f = A * 2 ^ (64 - f) + r / 2 ^ f := by
    rw [show A * 2 ^ 64 = A * 2 ^ (64 - f) * 2 ^ f by rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hf],
      add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), add_comm]
  have c : (2 : ℕ) ^ 128 = 2 ^ (64 + f) * 2 ^ (64 - f) := by rw [← pow_add]; congr 1; omega
  rw [q, c, Nat.mul_mod_mul_right, mul_add_mod_mul _ _ _ _ yl, mul_comm (A % _),
    Nat.two_pow_add_eq_or_of_lt yl]

/-- On the code: `trig::reduce(m, f)` with `f ≤ 62` never fails and returns the
quarter turns `N = ⌊m · C / 2^(64 + f)⌋` of the exact product with `C` of
`FRAC_2_PI`: the quadrant `⌊N / 2^128⌋ mod 4` and the 128 bits of the fraction
`N mod 2^128`. -/
theorem reduce_spec (m : Std.U64) (f : Std.U32) (hf : f.val ≤ 62) :
    fulcrum.trig.reduce m f ⦃ r =>
      r.1.val = m.val * frac2PiN / 2 ^ (f.val + 64) / 2 ^ 128 % 4 ∧
        r.2.val = m.val * frac2PiN / 2 ^ (f.val + 64) % 2 ^ 128 ⦄ := by
  unfold fulcrum.trig.reduce
  have hm : m.val < 2 ^ 64 := m.bv.isLt
  rw [lift, bind_ok]
  refine WP.spec_bind (frac_2_pi_word_spec 2#usize (by decide)) fun x2 h2 => ?_
  rw [lift, bind_ok]
  refine WP.spec_bind (UScalar.mul_spec (x := UScalar.cast .U128 m) (y := UScalar.cast .U128 x2)
    (by rw [cast_u128_val, cast_u128_val]; exact mul_le_u128 hm x2.bv.isLt)) fun w0 hw0 => ?_
  refine WP.spec_bind (frac_2_pi_word_spec 1#usize (by decide)) fun x1 h1 => ?_
  rw [lift, bind_ok]
  refine WP.spec_bind (UScalar.mul_spec (x := UScalar.cast .U128 m) (y := UScalar.cast .U128 x1)
    (by rw [cast_u128_val, cast_u128_val]; exact mul_le_u128 hm x1.bv.isLt)) fun w1 hw1 => ?_
  refine WP.spec_bind (frac_2_pi_word_spec 0#usize (by decide)) fun x0 h0 => ?_
  rw [lift, bind_ok]
  refine WP.spec_bind (UScalar.mul_spec (x := UScalar.cast .U128 m) (y := UScalar.cast .U128 x0)
    (by rw [cast_u128_val, cast_u128_val]; exact mul_le_u128 hm x0.bv.isLt)) fun w2 hw2 => ?_
  rw [cast_u128_val, cast_u128_val] at hw0 hw1 hw2
  have b0 : w0.val < 2 ^ 128 := w0.bv.isLt
  have b1 : w1.val < 2 ^ 128 := w1.bv.isLt
  have b2 : w2.val < 2 ^ 128 := w2.bv.isLt
  have n128 : UScalarTy.U128.numBits = 128 := rfl
  have mx : UScalar.max .U128 = 2 ^ 128 - 1 := U128_max_val
  refine WP.spec_bind (shr_i32_spec w0 64#i32 64 rfl (by rw [n128]; norm_num)) fun i6 h6 => ?_
  rw [lift, bind_ok, lift, bind_ok]
  refine WP.spec_bind (UScalar.add_spec (x := i6) (y := UScalar.cast .U128 (UScalar.cast .U64 w1))
    (by rw [cast_u128_val, cast_u64_val, h6, mx]; omega)) fun t1 ht1 => ?_
  rw [cast_u128_val, cast_u64_val, h6] at ht1
  refine WP.spec_bind (shr_i32_spec t1 64#i32 64 rfl (by rw [n128]; norm_num)) fun i9 h9 => ?_
  refine WP.spec_bind (shr_i32_spec w1 64#i32 64 rfl (by rw [n128]; norm_num)) fun i10 h10 => ?_
  refine WP.spec_bind (UScalar.add_spec (x := i9) (y := i10) (by rw [h9, h10, mx]; omega)) fun i11 h11 => ?_
  rw [lift, bind_ok, lift, bind_ok]
  refine WP.spec_bind (UScalar.add_spec (x := i11) (y := UScalar.cast .U128 (UScalar.cast .U64 w2))
    (by rw [cast_u128_val, cast_u64_val, h11, h9, h10, mx]; omega)) fun t2 ht2 => ?_
  rw [cast_u128_val, cast_u64_val, h11, h9, h10] at ht2
  refine WP.spec_bind (shr_i32_spec t2 64#i32 64 rfl (by rw [n128]; norm_num)) fun i14 h14 => ?_
  refine WP.spec_bind (shr_i32_spec w2 64#i32 64 rfl (by rw [n128]; norm_num)) fun i15 h15 => ?_
  refine WP.spec_bind (UScalar.add_spec (x := i14) (y := i15) (by rw [h14, h15, mx]; omega)) fun i16 h16 => ?_
  rw [h14, h15] at h16
  obtain ⟨wt, wm, wh⟩ := reduce_words m.val x0.val x1.val x2.val hm x0.bv.isLt x1.bv.isLt x2.bv.isLt
  rw [hw0, hw1] at ht1
  rw [hw1, hw2] at ht2
  rw [hw2] at h16
  rw [← ht1, ← ht2, ← h16] at wt
  rw [← ht1] at wm
  rw [← ht1, ← ht2, ← h16] at wh
  refine WP.spec_bind (shl_i32_spec i16 64#i32 64 rfl (by rw [n128]; norm_num)
    (by rw [n128]; calc i16.val * 2 ^ 64 < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul_of_pos_right wh (by positivity)
          _ = 2 ^ 128 := by norm_num)) fun i17 h17 => ?_
  rw [lift, bind_ok, lift, bind_ok, lift, bind_ok, lift, bind_ok, lift, bind_ok]
  have hv : (i17 ||| UScalar.cast .U128 (UScalar.cast .U64 t2)).val =
      m.val * (x0.val * 2 ^ 128 + x1.val * 2 ^ 64 + x2.val) / 2 ^ 128 := by
    rw [UScalar.val_or, cast_u128_val, cast_u64_val, h17, wt, mul_comm,
      Nat.two_pow_add_eq_or_of_lt (Nat.mod_lt _ (Nat.two_pow_pos 64))]
  have mv : (UScalar.cast .U128 (UScalar.cast .U64 t1)).val =
      m.val * (x0.val * 2 ^ 128 + x1.val * 2 ^ 64 + x2.val) / 2 ^ 64 % 2 ^ 64 := by
    rw [cast_u128_val, cast_u64_val, wm]
  generalize i17 ||| UScalar.cast .U128 (UScalar.cast .U64 t2) = high at hv ⊢
  generalize UScalar.cast .U128 (UScalar.cast .U64 t1) = mid at mv ⊢
  have cw : x0.val * 2 ^ 128 + x1.val * 2 ^ 64 + x2.val = frac2PiN := by
    have e0 : x0.val = (fulcrum.tables.trig.FRAC_2_PI.val[0]!).val := by rw [h0]; rfl
    have e1 : x1.val = (fulcrum.tables.trig.FRAC_2_PI.val[1]!).val := by rw [h1]; rfl
    have e2 : x2.val = (fulcrum.tables.trig.FRAC_2_PI.val[2]!).val := by rw [h2]; rfl
    unfold frac2PiN; rw [e0, e1, e2]
  rw [cw] at hv mv
  generalize m.val * frac2PiN = P at hv mv ⊢
  have hb : high.val < 2 ^ 128 := high.bv.isLt
  refine WP.spec_bind (UScalar.add_spec (x := f) (y := 64#u32)
    (by rw [lit_val, U32_max_val]; omega)) fun i21 h21 => ?_
  rw [lit_val] at h21
  refine WP.spec_bind (UScalar.ShiftRight_spec high i21 (by rw [h21, n128]; omega)) fun i22 ⟨h22, _⟩ => ?_
  rw [h21, Nat.shiftRight_eq_div_pow] at h22
  rw [lift, bind_ok, lift, bind_ok]
  have qv : (UScalar.cast .U64 i22 &&& 3#u64).val = P / 2 ^ (f.val + 64) / 2 ^ 128 % 4 := by
    have lt : i22.val < 2 ^ 64 := by
      rw [h22, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
      exact hb.trans_le (by rw [← pow_add]; exact Nat.pow_le_pow_right two_pos (by omega))
    rw [UScalar.val_and, UScalar.cast_val_mod_pow_of_inBounds_eq _ _ lt, lit_val,
      show (3 : ℕ) = 2 ^ 2 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, h22, hv,
      Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm (2 ^ 128)]
  refine WP.spec_bind (UScalar.sub_spec (x := 64#u32) (y := f) (by rw [lit_val]; omega)) fun i24 ⟨h24, _⟩ => ?_
  rw [lit_val] at h24
  refine WP.spec_bind (UScalar.ShiftLeft_spec high i24 _ (by rw [h24, n128]; omega) rfl) fun i25 ⟨h25, _⟩ => ?_
  refine WP.spec_bind (UScalar.ShiftRight_spec mid f (by rw [n128]; omega)) fun i26 ⟨h26, _⟩ => ?_
  rw [lift, bind_ok, WP.spec_ok]
  refine ⟨qv, ?_⟩
  rw [UScalar.val_or, h25, h26, h24, UScalar.size_def, n128, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, hv, mv]
  exact frac_words P f.val (by omega)

/-- Halving `⌊X / 2^65⌋` with the dropped bit added rounds `X / 2^66`:
`⌊(⌊X / 2^65⌋ + 1) / 2⌋ = ⌊(X + 2^65) / 2^66⌋`, here as the cast of
`trig::position` from `i128` to `u64`. -/
theorem round_quarter_bit (X : ℕ) :
    ((((X / 2 ^ 65 : ℕ) : ℤ) + 1) / 2 % 2 ^ 64).toNat = (X + 2 ^ 65) / 2 ^ 66 % 2 ^ 64 := by
  omega

/-- On the code: `trig::position(q, frac)` with `q < 4` never fails and rounds
the quarter turns `q + frac / 2^128` to 62 fractional bits, to nearest with
ties up, wrapping mod 4. -/
theorem position_spec (q : Std.U64) (fr : Std.U128) (hq : q.val < 4) :
    fulcrum.trig.position q fr ⦃ t => t.val = (q.val * 2 ^ 128 + fr.val + 2 ^ 65) / 2 ^ 66 % 2 ^ 64 ⦄ := by
  unfold fulcrum.trig.position
  have n128 : UScalarTy.U128.numBits = 128 := rfl
  rw [lift, bind_ok]
  refine WP.spec_bind (UScalar.add_spec (x := fulcrum.tables.trig.FRAC) (y := 1#u32)
    (by rw [trig_frac_val, lit_val, U32_max_val]; norm_num)) fun i1 h1 => ?_
  rw [trig_frac_val, lit_val, show (62 + 1 : ℕ) = 63 from rfl] at h1
  refine WP.spec_bind (UScalar.ShiftLeft_spec (UScalar.cast .U128 q) i1 _ (by rw [h1, n128]; norm_num) rfl)
    fun i2 ⟨h2, _⟩ => ?_
  rw [cast_u128_val, h1, Nat.shiftLeft_eq, UScalar.size_def, n128,
    Nat.mod_eq_of_lt (by calc q.val * 2 ^ 63 < 4 * 2 ^ 63 := Nat.mul_lt_mul_of_pos_right hq (by positivity)
      _ < 2 ^ 128 := by norm_num)] at h2
  refine WP.spec_bind (UScalar.sub_spec (x := 127#u32) (y := fulcrum.tables.trig.FRAC)
    (by rw [trig_frac_val, lit_val]; norm_num)) fun i3 ⟨h3, _⟩ => ?_
  rw [trig_frac_val, lit_val, show (127 - 62 : ℕ) = 65 from rfl] at h3
  refine WP.spec_bind (UScalar.ShiftRight_spec fr i3 (by rw [h3, n128]; norm_num)) fun i4 ⟨h4, _⟩ => ?_
  rw [h3, Nat.shiftRight_eq_div_pow] at h4
  have frl : fr.val < 2 ^ 128 := fr.bv.isLt
  have i4l : i4.val < 2 ^ 63 := by
    rw [h4, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]; exact frl.trans_le (by norm_num)
  have vv : (i2 ||| i4).val = (q.val * 2 ^ 128 + fr.val) / 2 ^ 65 := by
    rw [UScalar.val_or, h2, mul_comm, ← Nat.two_pow_add_eq_or_of_lt i4l, h4,
      show (2 : ℕ) ^ 128 = 2 ^ 63 * 2 ^ 65 by norm_num, ← mul_assoc, add_comm (q.val * 2 ^ 63 * 2 ^ 65),
      Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), add_comm, mul_comm]
  rw [lift, bind_ok, lift, bind_ok]
  have vl : (i2 ||| i4).val < 2 ^ 65 := by
    rw [vv, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    calc q.val * 2 ^ 128 + fr.val < 3 * 2 ^ 128 + 2 ^ 128 := by omega
      _ ≤ 2 ^ 65 * 2 ^ 65 := by norm_num
  have hc : (UScalar.hcast .I128 (i2 ||| i4)).val = ((i2 ||| i4).val : ℤ) := by
    rw [UScalar.hcast_val_eq, IScalarTy.I128_numBits_eq]
    exact Int.bmod_eq_of_le ((neg_nonpos.mpr (by positivity)).trans (Int.natCast_nonneg _))
      ((by exact_mod_cast vl : ((i2 ||| i4).val : ℤ) < 2 ^ 65).trans_le (by norm_num))
  refine WP.spec_bind (shr_round_spec _ 1#u32) fun i6 h6 => ?_
  rw [hc, lit_val, ← zero_add 1, ← add_half_shr, shr_eq_div, pow_zero, zero_add, pow_one, vv] at h6
  rw [WP.spec_ok, IScalar.hcast_val_eq, h6, UScalarTy.U64_numBits_eq]
  exact round_quarter_bit _

/-- The position of `trig::position` after `trig::reduce` of `m`, on naturals:
the quarter turns `⌊m · C / 2^(64 + f)⌋ mod 2^130` at 128 fractional bits
rounded to 62, wrapping mod 4. -/
def posN (m f : ℕ) : ℕ := (m * frac2PiN / 2 ^ (f + 64) % 2 ^ 130 + 2 ^ 65) / 2 ^ 66 % 2 ^ 64

/-- The position `posN m f`, shifted by `s` units of `2^-62` quarter turns and
wrapped, is the angle `m / 2^f` radians shifted by `s / 2^62` quarters, up to
`0.79 · 2^-62` in the sine: `C` is within `½` of `2/π · 2^192`, the floor and the
rounding lose below `2^-66` and `½` units. -/
theorem position_near (m f s : ℕ) (hm : m < 2 ^ 64) :
    |Real.sin (((posN m f + s) % 2 ^ 64 : ℕ) / 2 ^ 62 * (Real.pi / 2)) -
      Real.sin (m / 2 ^ f + s / 2 ^ 62 * (Real.pi / 2))| ≤ 79 / 100 / 2 ^ 62 := by
  have hC : |(frac2PiN : ℝ) - 2 / Real.pi * 2 ^ 192| ≤ 1 / 2 := frac_2_pi_entry
  set N := m * frac2PiN / 2 ^ (f + 64) with hN
  set R := (N % 2 ^ 130 + 2 ^ 65) / 2 ^ 66 with hR
  set u := (posN m f + s) % 2 ^ 64 with hu
  have eN := Nat.mod_add_div N (2 ^ 130)
  have eR := Nat.mod_add_div R (2 ^ 64)
  have eu := Nat.mod_add_div (posN m f + s) (2 ^ 64)
  rw [← hu] at eu
  have pR : posN m f = R % 2 ^ 64 := rfl
  set K := R / 2 ^ 64 + N / 2 ^ 130 + (posN m f + s) / 2 ^ 64 with hK
  have hR' := floor_div_near (N % 2 ^ 130 + 2 ^ 65) (2 ^ 66) (by positivity)
  have hN' := floor_div_near (m * frac2PiN) (2 ^ (f + 64)) (by positivity)
  rw [← hR] at hR'
  rw [← hN] at hN'
  have mR : (m : ℝ) < 2 ^ 64 := by exact_mod_cast hm
  set δ : ℝ := u - s + 2 ^ 64 * K - m * (2 / Real.pi) * 2 ^ 62 / 2 ^ f with hδ
  have eδ : δ = (R - (N % 2 ^ 130 : ℕ) / 2 ^ 66) + (N - m * frac2PiN / 2 ^ (f + 64)) / 2 ^ 66 +
      m * (frac2PiN - 2 / Real.pi * 2 ^ 192) / 2 ^ (f + 130) := by
    have eN' : ((N % 2 ^ 130 : ℕ) : ℝ) + 2 ^ 130 * (N / 2 ^ 130 : ℕ) = N := by exact_mod_cast eN
    have eR' : ((R % 2 ^ 64 : ℕ) : ℝ) + 2 ^ 64 * (R / 2 ^ 64 : ℕ) = R := by exact_mod_cast eR
    have eu' : (u : ℝ) + 2 ^ 64 * ((posN m f + s) / 2 ^ 64 : ℕ) = posN m f + s := by exact_mod_cast eu
    rw [← pR] at eR'
    rw [hδ, hK]; push_cast
    rw [pow_add, pow_add]
    linear_combination eu' + eR' + eN' / 2 ^ 66
  have b1 : |(R : ℝ) - (N % 2 ^ 130 : ℕ) / 2 ^ 66| ≤ 1 / 2 := by
    simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat] at hR'
    rw [add_div, show (2 : ℝ) ^ 65 / 2 ^ 66 = 1 / 2 by norm_num] at hR'
    exact abs_le.mpr ⟨by linarith [hR'.2], by linarith [hR'.1]⟩
  have b2 : |((N : ℝ) - m * frac2PiN / 2 ^ (f + 64)) / 2 ^ 66| ≤ 1 / 2 ^ 66 := by
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hN'
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 66)]
    exact div_le_div_of_nonneg_right (abs_le.mpr ⟨by linarith [hN'.2], by linarith [hN'.1]⟩) (by positivity)
  have b3 : |(m : ℝ) * (frac2PiN - 2 / Real.pi * 2 ^ 192) / 2 ^ (f + 130)| ≤ 1 / 2 ^ 67 := by
    rw [abs_div, abs_mul, Nat.abs_cast, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ (f + 130)),
      div_le_iff₀ (by positivity)]
    calc (m : ℝ) * |(frac2PiN : ℝ) - 2 / Real.pi * 2 ^ 192| ≤ 2 ^ 64 * (1 / 2) :=
          mul_le_mul mR.le hC (abs_nonneg _) (by positivity)
      _ = 1 / 2 ^ 67 * 2 ^ 130 := by norm_num
      _ ≤ 1 / 2 ^ 67 * 2 ^ (f + 130) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ one_le_two (by omega)) (by positivity)
  have bδ : |δ| ≤ 1 / 2 + 1 / 2 ^ 66 + 1 / 2 ^ 67 := by
    rw [eδ]; exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add b1 b2)) b3)
  have angle : (u : ℝ) / 2 ^ 62 * (Real.pi / 2) =
      (m / 2 ^ f + s / 2 ^ 62 * (Real.pi / 2) + δ * Real.pi / 2 ^ 63) - K * (2 * Real.pi) := by
    rw [hδ]; field_simp; ring
  rw [angle, Real.sin_sub_nat_mul_two_pi]
  refine (Real.abs_sin_sub_sin_le _ _).trans ?_
  rw [add_sub_cancel_left, abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 63)]
  calc |δ| * Real.pi / 2 ^ 63 ≤ (1 / 2 + 1 / 2 ^ 66 + 1 / 2 ^ 67) * 3.15 / 2 ^ 63 := by
        gcongr
        exact Real.pi_lt_d2.le
    _ ≤ 79 / 100 / 2 ^ 62 := by norm_num

/-- `trig::reduce` of `m` and `trig::position` of its result give `posN m f`,
for any continuation `k` of the position. -/
theorem reduce_position_spec {α} (m : Std.U64) (f : Std.U32) (hf : f.val ≤ 62) (k : Std.U64 → Result α)
    (P : α → Prop) (hk : ∀ t : Std.U64, t.val = posN m.val f.val → k t ⦃ P ⦄) :
    (do
      let (q, fr) ← fulcrum.trig.reduce m f
      let t ← fulcrum.trig.position q fr
      k t) ⦃ P ⦄ := by
  refine WP.spec_bind (reduce_spec m f hf) fun r ⟨hq, hr⟩ => ?_
  obtain ⟨q, fr⟩ := r
  refine WP.spec_bind (position_spec q fr (by rw [hq]; exact Nat.mod_lt _ (by norm_num))) fun t ht => hk t ?_
  rw [ht, hq, hr, posN, show (2 : ℕ) ^ 130 = 2 ^ 128 * 4 by norm_num, Nat.mod_mul, mul_comm (2 ^ 128), add_comm (_ * 2 ^ 128)]

/-- `trig::sin_position` at the position `(posN m f + s) mod 2^64` with `62` bits
is within `½ + 6.9 / 2^(62 - f)` of `sin (m / 2^f + s / 2^62 · π/2) · 2^f`, and
above `-2^63`. -/
theorem sin_position_radians (t : Std.U64) (m s : ℕ) (f : Std.U32) (hm : m < 2 ^ 64) (hf : f.val ≤ 62)
    (ht : t.val = (posN m f.val + s) % 2 ^ 64) :
    fulcrum.trig.sin_position t fulcrum.tables.trig.FRAC f ⦃ r =>
      |(r.val : ℝ) - Real.sin (m / 2 ^ f.val + s / 2 ^ 62 * (Real.pi / 2)) * 2 ^ f.val| ≤
        1 / 2 + 69 / 10 / 2 ^ (62 - f.val) ∧ -2 ^ 63 < r.val ⦄ := by
  refine WP.spec_mono (sin_position_spec t _ f (by rw [trig_frac_val]) hf
    (by rw [trig_frac_val]; exact t.bv.isLt)) fun r hr => ?_
  rw [trig_frac_val, ht] at hr
  have near := position_near m f.val s hm
  set S := Real.sin (m / 2 ^ f.val + s / 2 ^ 62 * (Real.pi / 2))
  set S' := Real.sin (((posN m f.val + s) % 2 ^ 64 : ℕ) / 2 ^ 62 * (Real.pi / 2))
  have S1 : -1 ≤ S := Real.neg_one_le_sin _
  clear_value S S'
  have p62 : (2 : ℝ) ^ 62 = 2 ^ (62 - f.val) * 2 ^ f.val := by rw [← pow_add, Nat.sub_add_cancel hf]
  have d : |S' * 2 ^ f.val - S * 2 ^ f.val| ≤ 79 / 100 / 2 ^ (62 - f.val) := by
    rw [← sub_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ f.val)]
    calc |S' - S| * 2 ^ f.val ≤ 79 / 100 / 2 ^ 62 * 2 ^ f.val := by gcongr
      _ = 79 / 100 / 2 ^ (62 - f.val) := by rw [p62]; field_simp
  have err : |(r.val : ℝ) - S * 2 ^ f.val| ≤ 1 / 2 + 69 / 10 / 2 ^ (62 - f.val) := by
    calc |(r.val : ℝ) - S * 2 ^ f.val| ≤ |(r.val : ℝ) - S' * 2 ^ f.val| + |S' * 2 ^ f.val - S * 2 ^ f.val| :=
          abs_sub_le _ _ _
      _ ≤ 1 / 2 + 61 / 10 / 2 ^ (62 - f.val) + 79 / 100 / 2 ^ (62 - f.val) := add_le_add hr d
      _ ≤ 1 / 2 + 69 / 10 / 2 ^ (62 - f.val) := by
          rw [add_assoc, ← add_div]; gcongr; norm_num
  refine ⟨err, ?_⟩
  have e7 : 1 / 2 + 69 / 10 / 2 ^ (62 - f.val) ≤ (8 : ℝ) :=
    (add_le_add le_rfl (div_le_self (by norm_num) (one_le_pow₀ one_le_two))).trans (by norm_num)
  have sl : -(2 : ℝ) ^ 62 ≤ S * 2 ^ f.val := by
    have := mul_le_mul_of_nonneg_right S1
      (by positivity : (0 : ℝ) ≤ 2 ^ f.val)
    have pf : (2 : ℝ) ^ f.val ≤ 2 ^ 62 := pow_le_pow_right₀ one_le_two hf
    linarith
  have : -(2 : ℝ) ^ 63 < r.val := by linarith [(abs_le.mp (err.trans e7)).1]
  exact_mod_cast this

/-- `|raw|` as a real is `raw` or `-raw` by the sign. -/
theorem natAbs_real (x : ℤ) : ((x.natAbs : ℕ) : ℝ) = if x < 0 then -(x : ℝ) else x := by
  rw [Nat.cast_natAbs, Int.cast_abs]
  split_ifs with h
  · exact abs_of_neg (by exact_mod_cast h)
  · exact abs_of_nonneg (by exact_mod_cast not_lt.mp h)

/-- L4 on the code: `trig::sin` with `f ≤ 62` never fails and is within
`½ + 6.9 / 2^(62 - f)` of `sin (raw / 2^f) · 2^f`. -/
theorem sin_spec (raw : Std.I64) (f : Std.U32) (hf : f.val ≤ 62) :
    fulcrum.trig.sin raw f ⦃ r =>
      |(r.val : ℝ) - Real.sin (raw.val / 2 ^ f.val) * 2 ^ f.val| ≤ 1 / 2 + 69 / 10 / 2 ^ (62 - f.val) ⦄ := by
  unfold fulcrum.trig.sin
  refine WP.spec_bind (I64_unsigned_abs_spec raw) fun m hm => ?_
  refine reduce_position_spec m f hf _ _ fun t ht => ?_
  refine WP.spec_bind (sin_position_radians t m.val 0 f m.bv.isLt hf (by rw [ht, add_zero, posN, Nat.mod_mod]))
    fun s ⟨hs, hlo⟩ => ?_
  rw [Nat.cast_zero, zero_div, zero_mul, add_zero, hm, natAbs_real] at hs
  by_cases hn : raw < 0#i64
  · have hn' : raw.val < 0 := hn
    rw [ite_eq_left hn, ite_eq_left hn'] at *
    refine WP.spec_mono (IScalar.neg_step _ (fun e => ?_)) fun r hr => ?_
    · rw [e, IScalar.min_def, IScalarTy.I64_numBits_eq] at hlo; norm_num at hlo
    · rw [hr, Int.cast_neg, neg_div, Real.sin_neg] at *
      rw [show -(s.val : ℝ) - Real.sin (raw.val / 2 ^ f.val) * 2 ^ f.val =
        -((s.val : ℝ) - -Real.sin (raw.val / 2 ^ f.val) * 2 ^ f.val) by ring, abs_neg]
      exact hs
  · have hn' : ¬ raw.val < 0 := hn
    rw [ite_eq_right hn'] at hs
    rw [ite_eq_right hn, WP.spec_ok]
    exact hs

/-- `cos (|raw| / 2^f)` is `cos (raw / 2^f)`. -/
theorem cos_natAbs (x : ℤ) (f : ℕ) :
    Real.cos (((x.natAbs : ℕ) : ℝ) / 2 ^ f) = Real.cos ((x : ℝ) / 2 ^ f) := by
  rw [natAbs_real]; split_ifs
  · rw [neg_div, Real.cos_neg]
  · rfl

/-- `trig::sin_position` a quarter turn after the position of `|raw|` is within
`½ + 6.9 / 2^(62 - f)` of `cos (raw / 2^f) · 2^f`. -/
theorem cos_position_radians (raw : Std.I64) (t : Std.U64) (f : Std.U32) (hf : f.val ≤ 62)
    (ht : t.val = posN raw.val.natAbs f.val) :
    (do
      let one ← fulcrum.trig.ONE
      let u ← lift (core.num.U64.wrapping_add t one)
      fulcrum.trig.sin_position u fulcrum.tables.trig.FRAC f) ⦃ r =>
      |(r.val : ℝ) - Real.cos (raw.val / 2 ^ f.val) * 2 ^ f.val| ≤ 1 / 2 + 69 / 10 / 2 ^ (62 - f.val) ⦄ := by
  refine WP.spec_bind trig_one_spec fun one h1 => ?_
  rw [lift, bind_ok]
  have hl : raw.val.natAbs < 2 ^ 64 := by
    have := natAbs_le_pow raw 63 IScalarTy.I64_numBits_eq
    exact this.trans_lt (by norm_num)
  refine WP.spec_mono (sin_position_radians _ raw.val.natAbs (2 ^ 62) f hl hf (by
    rw [show core.num.U64.wrapping_add t one = UScalar.wrapping_add t one from rfl,
      UScalar.wrapping_add_val_eq, ht, h1, UScalar.size_def, UScalarTy.U64_numBits_eq])) fun r ⟨hr, _⟩ => ?_
  rw [Nat.cast_pow, Nat.cast_ofNat, div_self (by positivity), one_mul, Real.sin_add_pi_div_two,
    cos_natAbs] at hr
  exact hr

/-- L4 on the code: `trig::cos` with `f ≤ 62` never fails and is within
`½ + 6.9 / 2^(62 - f)` of `cos (raw / 2^f) · 2^f`. -/
theorem cos_spec (raw : Std.I64) (f : Std.U32) (hf : f.val ≤ 62) :
    fulcrum.trig.cos raw f ⦃ r =>
      |(r.val : ℝ) - Real.cos (raw.val / 2 ^ f.val) * 2 ^ f.val| ≤ 1 / 2 + 69 / 10 / 2 ^ (62 - f.val) ⦄ := by
  unfold fulcrum.trig.cos
  refine WP.spec_bind (I64_unsigned_abs_spec raw) fun m hm => ?_
  exact reduce_position_spec m f hf _ _ fun t ht => cos_position_radians raw t f hf (hm ▸ ht)

/-- L4 on the code: `trig::sin_cos` with `f ≤ 62` never fails and each of its
two values is within `½ + 6.9 / 2^(62 - f)` of `sin (raw / 2^f) · 2^f` and
`cos (raw / 2^f) · 2^f`. -/
theorem sin_cos_spec (raw : Std.I64) (f : Std.U32) (hf : f.val ≤ 62) :
    fulcrum.trig.sin_cos raw f ⦃ r =>
      |(r.1.val : ℝ) - Real.sin (raw.val / 2 ^ f.val) * 2 ^ f.val| ≤ 1 / 2 + 69 / 10 / 2 ^ (62 - f.val) ∧
        |(r.2.val : ℝ) - Real.cos (raw.val / 2 ^ f.val) * 2 ^ f.val| ≤ 1 / 2 + 69 / 10 / 2 ^ (62 - f.val) ⦄ := by
  unfold fulcrum.trig.sin_cos
  refine WP.spec_bind (I64_unsigned_abs_spec raw) fun m hm => ?_
  refine reduce_position_spec m f hf _ _ fun t ht => ?_
  refine WP.spec_bind (sin_position_radians t m.val 0 f m.bv.isLt hf (by rw [ht, add_zero, posN, Nat.mod_mod]))
    fun s ⟨hs, hlo⟩ => ?_
  rw [Nat.cast_zero, zero_div, zero_mul, add_zero, hm, natAbs_real] at hs
  refine WP.spec_bind trig_one_spec fun one h1 => ?_
  rw [lift, bind_ok]
  refine WP.spec_bind (sin_position_radians _ m.val (2 ^ 62) f m.bv.isLt hf (by
    rw [show core.num.U64.wrapping_add t one = UScalar.wrapping_add t one from rfl,
      UScalar.wrapping_add_val_eq, ht, h1, UScalar.size_def, UScalarTy.U64_numBits_eq])) fun c ⟨hc, _⟩ => ?_
  rw [Nat.cast_pow, Nat.cast_ofNat, div_self (by positivity), one_mul, Real.sin_add_pi_div_two, hm,
    cos_natAbs] at hc
  by_cases hn : raw < 0#i64
  · have hn' : raw.val < 0 := hn
    rw [ite_eq_left hn'] at hs
    rw [ite_eq_left hn]
    refine WP.spec_bind (IScalar.neg_step _ (fun e => ?_)) fun r hr => ?_
    · rw [e, IScalar.min_def, IScalarTy.I64_numBits_eq] at hlo; norm_num at hlo
    · rw [WP.spec_ok]
      refine ⟨?_, hc⟩
      rw [hr, Int.cast_neg, neg_div, Real.sin_neg] at *
      rw [show -(s.val : ℝ) - Real.sin (raw.val / 2 ^ f.val) * 2 ^ f.val =
        -((s.val : ℝ) - -Real.sin (raw.val / 2 ^ f.val) * 2 ^ f.val) by ring, abs_neg]
      exact hs
  · have hn' : ¬ raw.val < 0 := hn
    rw [ite_eq_right hn'] at hs
    rw [ite_eq_right hn, WP.spec_ok]
    exact ⟨hs, hc⟩

end Fulcrum

end
