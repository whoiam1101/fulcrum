module

public import Fulcrum.L4.Exp
public import Fulcrum.Math.Pow

/-!
# L4: `exp::mul_hi`, `log2_wide`, `exp2_wide`, `pow_magnitude`, `pow` (INTERNALS §3.16)

On the code extracted by Aeneas, with `1 ≤ f ≤ 32`.

- `widening_mul_u128` and `mul_hi`: the top word of four `u64 × u64` products is
  `⌊a · b / 2^128⌋` (`widening_hi`).
- `log2_wide(a, f)` of `0 < a ≤ 2^63` shifts `a` to the mantissa `U` exactly (right by one bit
  for `a = 2^63`), takes the quotient `s = ⌊(U - C) · 2^128 / (U + C)⌋` in two 64-bit steps
  (`div_two_words`) and is `log2WideN` of `Math/Pow.lean` shifted to 120 bits: within `1.05`
  units of `log₂ (a / 2^f) · 2^120`, below `2^126` in magnitude.
- `exp2_wide(w, f)` splits `w = n · 2^120 + t` by a shift and a mask and returns the mark
  `2^(2f)` for `n ≥ f`; `y = ⌊⌊r / 2^48⌋ · ⌊LN_2 / 2^40⌋ / 2^64⌋` of the remainder `r` is within
  `2.7` units of `r · ln 2 / 2^48`, the mantissa within `2.2 · 2^56`, and the result within
  `½ + 2.2 · 2^(2f) / 2^71` of `2^(w / 2^120) · 2^f`.
- `pow_magnitude` multiplies `|y|` by the halves of `|log2_wide|` exactly: the sum is
  `⌊|y| · |l| / 2^fy⌋` and, with its sign, within `1` of `y · l / 2^fy`, so the exponent is within
  `1.05 Y + 1` units of `y / 2^fy · log₂ x · 2^120`, `Y = |y| / 2^fy`; `pow_tail_near` turns that
  into the relative error `(Y + 1) / 2^120` of the result. The shortcut for `|w| ≥ 64` gives `0`
  below `½` or the mark with `X ≥ 2^(2f - 1)` (`powOk`).
- `pow` returns `2^f` for `y = 0`, `0` or the mark for `x = 0`, `none` for a negative `x` and
  `y / 2^fy` not an integer, and otherwise `powOk` of `|x|`, negated for a negative `x` and an
  odd `y / 2^fy` (`i64_and_mask_val` reads the low bits of `y`).
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace Fulcrum

set_option maxRecDepth 10000

/-- The top word of `a · b` from four `u64 × u64` products: `a = a₁ 2^64 + a₀`,
`b = b₁ 2^64 + b₀`, `mid = ⌊a₀b₀ / 2^64⌋ + (a₀b₁ mod 2^64) + (a₁b₀ mod 2^64)`. -/
theorem widening_hi (a b : ℕ) :
    a / 2 ^ 64 * (b / 2 ^ 64) + a % 2 ^ 64 * (b / 2 ^ 64) / 2 ^ 64 + a / 2 ^ 64 * (b % 2 ^ 64) / 2 ^ 64 +
      (a % 2 ^ 64 * (b % 2 ^ 64) / 2 ^ 64 + a % 2 ^ 64 * (b / 2 ^ 64) % 2 ^ 64 +
        a / 2 ^ 64 * (b % 2 ^ 64) % 2 ^ 64) / 2 ^ 64 = a * b / 2 ^ 128 := by
  have ea := Nat.div_add_mod a (2 ^ 64)
  have eb := Nat.div_add_mod b (2 ^ 64)
  generalize a / 2 ^ 64 = a1 at ea ⊢
  generalize a % 2 ^ 64 = a0 at ea ⊢
  generalize b / 2 ^ 64 = b1 at eb ⊢
  generalize b % 2 ^ 64 = b0 at eb ⊢
  have p : a * b = a1 * b1 * 2 ^ 128 + a0 * b1 * 2 ^ 64 + a1 * b0 * 2 ^ 64 + a0 * b0 := by
    rw [← ea, ← eb]; ring
  rw [p]
  generalize a1 * b1 = P11
  generalize a0 * b1 = P01
  generalize a1 * b0 = P10
  generalize a0 * b0 = P00
  omega

/-- L4 on the code: the top word of `wide::widening_mul_u128(a, b)` is `⌊a · b / 2^128⌋`, and
it never fails. -/
theorem widening_mul_u128_spec (a b : Std.U128) :
    fulcrum.wide.widening_mul_u128 a b ⦃ p => p.1.val = a.val * b.val / 2 ^ 128 ⦄ := by
  have n128 : UScalarTy.U128.numBits = 128 := rfl
  have mx : UScalar.max .U128 = 2 ^ 128 - 1 := U128_max_val
  have al : a.val < 2 ^ 128 := a.bv.isLt
  have bl : b.val < 2 ^ 128 := b.bv.isLt
  unfold fulcrum.wide.widening_mul_u128
  refine WP.spec_bind (shr_i32_spec a 64#i32 64 rfl (by rw [n128]; norm_num)) fun a1 ha1 => ?_
  rw [lift, bind_ok, lift, bind_ok]
  refine WP.spec_bind (shr_i32_spec b 64#i32 64 rfl (by rw [n128]; norm_num)) fun b1 hb1 => ?_
  rw [lift, bind_ok, lift, bind_ok]
  have a0v : (UScalar.cast .U128 (UScalar.cast .U64 a)).val = a.val % 2 ^ 64 := by
    rw [cast_u128_val, cast_u64_val]
  have b0v : (UScalar.cast .U128 (UScalar.cast .U64 b)).val = b.val % 2 ^ 64 := by
    rw [cast_u128_val, cast_u64_val]
  generalize UScalar.cast .U128 (UScalar.cast .U64 a) = a0 at a0v ⊢
  generalize UScalar.cast .U128 (UScalar.cast .U64 b) = b0 at b0v ⊢
  have a1l : a1.val < 2 ^ 64 := by rw [ha1, Nat.div_lt_iff_lt_mul (by positivity)]; omega
  have b1l : b1.val < 2 ^ 64 := by rw [hb1, Nat.div_lt_iff_lt_mul (by positivity)]; omega
  have a0l : a0.val < 2 ^ 64 := by rw [a0v]; omega
  have b0l : b0.val < 2 ^ 64 := by rw [b0v]; omega
  have pl : ∀ x y : ℕ, x < 2 ^ 64 → y < 2 ^ 64 → x * y ≤ 2 ^ 128 - 1 := fun x y hx hy => by
    have := Nat.mul_le_mul (Nat.le_pred_of_lt hx) (Nat.le_pred_of_lt hy)
    exact this.trans (by norm_num)
  refine WP.spec_bind (UScalar.mul_spec (x := a0) (y := b0) (by rw [mx]; exact pl _ _ a0l b0l)) fun p00 h00 => ?_
  refine WP.spec_bind (UScalar.mul_spec (x := a0) (y := b1) (by rw [mx]; exact pl _ _ a0l b1l)) fun p01 h01 => ?_
  refine WP.spec_bind (UScalar.mul_spec (x := a1) (y := b0) (by rw [mx]; exact pl _ _ a1l b0l)) fun p10 h10 => ?_
  refine WP.spec_bind (shr_i32_spec p00 64#i32 64 rfl (by rw [n128]; norm_num)) fun i2 h2 => ?_
  rw [lift, bind_ok, lift, bind_ok]
  have q00 : p00.val ≤ 2 ^ 128 - 1 := by rw [h00]; exact pl _ _ a0l b0l
  refine WP.spec_bind (UScalar.add_spec (x := i2) (y := UScalar.cast .U128 (UScalar.cast .U64 p01))
    (by rw [cast_u128_val, cast_u64_val, h2, mx]; omega)) fun i5 h5 => ?_
  rw [cast_u128_val, cast_u64_val, h2] at h5
  rw [lift, bind_ok, lift, bind_ok]
  refine WP.spec_bind (UScalar.add_spec (x := i5) (y := UScalar.cast .U128 (UScalar.cast .U64 p10))
    (by rw [cast_u128_val, cast_u64_val, h5, mx]; omega)) fun mid hmid => ?_
  rw [cast_u128_val, cast_u64_val, h5] at hmid
  rw [lift, bind_ok, lift, bind_ok]
  refine WP.spec_bind (UScalar.ShiftLeft_IScalar_spec mid 64#i32 _ (by decide) (by rw [n128]; decide) rfl)
    fun i10 _ => ?_
  rw [lift, bind_ok]
  have top := widening_hi a.val b.val
  rw [← ha1, ← hb1, ← a0v, ← b0v] at top
  have tl : a.val * b.val / 2 ^ 128 < 2 ^ 128 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    exact (Nat.mul_lt_mul_of_lt_of_le al bl.le (by omega)).trans_le le_rfl
  refine WP.spec_bind (UScalar.mul_spec (x := a1) (y := b1) (by rw [mx]; exact pl _ _ a1l b1l)) fun i11 h11 => ?_
  refine WP.spec_bind (shr_i32_spec p01 64#i32 64 rfl (by rw [n128]; norm_num)) fun i12 h12 => ?_
  refine WP.spec_bind (UScalar.add_spec (x := i11) (y := i12) (by rw [h11, h12, h01, mx]; omega)) fun i13 h13 => ?_
  refine WP.spec_bind (shr_i32_spec p10 64#i32 64 rfl (by rw [n128]; norm_num)) fun i14 h14 => ?_
  refine WP.spec_bind (UScalar.add_spec (x := i13) (y := i14) (by rw [h13, h11, h12, h14, h01, h10, mx]; omega))
    fun i15 h15 => ?_
  refine WP.spec_bind (shr_i32_spec mid 64#i32 64 rfl (by rw [n128]; norm_num)) fun i16 h16 => ?_
  refine WP.spec_bind (UScalar.add_spec (x := i15) (y := i16)
    (by rw [h15, h13, h11, h12, h14, h16, hmid, h01, h10, h00, mx]; omega)) fun hi hhi => ?_
  rw [WP.spec_ok, hhi, h15, h13, h11, h12, h14, h16, hmid, h01, h10, h00]
  exact top

/-- L4 on the code: `exp::mul_hi(a, b)` never fails and is `⌊a · b / 2^128⌋`. -/
theorem mul_hi_spec (a b : Std.U128) : fulcrum.exp.mul_hi a b ⦃ r => r.val = a.val * b.val / 2 ^ 128 ⦄ := by
  unfold fulcrum.exp.mul_hi
  refine WP.spec_bind (widening_mul_u128_spec a b) fun p hp => ?_
  obtain ⟨h, l⟩ := p
  exact (WP.spec_ok _).mpr hp

/-- `u128::MAX` is `2^128 - 1`. -/
theorem u128_max_val : core.num.U128.MAX.val = 2 ^ 128 - 1 := rfl

/-- The 128-bit quotient of `log2_wide` from two 64-bit steps:
`⌊x / d⌋ · 2^64 + ⌊(x mod d) · 2^64 / d⌋ = ⌊x · 2^64 / d⌋`. -/
theorem div_two_words (x d : ℕ) (hd : 0 < d) : x / d * 2 ^ 64 + x % d * 2 ^ 64 / d = x * 2 ^ 64 / d := by
  have e := Nat.div_add_mod x d
  conv_rhs => rw [← e]
  rw [add_mul, mul_assoc, mul_comm d, add_comm (x / d * 2 ^ 64 * d), Nat.add_mul_div_right _ _ hd, add_comm]

/-- An entry `k < 256` of `LOG2_WIDE`, read by `index_usize`: within `½` of
`log₂ (1 + k/256) · 2^126`, and at most `2^126`. -/
theorem log2_wide_table_spec (i : Std.Usize) (hi : i.val < 256) :
    Array.index_usize fulcrum.tables.exp.LOG2_WIDE i ⦃ x =>
      |(x.val : ℝ) - Real.logb 2 (1 + (i.val : ℝ) / 256) * 2 ^ 126| ≤ 1 / 2 ∧ x.val ≤ 2 ^ 126 ⦄ := by
  have hl : i.val < fulcrum.tables.exp.LOG2_WIDE.length := by
    rw [Array.length, fulcrum.tables.exp.LOG2_WIDE.property]; exact hi
  refine WP.spec_mono (Array.index_usize_spec _ i hl) fun x hx => ?_
  have e := log2_wide_entry i.val hi
  rw [getElem!_pos fulcrum.tables.exp.LOG2_WIDE.val i.val
    (show i.val < fulcrum.tables.exp.LOG2_WIDE.val.length from hl), ← hx] at e
  refine ⟨e, ?_⟩
  have lb : Real.logb 2 (1 + (i.val : ℝ) / 256) < 1 := by
    rw [Real.logb_lt_iff_lt_rpow (by norm_num) (by positivity), Real.rpow_one]
    have : (i.val : ℝ) < 256 := by exact_mod_cast hi
    linarith
  have u : (x.val : ℝ) < 2 ^ 126 + 1 := by
    have := (abs_le.mp e).2
    nlinarith
  exact Nat.lt_succ_iff.mp (by exact_mod_cast u)

/-- `exp::W_FRAC` is `120`. -/
theorem w_frac_val : fulcrum.exp.W_FRAC.val = 120 := by
  unfold fulcrum.exp.W_FRAC; rfl

/-- `tables::exp::WIDE_FRAC` is `126`. -/
theorem wide_frac_val : fulcrum.tables.exp.WIDE_FRAC.val = 126 := by
  unfold fulcrum.tables.exp.WIDE_FRAC; rfl

/-- A Horner step of `log2_wide` on the code: `c + mul_hi z g` of `c = ⌊(2^128 - 1)/n⌋`,
`n ≥ 3`, and `z ≤ 2^110` never fails and is `c + ⌊z g / 2^128⌋`. -/
theorem horner_wide_spec {α} (z g : Std.U128) (n : Std.U128) (hn : 3 ≤ n.val) (hz : z.val ≤ 2 ^ 110)
    (k : Std.U128 → Result α) (P : α → Prop)
    (hk : ∀ r : Std.U128, r.val = (2 ^ 128 - 1) / n.val + mul128 z.val g.val → k r ⦃ P ⦄) :
    (do
      let c ← core.num.U128.MAX / n
      let i ← fulcrum.exp.mul_hi z g
      let r ← c + i
      k r) ⦃ P ⦄ := by
  refine WP.spec_bind (u128_div_spec _ n n.val rfl (by omega)) fun c hc => ?_
  rw [u128_max_val] at hc
  refine WP.spec_bind (mul_hi_spec z g) fun i hi => ?_
  have il : i.val ≤ 2 ^ 110 := by
    rw [hi]; exact (mul128_le_left _ _ g.bv.isLt.le).trans hz
  have cl : c.val ≤ (2 ^ 128 - 1) / 3 := by rw [hc]; exact Nat.div_le_div_left hn (by norm_num)
  refine WP.spec_bind (UScalar.add_spec (x := c) (y := i) (by rw [U128_max_val]; omega)) fun r hr => ?_
  exact hk r (by rw [hr, hc, hi]; rfl)

/-- L4 on the code: `exp::log2_wide(a, f)` of `0 < a ≤ 2^63`, `1 ≤ f ≤ 32` never fails and is
within `1.05` units of `log₂ (a / 2^f) · 2^120`; its magnitude is below `2^126`. -/
theorem log2_wide_spec (a : Std.U64) (f : Std.U32) (ha0 : 0 < a.val) (ha : a.val ≤ 2 ^ 63) (hf1 : 1 ≤ f.val)
    (hf : f.val ≤ 32) :
    fulcrum.exp.log2_wide a f ⦃ l =>
      |(l.val : ℝ) - Real.logb 2 ((a.val : ℝ) / 2 ^ f.val) * 2 ^ 120| ≤ 105 / 100 ∧ l.val.natAbs < 2 ^ 126 ⦄ := by
  have n128 : UScalarTy.U128.numBits = 128 := rfl
  have n64 : UScalarTy.U64.numBits = 64 := rfl
  unfold fulcrum.exp.log2_wide
  have a0 : a.val ≠ 0 := by omega
  set L := Nat.log 2 a.val with hL
  have hlo : 2 ^ L ≤ a.val := Nat.pow_log_le_self 2 a0
  have hhi : a.val < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two _
  have L63 : L ≤ 63 := by
    have : a.val < 2 ^ 64 := by omega
    exact Nat.le_of_lt_succ ((Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp (hlo.trans_lt this))
  have hlz : (core.num.U64.leading_zeros a).val = 64 - L - 1 := leading_zeros_val a a0 (Nat.le_of_ble_eq_true rfl)
  rw [lift, bind_ok]
  refine WP.spec_bind (UScalar.sub_spec (x := 63#u32) (y := core.num.U64.leading_zeros a)
    (by rw [hlz, lit_val]; omega)) fun e ⟨he, _⟩ => ?_
  rw [hlz, lit_val] at he
  have ev : e.val = L := by omega
  refine WP.spec_bind (Pₘ := fun u : Std.U64 => u.val * 2 ^ L = a.val * 2 ^ 62) ?_ fun u hu => ?_
  · by_cases big : e > fulcrum.tables.exp.FRAC
    · have b : 62 < L := by have : fulcrum.tables.exp.FRAC.val < e.val := big; rw [exp_frac_val] at this; omega
      rw [ite_eq_left big]
      refine WP.spec_bind (UScalar.sub_spec (x := e) (y := fulcrum.tables.exp.FRAC)
        (by rw [exp_frac_val]; omega)) fun i1 ⟨h1, _⟩ => ?_
      rw [exp_frac_val, ev] at h1
      refine WP.spec_mono (UScalar.ShiftRight_spec a i1 (by rw [h1, n64]; omega)) fun u ⟨hu, _⟩ => ?_
      have L63' : L = 63 := by omega
      have av : a.val = 2 ^ 63 := le_antisymm ha (by rw [← L63']; exact hlo)
      rw [hu, Nat.shiftRight_eq_div_pow, h1, L63', av]
      norm_num
    · have b : L ≤ 62 := by
        have : ¬ fulcrum.tables.exp.FRAC.val < e.val := big; rw [exp_frac_val] at this; omega
      rw [ite_eq_right big]
      refine WP.spec_bind (UScalar.sub_spec (x := fulcrum.tables.exp.FRAC) (y := e)
        (by rw [exp_frac_val, ev]; exact b)) fun i1 ⟨h1, _⟩ => ?_
      rw [exp_frac_val, ev] at h1
      have Ul : a.val * 2 ^ (62 - L) < 2 ^ 63 := by
        calc a.val * 2 ^ (62 - L) < 2 ^ (L + 1) * 2 ^ (62 - L) := Nat.mul_lt_mul_of_pos_right hhi (by positivity)
          _ = 2 ^ 63 := by rw [← pow_add]; congr 1; omega
      refine WP.spec_mono (UScalar.ShiftLeft_spec a i1 _ (by rw [h1, n64]; omega) rfl) fun u ⟨hu, _⟩ => ?_
      rw [hu, h1, Nat.shiftLeft_eq, UScalar.size_def, n64, Nat.mod_eq_of_lt (Ul.trans (by norm_num)), mul_assoc,
        ← pow_add, show 62 - L + L = 62 by omega]
  have Ug : 2 ^ 62 ≤ u.val := by
    have : 2 ^ 62 * 2 ^ L ≤ u.val * 2 ^ L := by rw [hu, mul_comm (2 ^ 62)]; exact Nat.mul_le_mul_right _ hlo
    exact Nat.le_of_mul_le_mul_right this (by positivity)
  have Ul : u.val < 2 ^ 63 := by
    have : u.val * 2 ^ L < 2 ^ 63 * 2 ^ L := by
      rw [hu, show 2 ^ 63 * 2 ^ L = 2 ^ (L + 1) * 2 ^ 62 by rw [← pow_add, ← pow_add]; congr 1; omega]
      exact Nat.mul_lt_mul_of_pos_right hhi (by positivity)
    exact Nat.lt_of_mul_lt_mul_right this
  refine WP.spec_bind (UScalar.sub_spec (x := fulcrum.tables.exp.FRAC) (y := fulcrum.tables.exp.STEPS)
    (by rw [exp_frac_val, exp_steps_val]; norm_num)) fun i ⟨hi, _⟩ => ?_
  rw [exp_frac_val, exp_steps_val] at hi
  norm_num at hi
  refine WP.spec_bind (UScalar.ShiftRight_spec u i (by rw [hi, n64]; norm_num)) fun i1 ⟨h1, _⟩ => ?_
  rw [hi, Nat.shiftRight_eq_div_pow] at h1
  refine WP.spec_bind (UScalar.ShiftLeft_spec 1#u64 fulcrum.tables.exp.STEPS _
    (by rw [exp_steps_val, n64]; norm_num) rfl) fun i2 ⟨h2, _⟩ => ?_
  rw [exp_steps_val, lit_val, Nat.shiftLeft_eq, one_mul, UScalar.size_def, n64] at h2
  norm_num at h2
  have q1 : 256 ≤ i1.val := by rw [h1]; exact (Nat.le_div_iff_mul_le (by positivity)).mpr (by omega)
  have q2 : i1.val < 512 := by rw [h1, Nat.div_lt_iff_lt_mul (by positivity)]; omega
  refine WP.spec_bind (UScalar.sub_spec (x := i1) (y := i2) (by omega)) fun k ⟨hk, _⟩ => ?_
  have k256 : k.val < 256 := by omega
  refine WP.spec_bind (UScalar.ShiftLeft_spec k i _ (by rw [hi, n64]; norm_num) rfl) fun i3 ⟨h3, _⟩ => ?_
  rw [hi, Nat.shiftLeft_eq, UScalar.size_def, n64, Nat.mod_eq_of_lt (by omega)] at h3
  refine WP.spec_bind exp_one_spec fun i4 h4 => ?_
  refine WP.spec_bind (UScalar.add_spec (x := i4) (y := i3) (by rw [h4, h3, U64_max_val]; omega)) fun c hc => ?_
  have cv : c.val = 2 ^ 62 + k.val * 2 ^ 54 := by rw [hc, h4, h3]
  have Cle : c.val ≤ u.val := by
    rw [cv, hk, h1, h2]
    have := Nat.div_mul_le_self u.val (2 ^ 54)
    omega
  have rl : u.val - c.val < 2 ^ 54 := by
    rw [cv, hk, h1, h2]
    have := Nat.lt_div_mul_add (a := u.val) (b := 2 ^ 54) (by positivity)
    omega
  refine WP.spec_bind (UScalar.add_spec (x := u) (y := c) (by rw [U64_max_val]; omega)) fun i6 h6 => ?_
  rw [lift, bind_ok]
  refine WP.spec_bind (UScalar.sub_spec (x := u) (y := c) Cle) fun i7 ⟨h7, _⟩ => ?_
  rw [lift, bind_ok]
  have dv : (UScalar.cast .U128 i6).val = u.val + c.val := by rw [cast_u128_val, h6]
  have rv : (UScalar.cast .U128 i7).val = u.val - c.val := by rw [cast_u128_val, h7]
  generalize UScalar.cast .U128 i6 = d at dv ⊢
  generalize UScalar.cast .U128 i7 = r at rv ⊢
  have dpos : 0 < d.val := by omega
  have dl : d.val < 2 ^ 64 := by omega
  refine WP.spec_bind (shl_i32_spec r 64#i32 64 rfl (by rw [n128]; norm_num) (by
    rw [n128, rv]
    calc (u.val - c.val) * 2 ^ 64 < 2 ^ 54 * 2 ^ 64 := Nat.mul_lt_mul_of_pos_right rl (by positivity)
      _ ≤ 2 ^ 128 := by norm_num)) fun i8 h8 => ?_
  obtain ⟨high, ehigh, hhigh⟩ := UScalar.div_spec i8 (y := d) dpos.ne'
  rw [ehigh, bind_ok]
  refine WP.spec_bind (UScalar.rem_spec i8 (y := d) dpos.ne') fun i9 hi9 => ?_
  have i9l : i9.val < d.val := by rw [hi9]; exact Nat.mod_lt _ dpos
  refine WP.spec_bind (shl_i32_spec i9 64#i32 64 rfl (by rw [n128]; norm_num) (by
    rw [n128]
    calc i9.val * 2 ^ 64 < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul_of_pos_right (i9l.trans dl) (by positivity)
      _ = 2 ^ 128 := by norm_num)) fun i10 h10 => ?_
  obtain ⟨low, elow, hlow⟩ := UScalar.div_spec i10 (y := d) dpos.ne'
  rw [elow, bind_ok]
  have lowl : low.val < 2 ^ 64 := by
    rw [hlow, h10, Nat.div_lt_iff_lt_mul dpos]
    exact Nat.mul_lt_mul_of_pos_right i9l (by positivity) |>.trans_le (by rw [mul_comm])
  have highl : high.val < 2 ^ 55 := by
    rw [hhigh, h8, rv, Nat.div_lt_iff_lt_mul dpos]
    calc (u.val - c.val) * 2 ^ 64 < 2 ^ 54 * 2 ^ 64 := Nat.mul_lt_mul_of_pos_right rl (by positivity)
      _ = 2 ^ 55 * 2 ^ 63 := by norm_num
      _ ≤ 2 ^ 55 * d.val := Nat.mul_le_mul_left _ (by omega)
  refine WP.spec_bind (shl_i32_spec high 64#i32 64 rfl (by rw [n128]; norm_num) (by
    rw [n128]
    calc high.val * 2 ^ 64 < 2 ^ 55 * 2 ^ 64 := Nat.mul_lt_mul_of_pos_right highl (by positivity)
      _ ≤ 2 ^ 128 := by norm_num)) fun i11 h11 => ?_
  rw [lift, bind_ok]
  have sv : (i11 ||| low).val = (u.val - c.val) * 2 ^ 128 / (u.val + c.val) := by
    rw [UScalar.val_or, h11, mul_comm, ← Nat.two_pow_add_eq_or_of_lt lowl, mul_comm, hlow, h10, hi9, hhigh, h8, rv, dv,
      div_two_words _ _ (by omega), mul_assoc, ← pow_add]
  generalize i11 ||| low = s at sv ⊢
  have sl : s.val ≤ 2 ^ 119 := by
    rw [sv]
    refine Nat.div_le_of_le_mul ?_
    calc (u.val - c.val) * 2 ^ 128 ≤ 2 ^ 54 * 2 ^ 128 := Nat.mul_le_mul_right _ rl.le
      _ = 2 ^ 119 * 2 ^ 63 := by norm_num
      _ ≤ 2 ^ 119 * (u.val + c.val) := Nat.mul_le_mul_left _ (by omega)
      _ = (u.val + c.val) * 2 ^ 119 := mul_comm _ _
  refine WP.spec_bind (mul_hi_spec s s) fun z hz => ?_
  have zl : z.val ≤ 2 ^ 110 := by
    rw [hz]; exact Nat.div_le_of_le_mul ((Nat.mul_le_mul sl sl).trans (by norm_num))
  refine WP.spec_bind (u128_div_spec _ 13#u128 13 (lit_val _ (by decide)) (by norm_num)) fun g hg => ?_
  rw [u128_max_val] at hg
  refine horner_wide_spec z g 11#u128 (by rw [lit_val _ (by decide)]; omega) zl _ _ fun g1 hg1 => ?_
  refine horner_wide_spec z g1 9#u128 (by rw [lit_val _ (by decide)]; omega) zl _ _ fun g2 hg2 => ?_
  refine horner_wide_spec z g2 7#u128 (by rw [lit_val _ (by decide)]; omega) zl _ _ fun g3 hg3 => ?_
  refine horner_wide_spec z g3 5#u128 (by rw [lit_val _ (by decide)]; omega) zl _ _ fun g4 hg4 => ?_
  refine horner_wide_spec z g4 3#u128 (by rw [lit_val _ (by decide)]) zl _ _ fun g5 hg5 => ?_
  refine WP.spec_bind (mul_hi_spec z g5) fun i22 h22 => ?_
  refine WP.spec_bind (mul_hi_spec s i22) fun i23 h23 => ?_
  have i23l : i23.val ≤ 2 ^ 119 := by rw [h23]; exact (mul128_le_left _ _ i22.bv.isLt.le).trans sl
  refine WP.spec_bind (UScalar.add_spec (x := s) (y := i23) (by rw [U128_max_val]; omega)) fun at' hat => ?_
  rw [lift, bind_ok]
  have ck := usize_cast_val k (by omega)
  refine WP.spec_bind (log2_wide_table_spec _ (by rw [ck]; exact k256)) fun T ⟨hT, TU⟩ => ?_
  rw [ck] at hT
  refine WP.spec_bind (mul_hi_spec at' fulcrum.tables.exp.TWO_LOG2_E_WIDE) fun i26 h26 => ?_
  have i26l : i26.val ≤ 2 ^ 120 := by
    rw [h26]
    exact Nat.div_le_of_le_mul ((Nat.mul_le_mul (show at'.val ≤ 2 ^ 120 by omega)
      fulcrum.tables.exp.TWO_LOG2_E_WIDE.bv.isLt.le).trans (by rw [mul_comm]))
  refine WP.spec_bind (UScalar.add_spec (x := T) (y := i26) (by rw [U128_max_val]; omega)) fun l hl => ?_
  have lv : l.val = log2WideN T.val s.val fulcrum.tables.exp.TWO_LOG2_E_WIDE.val := by
    rw [hl, h26, hat, h23, h22, hg5, hg4, hg3, hg2, hg1, hg, hz]
    simp only [lit_val]
    rfl
  have ll : l.val ≤ 2 ^ 126 + 2 ^ 120 := by omega
  set σ : ℝ := ((u.val : ℝ) - c.val) / ((u.val : ℝ) + c.val) with hσ
  have Cp : (0 : ℝ) < c.val := by rw [cv]; positivity
  have CU : (c.val : ℝ) ≤ u.val := by exact_mod_cast Cle
  have σ0 : 0 ≤ σ := div_nonneg (by linarith) (by positivity)
  have σM : σ ≤ 1 / 512 := by
    rw [hσ, div_le_iff₀ (by positivity)]
    have : ((u.val - c.val : ℕ) : ℝ) < 2 ^ 54 := by exact_mod_cast rl
    rw [Nat.cast_sub Cle] at this
    have : (2 : ℝ) ^ 62 ≤ u.val := by exact_mod_cast Ug
    have : (2 : ℝ) ^ 62 ≤ c.val := by exact_mod_cast (show 2 ^ 62 ≤ c.val by omega)
    linarith
  have ⟨fl, fu⟩ := floor_div_near ((u.val - c.val) * 2 ^ 128) (u.val + c.val) (by omega)
  rw [← sv] at fl fu
  rw [Nat.cast_mul, Nat.cast_sub Cle, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat] at fl fu
  have hsσ : (s.val : ℝ) ≤ σ * 2 ^ 128 := by rw [hσ, div_mul_eq_mul_div]; exact fl
  have hsσ' : σ * 2 ^ 128 < s.val + 1 := by rw [hσ, div_mul_eq_mul_div]; linarith
  have cR : (1 : ℝ) + (k.val : ℝ) / 256 = c.val / 2 ^ 62 := by rw [cv]; push_cast; field_simp; ring
  rw [cR] at hT
  have near := log2_wide_series_near T.val s.val fulcrum.tables.exp.TWO_LOG2_E_WIDE.val _ σ hT
    two_log2_e_wide_entry σ0 σM hsσ hsσ'
  rw [hσ, log2_split _ _ Cp CU, ← lv] at near
  set S := Real.logb 2 ((u.val : ℝ) / 2 ^ 62) with hS
  have uR : (u.val : ℝ) / 2 ^ 62 = (a.val : ℝ) / 2 ^ L := by
    have : (u.val : ℝ) * 2 ^ L = a.val * 2 ^ 62 := by exact_mod_cast hu
    field_simp; linarith
  have ap : (0 : ℝ) < a.val := by exact_mod_cast ha0
  have S0 : 0 ≤ S := by
    rw [hS]; exact Real.logb_nonneg one_lt_two (by
      rw [le_div_iff₀ (by positivity), one_mul]; exact_mod_cast Ug)
  have S1 : S < 1 := by
    rw [hS, Real.logb_lt_iff_lt_rpow (by norm_num) (by positivity), Real.rpow_one, div_lt_iff₀ (by positivity)]
    have : (u.val : ℝ) < 2 ^ 63 := by exact_mod_cast Ul
    linarith
  rw [lift, bind_ok, lift, bind_ok]
  have ec : (UScalar.hcast .I128 e).val = (L : ℤ) := by
    rw [UScalar.hcast_val_eq, IScalarTy.I128_numBits_eq, ev]
    exact Int.bmod_eq_of_le (by push_cast; omega) (by push_cast; omega)
  have fc : (UScalar.hcast .I128 f).val = (f.val : ℤ) := by
    rw [UScalar.hcast_val_eq, IScalarTy.I128_numBits_eq]
    exact Int.bmod_eq_of_le (by push_cast; omega) (by push_cast; omega)
  have mn2 : IScalar.min .I128 = -2 ^ 127 := min_eq_neg_pow IScalarTy.I128_numBits_eq
  have mx2 : IScalar.max .I128 = 2 ^ 127 - 1 := max_eq_pow_sub_one IScalarTy.I128_numBits_eq
  refine WP.spec_bind (IScalar.sub_spec (x := UScalar.hcast .I128 e) (y := UScalar.hcast .I128 f)
    (by rw [ec, fc, mn2]; omega) (by rw [ec, fc, mx2]; omega)) fun i29 h29 => ?_
  rw [ec, fc] at h29
  refine WP.spec_bind (IScalar.ShiftLeft_spec i29 fulcrum.exp.W_FRAC
    (by rw [w_frac_val, IScalarTy.I128_numBits_eq]; norm_num)) fun i30 ⟨h30, _⟩ => ?_
  have i30v : i30.val = ((L : ℤ) - f.val) * 2 ^ 120 := by
    rw [h30, Int.shiftLeft_eq, h29, w_frac_val, IScalarTy.I128_numBits_eq]
    have lb : -(32 : ℤ) * 2 ^ 120 ≤ ((L : ℤ) - f.val) * 2 ^ 120 := by
      have : -(32 : ℤ) ≤ (L : ℤ) - f.val := by omega
      exact mul_le_mul_of_nonneg_right this (by positivity)
    have ub : ((L : ℤ) - f.val) * 2 ^ 120 ≤ 63 * 2 ^ 120 := by
      have : (L : ℤ) - f.val ≤ 63 := by omega
      exact mul_le_mul_of_nonneg_right this (by positivity)
    exact Int.bmod_eq_of_le (by push_cast; omega) (by push_cast; omega)
  refine WP.spec_bind (UScalar.sub_spec (x := fulcrum.tables.exp.WIDE_FRAC) (y := fulcrum.exp.W_FRAC)
    (by rw [wide_frac_val, w_frac_val]; norm_num)) fun i31 ⟨h31, _⟩ => ?_
  rw [wide_frac_val, w_frac_val] at h31
  refine WP.spec_bind (UScalar.ShiftRight_spec l i31 (by rw [h31, n128]; norm_num)) fun i32 ⟨h32, _⟩ => ?_
  rw [h31, Nat.shiftRight_eq_div_pow, show (126 - 120 : ℕ) = 6 from rfl] at h32
  have i32l : i32.val < 2 ^ 121 := by rw [h32, Nat.div_lt_iff_lt_mul (by positivity)]; omega
  rw [lift, bind_ok]
  have pc : (UScalar.hcast .I128 i32).val = (i32.val : ℤ) := by
    rw [UScalar.hcast_val_eq, IScalarTy.I128_numBits_eq]
    exact Int.bmod_eq_of_le ((neg_nonpos.mpr (by positivity)).trans (Int.natCast_nonneg _))
      ((by exact_mod_cast i32l : (i32.val : ℤ) < 2 ^ 121).trans_le (by norm_num))
  have i30b : -(32 : ℤ) * 2 ^ 120 ≤ i30.val ∧ i30.val ≤ 63 * 2 ^ 120 := by
    rw [i30v]
    constructor
    · have : -(32 : ℤ) ≤ (L : ℤ) - f.val := by omega
      exact mul_le_mul_of_nonneg_right this (by positivity)
    · have : (L : ℤ) - f.val ≤ 63 := by omega
      exact mul_le_mul_of_nonneg_right this (by positivity)
  refine WP.spec_mono (IScalar.add_spec (x := i30) (y := UScalar.hcast .I128 i32)
    (by rw [pc, mn2]; omega) (by rw [pc, mx2]; omega)) fun r hr => ?_
  rw [hr, i30v, pc]
  have h32' : i32.val = l.val / 64 := by rw [h32]
  have dn := div_near l.val 64 (S * 2 ^ 126) 3 (by norm_num) near
  rw [← h32'] at dn
  have tgt : Real.logb 2 ((a.val : ℝ) / 2 ^ f.val) * 2 ^ 120 = ((L : ℝ) - f.val) * 2 ^ 120 + S * 2 ^ 120 := by
    rw [hS, uR, logb2_div_pow _ ap, logb2_div_pow _ ap]; ring
  have key : (((((L : ℤ) - f.val) * 2 ^ 120 + (i32.val : ℤ) : ℤ)) : ℝ) -
      (((L : ℝ) - f.val) * 2 ^ 120 + S * 2 ^ 120) = (i32.val : ℝ) - S * 2 ^ 126 / 64 := by
    push_cast; ring
  refine ⟨?_, ?_⟩
  · rw [tgt, key]
    exact dn.trans (by norm_num)
  · have ib : (i32.val : ℝ) ≤ 2 ^ 120 + 2 := by
      have := (abs_le.mp dn).2
      have : S * 2 ^ 126 ≤ 1 * 2 ^ 126 := mul_le_mul_of_nonneg_right S1.le (by positivity)
      linarith
    have ib' : i32.val ≤ 2 ^ 120 + 2 := by exact_mod_cast ib
    have lo : -(32 : ℤ) * 2 ^ 120 ≤ ((L : ℤ) - f.val) * 2 ^ 120 := by
      have : -(32 : ℤ) ≤ (L : ℤ) - f.val := by omega
      exact mul_le_mul_of_nonneg_right this (by positivity)
    have hi' : ((L : ℤ) - f.val) * 2 ^ 120 ≤ 63 * 2 ^ 120 := by
      have : (L : ℤ) - f.val ≤ 63 := by omega
      exact mul_le_mul_of_nonneg_right this (by positivity)
    omega

/-- `2^(w / 2^120) · 2^f · 2^s = 2^(t / 2^120) · 2^126` for `w = 2^120 · n + t` and
`s = 126 - f - n`. -/
theorem exp2_wide_scale (w n : ℤ) (f s : ℕ) (t : ℝ) (h : (w : ℝ) = 2 ^ 120 * n + t) (hs : (s : ℤ) = 126 - f - n) :
    (2 : ℝ) ^ ((w : ℝ) / 2 ^ 120) * 2 ^ f * 2 ^ s = (2 : ℝ) ^ (t / 2 ^ 120) * 2 ^ 126 := by
  have e : (w : ℝ) / 2 ^ 120 = (n : ℝ) + t / 2 ^ 120 := by rw [h]; field_simp
  have p : (2 : ℝ) ^ n * 2 ^ f * 2 ^ s = 2 ^ 126 := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ two_ne_zero, ← zpow_add₀ two_ne_zero]
    congr 1
    omega
  rw [e, Real.rpow_add two_pos, Real.rpow_intCast, ← p]
  ring

/-- L4 on the code: `exp::exp2_wide(w, f)` with `1 ≤ f ≤ 32` never fails; it returns the mark
`2^(2f)` when `⌊w / 2^120⌋ ≥ f`, and otherwise a value within `½ + 2.2 · 2^(2f) / 2^71` of
`2^(w / 2^120) · 2^f`. -/
theorem exp2_wide_spec (w : Std.I128) (f : Std.U32) (hf1 : 1 ≤ f.val) (hf : f.val ≤ 32) :
    fulcrum.exp.exp2_wide w f ⦃ r =>
      ((f.val : ℤ) ≤ w.val / 2 ^ 120 ∧ r.val = 2 ^ (2 * f.val)) ∨
      (w.val / 2 ^ 120 < f.val ∧
        |(r.val : ℝ) - (2 : ℝ) ^ ((w.val : ℝ) / 2 ^ 120) * 2 ^ f.val| ≤ 1 / 2 + 22 / 10 * 2 ^ (2 * f.val) / 2 ^ 71) ⦄ := by
  have n128 : UScalarTy.U128.numBits = 128 := rfl
  unfold fulcrum.exp.exp2_wide
  refine WP.spec_bind (IScalar.ShiftRight_spec w fulcrum.exp.W_FRAC
    (by rw [w_frac_val, IScalarTy.I128_numBits_eq]; norm_num)) fun i ⟨hi, _⟩ => ?_
  rw [shr_eq_div, w_frac_val] at hi
  have ⟨wl, wu⟩ := val_bounds w IScalarTy.I128_numBits_eq
  have nlo : -2 ^ 7 ≤ i.val := by rw [hi, Int.le_ediv_iff_mul_le (by norm_num)]; omega
  have nhi : i.val < 2 ^ 7 := by rw [hi, Int.ediv_lt_iff_lt_mul (by norm_num)]; omega
  have inr : InRange 63 i.val :=
    ⟨(by unfold minOf; norm_num : minOf 63 ≤ -2 ^ 7).trans nlo, nhi.le.trans (by unfold maxOf; norm_num)⟩
  have nv : (IScalar.cast .I64 i).val = w.val / 2 ^ 120 :=
    ((IScalar.cast_val_eq .I64 i).trans ((wrap_eq_self_iff 63 _).2 inr)).trans hi
  rw [lift, bind_ok, lift, bind_ok]
  generalize IScalar.cast .I64 i = n at nv ⊢
  have fc := f_i64_val f hf
  by_cases ho : n >= UScalar.hcast .I64 f
  · have : (UScalar.hcast .I64 f).val ≤ n.val := ho
    rw [ite_eq_left ho]
    exact WP.spec_mono (overflow_spec f hf) fun r hr => Or.inl ⟨by rw [← nv]; omega, hr⟩
  have nlt : n.val < f.val := by
    have : ¬ (UScalar.hcast .I64 f).val ≤ n.val := ho
    omega
  rw [ite_eq_right ho, lift, bind_ok]
  refine WP.spec_bind (UScalar.ShiftLeft_spec 1#u128 fulcrum.exp.W_FRAC _
    (by rw [w_frac_val, n128]; norm_num) rfl) fun i3 ⟨h3, _⟩ => ?_
  rw [w_frac_val, lit_val, Nat.shiftLeft_eq, one_mul, UScalar.size_def, n128] at h3
  norm_num at h3
  refine WP.spec_bind (UScalar.sub_spec (x := i3) (y := 1#u128) (by rw [h3, lit_val]; norm_num))
    fun i4 ⟨h4, _⟩ => ?_
  rw [h3, lit_val] at h4
  rw [lift, bind_ok]
  have p128 : (2 : ℤ) ^ 120 ∣ 2 ^ 128 := pow_dvd_pow 2 (by norm_num)
  have tv : (IScalar.hcast .U128 w &&& i4).val = (w.val % 2 ^ 120).toNat := by
    rw [UScalar.val_and, h4, show (1329227995784915872903807060280344576 - 1 : ℕ) = 2 ^ 120 - 1 by norm_num,
      Nat.and_two_pow_sub_one_eq_mod, IScalar.hcast_val_eq, n128]
    have nn : 0 ≤ w.val % 2 ^ 128 := Int.emod_nonneg _ (by positivity)
    have : ((w.val % 2 ^ 128).toNat % 2 ^ 120 : ℕ) = ((w.val % 2 ^ 128) % 2 ^ 120).toNat := by
      rw [Int.toNat_emod nn (by positivity)]; rfl
    rw [this, Int.emod_emod_of_dvd _ p128]
  generalize IScalar.hcast .U128 w &&& i4 = t at tv ⊢
  have tl : t.val < 2 ^ 120 := by
    rw [tv]
    have a := Int.emod_lt_of_pos w.val (by positivity : (0 : ℤ) < 2 ^ 120)
    have b := Int.emod_nonneg w.val (by positivity : (2 : ℤ) ^ 120 ≠ 0)
    have : ((w.val % 2 ^ 120).toNat : ℤ) < ((2 ^ 120 : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg b]; push_cast; exact a
    exact_mod_cast this
  have tR : (t.val : ℝ) = ((w.val % 2 ^ 120 : ℤ) : ℝ) := by
    rw [tv]; exact_mod_cast Int.toNat_of_nonneg (Int.emod_nonneg _ (by positivity))
  have st : fulcrum.tables.exp.STEPS.val = 8 := exp_steps_val
  refine WP.spec_bind (UScalar.sub_spec (x := fulcrum.exp.W_FRAC) (y := fulcrum.tables.exp.STEPS)
    (by rw [w_frac_val, st]; norm_num)) fun rest ⟨hr, _⟩ => ?_
  rw [w_frac_val, st] at hr
  norm_num at hr
  refine WP.spec_bind (UScalar.ShiftRight_spec t rest (by rw [hr, n128]; norm_num)) fun i5 ⟨h5, _⟩ => ?_
  rw [Nat.shiftRight_eq_div_pow, hr] at h5
  have kl : i5.val < 256 := by rw [h5, Nat.div_lt_iff_lt_mul (by positivity)]; omega
  rw [lift, bind_ok]
  have kv : (UScalar.cast .U64 i5).val = i5.val := by
    rw [cast_u64_val, Nat.mod_eq_of_lt (by omega)]
  generalize UScalar.cast .U64 i5 = k at kv ⊢
  refine WP.spec_bind (UScalar.ShiftLeft_spec 1#u128 rest _ (by rw [hr, n128]; norm_num) rfl)
    fun i6 ⟨h6, _⟩ => ?_
  rw [hr, lit_val, Nat.shiftLeft_eq, one_mul, UScalar.size_def, n128] at h6
  norm_num at h6
  refine WP.spec_bind (UScalar.sub_spec (x := i6) (y := 1#u128) (by rw [h6, lit_val]; norm_num))
    fun i7 ⟨h7, _⟩ => ?_
  rw [h6, lit_val] at h7
  rw [lift, bind_ok]
  have rv : (t &&& i7).val = t.val % 2 ^ 112 := by
    rw [UScalar.val_and, h7, show (5192296858534827628530496329220096 - 1 : ℕ) = 2 ^ 112 - 1 by norm_num,
      Nat.and_two_pow_sub_one_eq_mod]
  generalize t &&& i7 = r at rv ⊢
  have rl : r.val < 2 ^ 112 := by rw [rv]; exact Nat.mod_lt _ (by positivity)
  refine WP.spec_bind (UScalar.sub_spec (x := fulcrum.exp.W_FRAC) (y := fulcrum.exp.EXPM1_FRAC)
    (by rw [w_frac_val, expm1_frac_val]; norm_num)) fun i8 ⟨h8, _⟩ => ?_
  rw [w_frac_val, expm1_frac_val] at h8
  norm_num at h8
  refine WP.spec_bind (UScalar.ShiftRight_spec r i8 (by rw [h8, n128]; norm_num)) fun i9 ⟨h9, _⟩ => ?_
  rw [Nat.shiftRight_eq_div_pow, h8] at h9
  have i9l : i9.val < 2 ^ 64 := by rw [h9, Nat.div_lt_iff_lt_mul (by positivity)]; omega
  refine WP.spec_bind (UScalar.sub_spec (x := fulcrum.tables.exp.LN_2_FRAC) (y := 64#u32)
    (by rw [ln_2_frac_val, lit_val]; norm_num)) fun i10 ⟨h10, _⟩ => ?_
  rw [ln_2_frac_val, lit_val] at h10
  refine WP.spec_bind (UScalar.ShiftRight_spec fulcrum.tables.exp.LN_2 i10 (by rw [h10, n128]; norm_num))
    fun i11 ⟨h11, _⟩ => ?_
  rw [h10, Nat.shiftRight_eq_div_pow, show (104 - 64 : ℕ) = 40 from rfl] at h11
  have i11l : i11.val < 2 ^ 64 := by rw [h11, ln_2_val]; norm_num
  refine WP.spec_bind (UScalar.mul_spec (x := i9) (y := i11) (by
    rw [U128_max_val]
    have := Nat.mul_le_mul (Nat.le_pred_of_lt i9l) (Nat.le_pred_of_lt i11l)
    exact this.trans (by norm_num))) fun i12 h12 => ?_
  refine WP.spec_bind (shr_i32_spec i12 64#i32 64 rfl (by rw [n128]; norm_num)) fun i13 h13 => ?_
  rw [h12] at h13
  have ylim : i13.val ≤ fulcrum.tables.exp.LN_2.val / 2 ^ 40 := by
    rw [h13, ← h11]
    exact Nat.div_le_of_le_mul (by rw [mul_comm, mul_comm (2 ^ 64)]; exact Nat.mul_le_mul_left _ i9l.le)
  rw [lift, bind_ok]
  have yv : (UScalar.cast .U64 i13).val = i13.val := by
    rw [cast_u64_val, Nat.mod_eq_of_lt (lt_of_le_of_lt ylim (by rw [ln_2_val]; norm_num))]
  refine WP.spec_bind (exp_unit_spec k _ (by rw [kv]; exact kl) (yv ▸ ylim)) fun m ⟨hm, mtop⟩ => ?_
  rw [yv, kv] at hm
  have mlt : m.val < 2 ^ 127 := by omega
  refine WP.spec_mono (round_mantissa_spec m n f mlt (by omega) (by omega) hf) fun res hres => Or.inr ⟨by rw [← nv]; exact nlt, ?_⟩
  rw [hres]
  set X : ℝ := (2 : ℝ) ^ ((w.val : ℝ) / 2 ^ 120) * 2 ^ f.val with hX
  set sh : ℕ := (126 - f.val - n.val).toNat with hsd
  have sv : (sh : ℤ) = 126 - f.val - n.val := Int.toNat_of_nonneg (by omega)
  have split : (w.val : ℝ) = 2 ^ 120 * (n.val : ℝ) + t.val := by
    rw [tR, nv]; exact_mod_cast (Int.mul_ediv_add_emod w.val (2 ^ (120 : ℕ))).symm
  have sc := exp2_wide_scale w.val n.val f.val sh t.val split sv
  rw [← hX] at sc
  have tk : (t.val : ℝ) / 2 ^ 120 = (i5.val : ℝ) / 256 + r.val / 2 ^ 120 := by
    have d : (t.val : ℝ) = (i5.val : ℝ) * 2 ^ 112 + r.val := by
      rw [h5, rv]; exact_mod_cast (Nat.div_add_mod' t.val (2 ^ 112)).symm
    rw [d]; field_simp; ring
  set A : ℝ := (i13.val : ℝ) / 2 ^ 72 with hA
  set B : ℝ := Real.log 2 * (r.val / 2 ^ 120) with hB
  have tgt : (2 : ℝ) ^ ((t.val : ℝ) / 2 ^ 120) = (2 : ℝ) ^ ((i5.val : ℝ) / 256) * Real.exp B := by
    rw [tk, Real.rpow_add two_pos, Real.rpow_def_of_pos two_pos ((r.val : ℝ) / 2 ^ 120)]
  have top : (2 : ℝ) ^ ((i5.val : ℝ) / 256) * Real.exp B ≤ 2 := by
    rw [← tgt]
    calc (2 : ℝ) ^ ((t.val : ℝ) / 2 ^ 120) ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le one_le_two (by
          rw [div_le_one (by positivity)]; exact_mod_cast tl.le)
      _ = 2 := Real.rpow_one 2
  have ⟨elam, lamM⟩ := ln_2_hi_near
  rw [← h11] at elam lamM
  have l0 := log_two_ge'
  have dAB : |A - B| ≤ 27 / 10 / 2 ^ 72 := by
    have ⟨ya, yb⟩ := floor_div_near (i9.val * i11.val) (2 ^ 64) (by positivity)
    rw [← h13] at ya yb
    have ⟨ra, rb⟩ := floor_div_near r.val (2 ^ 48) (by positivity)
    rw [← h9] at ra rb
    push_cast at ya yb ra rb
    have r0 : (0 : ℝ) ≤ r.val / 2 ^ 48 := by positivity
    have rM : (r.val : ℝ) / 2 ^ 48 ≤ 2 ^ 64 := by
      rw [div_le_iff₀ (by positivity)]
      have : (r.val : ℝ) < 2 ^ 112 := by exact_mod_cast rl
      linarith
    have core : |(i9.val : ℝ) * i11.val / 2 ^ 64 - r.val / 2 ^ 48 * Real.log 2| ≤ 16942 / 10000 := by
      rw [show (i9.val : ℝ) * i11.val / 2 ^ 64 - r.val / 2 ^ 48 * Real.log 2 =
        (((i9.val : ℝ) - r.val / 2 ^ 48) * i11.val + r.val / 2 ^ 48 * ((i11.val : ℝ) - Real.log 2 * 2 ^ 64)) / 2 ^ 64 by
          ring, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 64), div_le_iff₀ (by positivity)]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) i11.val), abs_of_nonneg r0]
      have t1 : |(i9.val : ℝ) - r.val / 2 ^ 48| * (i11.val : ℝ) ≤ 1 * (6932 / 10000 * 2 ^ 64) :=
        mul_le_mul (abs_le.mpr ⟨by linarith, by linarith⟩) lamM (Nat.cast_nonneg _) zero_le_one
      have t2 : (r.val : ℝ) / 2 ^ 48 * |(i11.val : ℝ) - Real.log 2 * 2 ^ 64| ≤ 2 ^ 64 * (1001 / 1000) :=
        mul_le_mul rM elam (abs_nonneg _) (by positivity)
      linarith
    rw [hA, hB, show (i13.val : ℝ) / 2 ^ 72 - Real.log 2 * (r.val / 2 ^ 120) =
      ((i13.val : ℝ) - r.val / 2 ^ 48 * Real.log 2) / 2 ^ 72 by ring, abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 72)]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have ⟨c1, c2⟩ := abs_le.mp core
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have es := exp_shift_near A B _ (1 / 2 ^ 60) dAB (by norm_num) (by norm_num)
  have T0 : (0 : ℝ) ≤ (2 : ℝ) ^ ((i5.val : ℝ) / 256) := by positivity
  refine (mantissa_round_near m.val n.val f.val 0 X (22 / 10 * 2 ^ 56) mlt hf (by omega) (by positivity) (by positivity)
    ?_ ?_).trans_eq (by ring)
  · rw [sc, tgt]
    exact (mul_le_mul_of_nonneg_right top (by positivity)).trans (by norm_num)
  rw [sc, tgt]
  calc |(m.val : ℝ) - (2 : ℝ) ^ ((i5.val : ℝ) / 256) * Real.exp B * 2 ^ 126|
      ≤ |(m.val : ℝ) - (2 : ℝ) ^ ((i5.val : ℝ) / 256) * Real.exp A * 2 ^ 126| +
        |(2 : ℝ) ^ ((i5.val : ℝ) / 256) * 2 ^ 126 * (Real.exp A - Real.exp B)| := by
        rw [show (m.val : ℝ) - (2 : ℝ) ^ ((i5.val : ℝ) / 256) * Real.exp B * 2 ^ 126 =
          ((m.val : ℝ) - (2 : ℝ) ^ ((i5.val : ℝ) / 256) * Real.exp A * 2 ^ 126) +
            (2 : ℝ) ^ ((i5.val : ℝ) / 256) * 2 ^ 126 * (Real.exp A - Real.exp B) by ring]
        exact abs_add_le _ _
    _ ≤ 81 / 100 * 2 ^ 56 + 2 ^ 126 * (2 * ((1 + 1 / 2 ^ 60) * (27 / 10 / 2 ^ 72))) := by
        refine add_le_add hm ?_
        rw [abs_mul, abs_of_nonneg (by positivity), show (2 : ℝ) ^ ((i5.val : ℝ) / 256) * 2 ^ 126 *
          |Real.exp A - Real.exp B| = 2 ^ 126 * ((2 : ℝ) ^ ((i5.val : ℝ) / 256) * |Real.exp A - Real.exp B|) by ring]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc (2 : ℝ) ^ ((i5.val : ℝ) / 256) * |Real.exp A - Real.exp B|
            ≤ (2 : ℝ) ^ ((i5.val : ℝ) / 256) * (Real.exp B * ((1 + 1 / 2 ^ 60) * (27 / 10 / 2 ^ 72))) :=
              mul_le_mul_of_nonneg_left es T0
          _ = (2 : ℝ) ^ ((i5.val : ℝ) / 256) * Real.exp B * ((1 + 1 / 2 ^ 60) * (27 / 10 / 2 ^ 72)) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right top (by positivity)
    _ ≤ 22 / 10 * 2 ^ 56 := by norm_num

/-- `⌊|y| · |l| / 2^fy⌋` is within `1` of `|y · l| / 2^fy`, and not above it. -/
theorem natAbs_mul_div_near (y l : ℤ) (fy : ℕ) :
    0 ≤ |(y : ℝ) * l| / 2 ^ fy - ((y.natAbs * l.natAbs / 2 ^ fy : ℕ) : ℝ) ∧
      |(y : ℝ) * l| / 2 ^ fy - ((y.natAbs * l.natAbs / 2 ^ fy : ℕ) : ℝ) < 1 := by
  have ⟨a, b⟩ := floor_div_near (y.natAbs * l.natAbs) (2 ^ fy) (by positivity)
  have e : ((y.natAbs * l.natAbs : ℕ) : ℝ) = |(y : ℝ) * l| := by
    rw [abs_mul, Nat.cast_mul, Nat.cast_natAbs, Nat.cast_natAbs, Int.cast_abs, Int.cast_abs]
  rw [e] at a b
  push_cast at a b
  constructor <;> linarith

/-- `2^(w / 2^120)` against `2^P` for `w` within `1.05 Y + 1` of `P · 2^120`, `0 ≤ Y ≤ 2^63`:
a value within `E` of `2^(w / 2^120) · 2^f` is within `E + 2^P · 2^f · (Y + 1) / 2^120` of
`2^P · 2^f`. -/
theorem pow_tail_near (w P Y E r : ℝ) (f : ℕ) (hY0 : 0 ≤ Y) (hY : Y ≤ 2 ^ 63)
    (hw : |w - P * 2 ^ 120| ≤ 105 / 100 * Y + 1) (hr : |r - (2 : ℝ) ^ (w / 2 ^ 120) * 2 ^ f| ≤ E) :
    |r - (2 : ℝ) ^ P * 2 ^ f| ≤ E + (2 : ℝ) ^ P * 2 ^ f * (Y + 1) / 2 ^ 120 := by
  have l0 := log_two_ge'
  have l1 := log_two_le'
  have d : |Real.log 2 * (w / 2 ^ 120) - Real.log 2 * P| ≤ Real.log 2 * ((105 / 100 * Y + 1) / 2 ^ 120) := by
    rw [show Real.log 2 * (w / 2 ^ 120) - Real.log 2 * P = Real.log 2 * ((w - P * 2 ^ 120) / 2 ^ 120) by ring,
      abs_mul, abs_of_pos (by linarith), abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 120)]
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hw (by positivity)) (by linarith)
  have dc : Real.log 2 * ((105 / 100 * Y + 1) / 2 ^ 120) ≤ 1 / 2 ^ 50 := by
    have : (105 / 100 * Y + 1) / 2 ^ 120 ≤ (105 / 100 * 2 ^ 63 + 1) / 2 ^ 120 :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    calc Real.log 2 * ((105 / 100 * Y + 1) / 2 ^ 120) ≤ 1 * ((105 / 100 * 2 ^ 63 + 1) / 2 ^ 120) :=
          mul_le_mul (by linarith) this (by positivity) zero_le_one
      _ ≤ 1 / 2 ^ 50 := by norm_num
  have es := exp_shift_near _ _ _ (1 / 2 ^ 50) d dc (by norm_num)
  rw [← Real.rpow_def_of_pos two_pos, ← Real.rpow_def_of_pos two_pos] at es
  have X0 : (0 : ℝ) ≤ (2 : ℝ) ^ P * 2 ^ f := by positivity
  have k : (1 + 1 / 2 ^ 50) * (Real.log 2 * ((105 / 100 * Y + 1) / 2 ^ 120)) ≤ (Y + 1) / 2 ^ 120 := by
    rw [show (1 + 1 / 2 ^ 50) * (Real.log 2 * ((105 / 100 * Y + 1) / 2 ^ 120)) =
      (1 + 1 / 2 ^ 50) * Real.log 2 * (105 / 100 * Y + 1) / 2 ^ 120 by ring]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have : (1 + 1 / 2 ^ 50) * Real.log 2 ≤ 7 / 10 := by nlinarith
    nlinarith
  calc |r - (2 : ℝ) ^ P * 2 ^ f| ≤ |r - (2 : ℝ) ^ (w / 2 ^ 120) * 2 ^ f| +
        |((2 : ℝ) ^ (w / 2 ^ 120) - (2 : ℝ) ^ P) * 2 ^ f| := by
        rw [show r - (2 : ℝ) ^ P * 2 ^ f = (r - (2 : ℝ) ^ (w / 2 ^ 120) * 2 ^ f) +
          ((2 : ℝ) ^ (w / 2 ^ 120) - (2 : ℝ) ^ P) * 2 ^ f by ring]
        exact abs_add_le _ _
    _ ≤ E + (2 : ℝ) ^ P * 2 ^ f * (Y + 1) / 2 ^ 120 := by
        refine add_le_add hr ?_
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ f)]
        calc |(2 : ℝ) ^ (w / 2 ^ 120) - (2 : ℝ) ^ P| * 2 ^ f
            ≤ (2 : ℝ) ^ P * ((1 + 1 / 2 ^ 50) * (Real.log 2 * ((105 / 100 * Y + 1) / 2 ^ 120))) * 2 ^ f :=
              mul_le_mul_of_nonneg_right es (by positivity)
          _ ≤ (2 : ℝ) ^ P * ((Y + 1) / 2 ^ 120) * 2 ^ f :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left k (by positivity)) (by positivity)
          _ = _ := by ring

/-- `2^P · 2^f ≥ 2^(2f - 1)` once `P ≥ f - 1`, `f ≥ 1`. -/
theorem pow_mark_le (P : ℝ) (f : ℕ) (hf : 1 ≤ f) (hP : (f : ℝ) - 1 ≤ P) :
    (2 : ℝ) ^ (2 * f - 1) ≤ (2 : ℝ) ^ P * 2 ^ f := by
  have e : (2 : ℝ) ^ (2 * f - 1) = (2 : ℝ) ^ (((f : ℝ) - 1)) * 2 ^ f := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_add two_pos]
    congr 1; push_cast [Nat.cast_sub (by omega : 1 ≤ 2 * f)]; ring
  rw [e]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le one_le_two hP) (by positivity)

/-- `(a / 2^f)^p = 2^(p · log₂ (a / 2^f))` for `a > 0`. -/
theorem rpow_eq_two_rpow (x p : ℝ) (hx : 0 < x) : x ^ p = (2 : ℝ) ^ (p * Real.logb 2 x) := by
  rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hx]

/-- `i128::unsigned_abs` is `natAbs`. -/
theorem I128_unsigned_abs_spec (x : Std.I128) :
    core.num.I128.unsigned_abs x ⦃ u => u.val = x.val.natAbs ⦄ :=
  (WP.spec_ok _).mpr (toNat_abs_eq_natAbs x.bv)

/-- The result `r` of `pow_magnitude` for `x = a / 2^f` and the exponent `y / 2^fy`, with
`X = x^(y / 2^fy) · 2^f` and `Y = |y| / 2^fy`: the mark `2^(2f)` with `X ≥ 2^(2f - 1)`, or a
value within `½ + 2.2 · 2^(2f) / 2^71 + X · (Y + 1) / 2^120` of `X`. -/
def powOk (f a : ℕ) (y : ℤ) (fy : ℕ) (r : ℤ) : Prop :=
  (r = 2 ^ (2 * f) ∧ (2 : ℝ) ^ (2 * f - 1) ≤ ((a : ℝ) / 2 ^ f) ^ ((y : ℝ) / 2 ^ fy) * 2 ^ f) ∨
    |(r : ℝ) - ((a : ℝ) / 2 ^ f) ^ ((y : ℝ) / 2 ^ fy) * 2 ^ f| ≤
      1 / 2 + 22 / 10 * 2 ^ (2 * f) / 2 ^ 71 +
        ((a : ℝ) / 2 ^ f) ^ ((y : ℝ) / 2 ^ fy) * 2 ^ f * (|(y : ℝ)| / 2 ^ fy + 1) / 2 ^ 120

/-- A result of `pow_magnitude` with `|y| ≤ 2^63` and `f ≤ 32` is at least `-1`. -/
theorem powOk_ge (f a : ℕ) (y : ℤ) (fy : ℕ) (r : ℤ) (hf : f ≤ 32) (hy : y.natAbs ≤ 2 ^ 63)
    (h : powOk f a y fy r) : -1 ≤ r := by
  rcases h with ⟨e, _⟩ | h
  · rw [e]; have : (0 : ℤ) ≤ 2 ^ (2 * f) := by positivity
    omega
  · set X := ((a : ℝ) / 2 ^ f) ^ ((y : ℝ) / 2 ^ fy) * 2 ^ f
    have X0 : 0 ≤ X := by positivity
    have Yb : |(y : ℝ)| / 2 ^ fy + 1 ≤ 2 ^ 120 := by
      have : |(y : ℝ)| ≤ 2 ^ 63 := by rw [← Int.cast_abs, Int.abs_eq_natAbs]; exact_mod_cast hy
      have : |(y : ℝ)| / 2 ^ fy ≤ 2 ^ 63 := (div_le_self (abs_nonneg _) (one_le_pow₀ one_le_two)).trans this
      linarith
    have t : X * (|(y : ℝ)| / 2 ^ fy + 1) / 2 ^ 120 ≤ X := by
      rw [div_le_iff₀ (by positivity)]; exact mul_le_mul_of_nonneg_left Yb X0
    have p : (22 / 10 : ℝ) * 2 ^ (2 * f) / 2 ^ 71 ≤ 1 / 4 := by
      have : (2 : ℝ) ^ (2 * f) ≤ 2 ^ 64 := pow_le_pow_right₀ one_le_two (by omega)
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have := (abs_le.mp h).1
    have : (-1 : ℝ) < r := by linarith
    have : (-1 : ℤ) < r := by exact_mod_cast this
    omega

/-- L4 on the code: `exp::pow_magnitude(a, f, y, fy)` of `0 < a ≤ 2^63`, `1 ≤ f ≤ 32`,
`fy ∈ {0, f}`, `|y| ≤ 2^31` for `fy = 0`, never fails and satisfies `powOk`: with
`x = a / 2^f`, `Y = |y| / 2^fy` and `X = x^(y / 2^fy) · 2^f` it returns the mark `2^(2f)` only
for `X ≥ 2^(2f - 1)`, and otherwise a value within `½ + 2.2 · 2^(2f) / 2^71 + X · (Y + 1) / 2^120`
of `X`. -/
theorem pow_magnitude_spec (a : Std.U64) (f : Std.U32) (y : Std.I64) (fy : Std.U32) (ha0 : 0 < a.val)
    (ha : a.val ≤ 2 ^ 63) (hf1 : 1 ≤ f.val) (hf : f.val ≤ 32) (hfy : fy.val = 0 ∨ fy.val = f.val)
    (hy : fy.val = 0 → y.val.natAbs ≤ 2 ^ 31) :
    fulcrum.exp.pow_magnitude a f y fy ⦃ r => powOk f.val a.val y.val fy.val r.val ⦄ := by
  unfold powOk
  have n128 : UScalarTy.U128.numBits = 128 := rfl
  have fy32 : fy.val ≤ 32 := by omega
  unfold fulcrum.exp.pow_magnitude
  refine WP.spec_bind (log2_wide_spec a f ha0 ha hf1 hf) fun l ⟨hl, lab⟩ => ?_
  refine WP.spec_bind (I128_unsigned_abs_spec l) fun lm hlm => ?_
  refine WP.spec_bind (I64_unsigned_abs_spec y) fun yi hyi => ?_
  rw [lift, bind_ok]
  have ymv : (UScalar.cast .U128 yi).val = y.val.natAbs := by rw [cast_u128_val, hyi]
  generalize UScalar.cast .U128 yi = ym at ymv ⊢
  have yab : y.val.natAbs ≤ 2 ^ 63 := natAbs_le_pow y 63 IScalarTy.I64_numBits_eq
  refine WP.spec_bind (shr_i32_spec lm 64#i32 64 rfl (by rw [n128]; norm_num)) fun i1 h1 => ?_
  have i1l : i1.val < 2 ^ 62 := by rw [h1, hlm, Nat.div_lt_iff_lt_mul (by positivity)]; omega
  refine WP.spec_bind (UScalar.mul_spec (x := ym) (y := i1) (by
    rw [U128_max_val, ymv]
    calc y.val.natAbs * i1.val ≤ 2 ^ 63 * 2 ^ 62 := Nat.mul_le_mul yab i1l.le
      _ ≤ 2 ^ 128 - 1 := by norm_num)) fun high hhigh => ?_
  refine WP.spec_bind (UScalar.add_spec (x := 62#u32) (y := fy) (by rw [lit_val, U32_max_val]; omega)) fun i2 h2 => ?_
  rw [lit_val] at h2
  refine WP.spec_bind (UScalar.ShiftLeft_spec 1#u128 i2 _ (by rw [h2, n128]; omega) rfl) fun i3 ⟨h3, _⟩ => ?_
  rw [h2, lit_val, Nat.shiftLeft_eq, one_mul, UScalar.size_def, n128,
    Nat.mod_eq_of_lt (Nat.pow_lt_pow_right one_lt_two (by omega))] at h3
  set Lr : ℝ := Real.logb 2 ((a.val : ℝ) / 2 ^ f.val) with hLr
  set p : ℝ := (y.val : ℝ) / 2 ^ fy.val with hp
  set Y : ℝ := |(y.val : ℝ)| / 2 ^ fy.val with hY
  have ap : (0 : ℝ) < a.val := by exact_mod_cast ha0
  have xp : (0 : ℝ) < (a.val : ℝ) / 2 ^ f.val := by positivity
  rw [rpow_eq_two_rpow _ _ xp]
  have Y0 : 0 ≤ Y := by positivity
  have YM : Y ≤ 2 ^ 63 := by
    rw [hY, div_le_iff₀ (by positivity)]
    have : |(y.val : ℝ)| ≤ 2 ^ 63 := by
      rw [← Int.cast_abs, Int.abs_eq_natAbs]; exact_mod_cast yab
    exact this.trans (le_mul_of_one_le_right (by positivity) (one_le_pow₀ one_le_two))
  have wnear : |(y.val : ℝ) * l.val / 2 ^ fy.val - p * Lr * 2 ^ 120| ≤ 105 / 100 * Y := by
    rw [hp, hY, show (y.val : ℝ) * l.val / 2 ^ fy.val - (y.val : ℝ) / 2 ^ fy.val * Lr * 2 ^ 120 =
      (y.val : ℝ) / 2 ^ fy.val * ((l.val : ℝ) - Lr * 2 ^ 120) by ring, abs_mul, abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < 2 ^ fy.val), mul_comm (105 / 100 : ℝ)]
    exact mul_le_mul_of_nonneg_left hl (by positivity)
  have trunc := natAbs_mul_div_near y.val l.val fy.val
  have sgn : ((l < 0#i128) != (y < 0#i64)) = true → y.val * l.val ≤ 0 := by
    intro h
    simp only [bne_iff_ne, ne_eq, decide_eq_decide, IScalar.lt_equiv] at h
    have z1 : (0#i128 : Std.I128).val = 0 := rfl
    have z2 : (0#i64 : Std.I64).val = 0 := rfl
    rw [z1, z2] at h
    rcases lt_or_ge l.val 0 with c | c
    · have : 0 ≤ y.val := by by_contra q; exact h ⟨fun _ => lt_of_not_ge q, fun _ => c⟩
      nlinarith
    · have : y.val < 0 := by by_contra q; exact h ⟨fun e => absurd e (not_lt.mpr c), fun e => absurd e q⟩
      nlinarith
  have sgn' : ¬ ((l < 0#i128) != (y < 0#i64)) = true → 0 ≤ y.val * l.val := by
    intro h
    simp only [bne_iff_ne, ne_eq, decide_eq_decide, IScalar.lt_equiv, not_not] at h
    have z1 : (0#i128 : Std.I128).val = 0 := rfl
    have z2 : (0#i64 : Std.I64).val = 0 := rfl
    rw [z1, z2] at h
    rcases lt_or_ge l.val 0 with c | c
    · have : y.val < 0 := h.mp c
      nlinarith
    · have : 0 ≤ y.val := by by_contra q; exact (not_lt.mpr c) (h.mpr (lt_of_not_ge q))
      nlinarith
  have bnd0 : 0 ≤ 22 / 10 * (2 : ℝ) ^ (2 * f.val) / 2 ^ 71 +
      (2 : ℝ) ^ (p * Lr) * 2 ^ f.val * (Y + 1) / 2 ^ 120 := by positivity
  by_cases big : high >= i3
  · have hb : 2 ^ (62 + fy.val) ≤ high.val := by have : i3.val ≤ high.val := big; omega
    rw [ite_eq_left big]
    have prod : (2 : ℝ) ^ 126 ≤ |(y.val : ℝ) * l.val| / 2 ^ fy.val := by
      rw [le_div_iff₀ (by positivity)]
      have n1 : high.val * 2 ^ 64 ≤ y.val.natAbs * l.val.natAbs := by
        rw [hhigh, ymv, h1, hlm, mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.div_mul_le_self _ _)
      have n2 : 2 ^ (62 + fy.val) * 2 ^ 64 ≤ y.val.natAbs * l.val.natAbs := (Nat.mul_le_mul_right _ hb).trans n1
      have e : ((y.val.natAbs * l.val.natAbs : ℕ) : ℝ) = |(y.val : ℝ) * l.val| := by
        rw [abs_mul, Nat.cast_mul, Nat.cast_natAbs, Nat.cast_natAbs, Int.cast_abs, Int.cast_abs]
      calc (2 : ℝ) ^ 126 * 2 ^ fy.val = ((2 ^ (62 + fy.val) * 2 ^ 64 : ℕ) : ℝ) := by
            rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, ← pow_add, ← pow_add]; congr 1; omega
        _ ≤ ((y.val.natAbs * l.val.natAbs : ℕ) : ℝ) := by exact_mod_cast n2
        _ = _ := e
    have YM' : 105 / 100 * Y ≤ 2 ^ 64 := by linarith
    by_cases hn : ((l < 0#i128) != (y < 0#i64)) = true
    · rw [ite_eq_left hn, WP.spec_ok]
      right
      have s0 := sgn hn
      have neg : (y.val : ℝ) * l.val / 2 ^ fy.val ≤ -2 ^ 126 := by
        have : (y.val : ℝ) * l.val ≤ 0 := by exact_mod_cast s0
        rw [abs_of_nonpos this] at prod
        rw [neg_div] at prod; linarith
      have Pl : p * Lr ≤ -63 := by
        have := (abs_le.mp wnear).1
        have : p * Lr * 2 ^ 120 ≤ -63 * 2 ^ 120 := by linarith
        exact le_of_mul_le_mul_right (by linarith) (by positivity : (0 : ℝ) < 2 ^ 120)
      have Xs : (2 : ℝ) ^ (p * Lr) * 2 ^ f.val ≤ 1 / 2 := by
        have h1' : (2 : ℝ) ^ (p * Lr) ≤ 2 ^ (-63 : ℝ) := Real.rpow_le_rpow_of_exponent_le one_le_two Pl
        have h2' : (2 : ℝ) ^ f.val ≤ 2 ^ 32 := pow_le_pow_right₀ one_le_two hf
        have : (2 : ℝ) ^ (-63 : ℝ) = 1 / 2 ^ 63 := by
          rw [Real.rpow_neg (by norm_num), show (63 : ℝ) = ((63 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; ring
        rw [this] at h1'
        calc (2 : ℝ) ^ (p * Lr) * 2 ^ f.val ≤ 1 / 2 ^ 63 * 2 ^ 32 := mul_le_mul h1' h2' (by positivity) (by positivity)
          _ ≤ 1 / 2 := by norm_num
      rw [show ((0#i128 : Std.I128).val : ℝ) = 0 from by norm_num [show (0#i128 : Std.I128).val = 0 from rfl],
        zero_sub, abs_neg, abs_of_nonneg (by positivity)]
      linarith
    · rw [ite_eq_right hn]
      refine WP.spec_mono (overflow_spec f hf) fun r hr => Or.inl ⟨hr, ?_⟩
      have s0 := sgn' hn
      have pos : (2 : ℝ) ^ 126 ≤ (y.val : ℝ) * l.val / 2 ^ fy.val := by
        have : 0 ≤ (y.val : ℝ) * l.val := by exact_mod_cast s0
        rwa [abs_of_nonneg this] at prod
      have Pl : (f.val : ℝ) - 1 ≤ p * Lr := by
        have := (abs_le.mp wnear).2
        have : 63 * 2 ^ 120 ≤ p * Lr * 2 ^ 120 := by linarith
        have : (63 : ℝ) ≤ p * Lr := le_of_mul_le_mul_right (by linarith) (by positivity : (0 : ℝ) < 2 ^ 120)
        have : (f.val : ℝ) ≤ 32 := by exact_mod_cast hf
        linarith
      exact pow_mark_le _ _ hf1 Pl
  have hb : high.val < 2 ^ (62 + fy.val) := by have : ¬ i3.val ≤ high.val := big; omega
  rw [ite_eq_right big]
  refine WP.spec_bind (UScalar.sub_spec (x := 64#u32) (y := fy) (by rw [lit_val]; omega)) fun i4 ⟨h4, _⟩ => ?_
  rw [lit_val] at h4
  have i5b : high.val * 2 ^ (64 - fy.val) < 2 ^ 126 := by
    calc high.val * 2 ^ (64 - fy.val) < 2 ^ (62 + fy.val) * 2 ^ (64 - fy.val) :=
          Nat.mul_lt_mul_of_pos_right hb (by positivity)
      _ = 2 ^ 126 := by rw [← pow_add]; congr 1; omega
  refine WP.spec_bind (UScalar.ShiftLeft_spec high i4 _ (by rw [h4, n128]; omega) rfl) fun i5 ⟨h5, _⟩ => ?_
  rw [h4, Nat.shiftLeft_eq, UScalar.size_def, n128, Nat.mod_eq_of_lt (i5b.trans (by norm_num))] at h5
  rw [lift, bind_ok, lift, bind_ok]
  have i7v : (UScalar.cast .U128 (UScalar.cast .U64 lm)).val = l.val.natAbs % 2 ^ 64 := by
    rw [cast_u128_val, cast_u64_val, hlm]
  generalize UScalar.cast .U128 (UScalar.cast .U64 lm) = i7 at i7v ⊢
  have i8b : y.val.natAbs * (l.val.natAbs % 2 ^ 64) < 2 ^ 127 := by
    calc y.val.natAbs * (l.val.natAbs % 2 ^ 64) ≤ 2 ^ 63 * (2 ^ 64 - 1) :=
          Nat.mul_le_mul yab (Nat.le_pred_of_lt (Nat.mod_lt _ (by positivity)))
      _ < 2 ^ 127 := by norm_num
  refine WP.spec_bind (UScalar.mul_spec (x := ym) (y := i7) (by rw [U128_max_val, ymv, i7v]; omega)) fun i8 h8 => ?_
  rw [ymv, i7v] at h8
  refine WP.spec_bind (UScalar.ShiftRight_spec i8 fy (by rw [n128]; omega)) fun i9 ⟨h9, _⟩ => ?_
  rw [Nat.shiftRight_eq_div_pow, h8] at h9
  have i9b : i9.val < 2 ^ 126 := by
    rw [h9]
    rcases hfy with h0 | h0
    · have ys := hy h0
      rw [h0, pow_zero, Nat.div_one]
      calc y.val.natAbs * (l.val.natAbs % 2 ^ 64) ≤ 2 ^ 31 * (2 ^ 64 - 1) :=
            Nat.mul_le_mul ys (Nat.le_pred_of_lt (Nat.mod_lt _ (by positivity)))
        _ < 2 ^ 126 := by norm_num
    · rw [Nat.div_lt_iff_lt_mul (by positivity)]
      calc y.val.natAbs * (l.val.natAbs % 2 ^ 64) < 2 ^ 127 := i8b
        _ = 2 ^ 126 * 2 ^ 1 := by norm_num
        _ ≤ 2 ^ 126 * 2 ^ fy.val := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right two_pos (by omega))
  refine WP.spec_bind (UScalar.add_spec (x := i5) (y := i9) (by rw [U128_max_val, h5]; omega)) fun i10 h10 => ?_
  have i10v : i10.val = y.val.natAbs * l.val.natAbs / 2 ^ fy.val := by
    rw [h10, h5, h9, hhigh, ymv, h1, hlm]
    have e : y.val.natAbs * l.val.natAbs =
        y.val.natAbs * (l.val.natAbs / 2 ^ 64) * 2 ^ (64 - fy.val) * 2 ^ fy.val + y.val.natAbs * (l.val.natAbs % 2 ^ 64) := by
      rw [mul_assoc _ (2 ^ (64 - fy.val)), ← pow_add, show 64 - fy.val + fy.val = 64 by omega]
      conv_lhs => rw [← Nat.div_add_mod l.val.natAbs (2 ^ 64)]
      ring
    rw [e, add_comm _ (y.val.natAbs * (l.val.natAbs % 2 ^ 64)), Nat.add_mul_div_right _ _ (by positivity), add_comm]
  have i10l : i10.val < 2 ^ 127 := by rw [h10, h5]; omega
  rw [lift, bind_ok]
  have mc : (UScalar.hcast .I128 i10).val = (i10.val : ℤ) := by
    rw [UScalar.hcast_val_eq, IScalarTy.I128_numBits_eq]
    exact Int.bmod_eq_of_le ((neg_nonpos.mpr (by positivity)).trans (Int.natCast_nonneg _))
      ((by exact_mod_cast i10l : (i10.val : ℤ) < 2 ^ 127).trans_le (by norm_num))
  generalize UScalar.hcast .I128 i10 = m at mc ⊢
  rw [i10v] at mc
  refine WP.spec_bind (Pₘ := fun m1 : Std.I128 => |(m1.val : ℝ) - (y.val : ℝ) * l.val / 2 ^ fy.val| < 1) ?_
    fun m1 hm1 => ?_
  · by_cases hn : ((l < 0#i128) != (y < 0#i64)) = true
    · rw [ite_eq_left hn]
      refine WP.spec_mono (IScalar.neg_step _ (fun e => ?_)) fun r' hr' => ?_
      · have : m.val = IScalar.min .I128 := by rw [e]
        rw [mc, IScalar.min_def, IScalarTy.I128_numBits_eq] at this
        have : (0 : ℤ) ≤ ((y.val.natAbs * l.val.natAbs / 2 ^ fy.val : ℕ) : ℤ) := Int.natCast_nonneg _
        omega
      · rw [hr', mc]
        have s0 : (y.val : ℝ) * l.val ≤ 0 := by exact_mod_cast sgn hn
        rw [abs_of_nonpos s0] at trunc
        rw [Int.cast_neg, Int.cast_natCast, show -((y.val.natAbs * l.val.natAbs / 2 ^ fy.val : ℕ) : ℝ) - (y.val : ℝ) * l.val / 2 ^ fy.val =
          -(y.val * l.val) / 2 ^ fy.val - ((y.val.natAbs * l.val.natAbs / 2 ^ fy.val : ℕ) : ℝ) by ring]
        exact abs_lt.mpr ⟨by linarith [trunc.1], by linarith [trunc.2]⟩
    · rw [ite_eq_right hn, WP.spec_ok, mc]
      have s0 : 0 ≤ (y.val : ℝ) * l.val := by exact_mod_cast sgn' hn
      rw [abs_of_nonneg s0] at trunc
      rw [Int.cast_natCast]
      exact abs_lt.mpr ⟨by linarith [trunc.2], by linarith [trunc.1]⟩
  have wn : |(m1.val : ℝ) - p * Lr * 2 ^ 120| ≤ 105 / 100 * Y + 1 := by
    calc |(m1.val : ℝ) - p * Lr * 2 ^ 120| ≤ |(m1.val : ℝ) - (y.val : ℝ) * l.val / 2 ^ fy.val| +
          |(y.val : ℝ) * l.val / 2 ^ fy.val - p * Lr * 2 ^ 120| := abs_sub_le _ _ _
      _ ≤ 1 + 105 / 100 * Y := add_le_add hm1.le wnear
      _ = _ := add_comm _ _
  refine WP.spec_mono (exp2_wide_spec m1 f hf1 hf) fun r hr => ?_
  rcases hr with ⟨ho, hrv⟩ | ⟨_, hv⟩
  · left
    refine ⟨hrv, pow_mark_le _ _ hf1 ?_⟩
    have : (f.val : ℤ) * 2 ^ 120 ≤ m1.val := by
      have := Int.mul_le_of_le_ediv (by positivity) ho
      linarith
    have q1 : (f.val : ℝ) * 2 ^ 120 ≤ m1.val := by exact_mod_cast this
    have q2 := (abs_le.mp wn).2
    have : ((f.val : ℝ) - 1) * 2 ^ 120 ≤ p * Lr * 2 ^ 120 := by
      rw [sub_mul, one_mul]
      linarith only [q1, q2, YM]
    exact le_of_mul_le_mul_right this (by positivity)
  · right
    have := pow_tail_near m1.val (p * Lr) Y _ r.val f.val Y0 YM wn hv
    exact this

/-- `x &&& m` of `i64` with the mask `m = 2^k - 1`, `k ≤ 62`, is `x mod 2^k`. -/
theorem i64_and_mask_val (x m : Std.I64) (k : ℕ) (hk : k ≤ 62) (hm : m.val = 2 ^ k - 1) :
    (x &&& m).val = x.val % 2 ^ k := by
  have pk : 2 ^ k ≤ 2 ^ 62 := Nat.pow_le_pow_right two_pos hk
  have p1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have mt : m.bv.toNat = 2 ^ k - 1 := by
    have h := BitVec.toInt_eq_toNat_cond m.bv
    have lt := m.bv.isLt
    have hv : m.bv.toInt = 2 ^ k - 1 := hm
    rw [hv] at h
    have e : ((2 ^ k : ℕ) : ℤ) = 2 ^ k := by push_cast; rfl
    rw [← e] at h
    generalize 2 ^ k = P at h pk p1 ⊢
    split at h <;> omega
  have d : (2 ^ k : ℤ) ∣ ((2 ^ IScalarTy.I64.numBits : ℕ) : ℤ) := by
    rw [IScalarTy.I64_numBits_eq, show ((2 ^ 64 : ℕ) : ℤ) = (2 : ℤ) ^ 64 by norm_num]
    exact pow_dvd_pow 2 (by omega)
  have small : ((x.bv.toNat % 2 ^ k : ℕ) : ℤ).bmod (2 ^ IScalarTy.I64.numBits) = ((x.bv.toNat % 2 ^ k : ℕ) : ℤ) := by
    have t : ((x.bv.toNat % 2 ^ k : ℕ) : ℤ) < 2 ^ 62 := by exact_mod_cast (Nat.mod_lt _ (by positivity)).trans_le pk
    have t0 : (0 : ℤ) ≤ ((x.bv.toNat % 2 ^ k : ℕ) : ℤ) := Int.natCast_nonneg _
    generalize ((x.bv.toNat % 2 ^ k : ℕ) : ℤ) = q at t t0 ⊢
    exact Int.bmod_eq_of_le (by rw [IScalarTy.I64_numBits_eq]; push_cast; omega)
      (by rw [IScalarTy.I64_numBits_eq]; push_cast; omega)
  rw [IScalar.val, IScalar.val, IScalar.bv_and, BitVec.toInt_and, mt, Nat.and_two_pow_sub_one_eq_mod,
    small, BitVec.toInt_eq_toNat_bmod, ← Int.emod_emod_of_dvd _ d, Int.bmod_emod,
    Int.emod_emod_of_dvd _ d]
  exact Int.natCast_emod _ (2 ^ k)

/-- L4 on the code: `exp::pow(raw, f, y, fy)` with `1 ≤ f ≤ 32`, `fy ∈ {0, f}` and
`|y| ≤ 2^31` for `fy = 0` never fails. `x^0` is `2^f`; `0^y` is `0` for `y > 0` and the mark
`2^(2f)` for `y < 0`; a negative `x` with `y / 2^fy` not an integer gives `none`; otherwise the
result is `powOk` of `|x|`, negated for a negative `x` and an odd `y / 2^fy`. -/
theorem pow_spec (raw : Std.I64) (f : Std.U32) (y : Std.I64) (fy : Std.U32) (hf1 : 1 ≤ f.val) (hf : f.val ≤ 32)
    (hfy : fy.val = 0 ∨ fy.val = f.val) (hy : fy.val = 0 → y.val.natAbs ≤ 2 ^ 31) :
    fulcrum.exp.pow raw f y fy ⦃ r =>
      (y.val = 0 ∧ r.map (·.val) = some (2 ^ f.val)) ∨
      (y.val ≠ 0 ∧ raw.val = 0 ∧ r.map (·.val) = some (if 0 < y.val then 0 else 2 ^ (2 * f.val))) ∨
      (y.val ≠ 0 ∧ raw.val < 0 ∧ y.val % 2 ^ fy.val ≠ 0 ∧ r = none) ∨
      (y.val ≠ 0 ∧ raw.val ≠ 0 ∧ (0 < raw.val ∨ y.val % 2 ^ fy.val = 0) ∧ ∃ m : ℤ,
        powOk f.val raw.val.natAbs y.val fy.val m ∧
        r.map (·.val) = some (if raw.val < 0 ∧ y.val / 2 ^ fy.val % 2 = 1 then -m else m)) ⦄ := by
  unfold fulcrum.exp.pow
  have yab : y.val.natAbs ≤ 2 ^ 63 := natAbs_le_pow y 63 IScalarTy.I64_numBits_eq
  by_cases y0 : y = 0#i64
  · have yv : y.val = 0 := by rw [y0]; rfl
    rw [ite_eq_left y0]
    refine WP.spec_bind (IScalar.ShiftLeft_spec 1#i128 f (by rw [IScalarTy.I128_numBits_eq]; omega))
      fun i ⟨hi, _⟩ => ?_
    rw [WP.spec_ok]
    left
    refine ⟨yv, ?_⟩
    simp only [Option.map_some]
    rw [hi, show ((1#i128 : Std.I128).val) = 1 from rfl, Int.shiftLeft_eq, one_mul, IScalarTy.I128_numBits_eq]
    refine congrArg some (Int.bmod_eq_of_le ?_ ?_)
    · exact (neg_nonpos.mpr (by positivity)).trans (by positivity)
    · exact (pow_lt_pow_right₀ (by norm_num) (by omega : f.val < 127)).trans_le (by norm_num)
  have yv : y.val ≠ 0 := fun e => y0 (IScalar.eq_imp _ _ (by rw [e]; rfl))
  rw [ite_eq_right y0]
  by_cases r0 : raw = 0#i64
  · have rv : raw.val = 0 := by rw [r0]; rfl
    rw [ite_eq_left r0]
    by_cases yp : y > 0#i64
    · have : 0 < y.val := yp
      rw [ite_eq_left yp, WP.spec_ok]
      exact Or.inr (Or.inl ⟨yv, rv, by simp only [Option.map_some, ite_eq_left this]; rfl⟩)
    · have : ¬ 0 < y.val := yp
      rw [ite_eq_right yp]
      refine WP.spec_bind (overflow_spec f hf) fun i hi => ?_
      rw [WP.spec_ok]
      exact Or.inr (Or.inl ⟨yv, rv, by simp only [Option.map_some, ite_eq_right this, hi]⟩)
  have rv : raw.val ≠ 0 := fun e => r0 (IScalar.eq_imp _ _ (by rw [e]; rfl))
  rw [ite_eq_right r0]
  refine WP.spec_bind (I64_unsigned_abs_spec raw) fun i hi => ?_
  have rab : raw.val.natAbs ≤ 2 ^ 63 := natAbs_le_pow raw 63 IScalarTy.I64_numBits_eq
  refine WP.spec_bind (pow_magnitude_spec i f y fy (by rw [hi]; omega) (by rw [hi]; exact rab) hf1 hf hfy hy)
    fun m hm => ?_
  rw [hi] at hm
  have mge := powOk_ge _ _ _ _ _ hf yab hm
  have negm : ∀ k : Option Std.I128 → Prop, (∀ v : Std.I128, v.val = -m.val → k (some v)) →
      (do let m1 ← -. m; ok (some m1)) ⦃ k ⦄ := by
    intro k hk
    refine WP.spec_bind (IScalar.neg_step _ (fun e => ?_)) fun v hv => ?_
    · have : m.val = IScalar.min .I128 := by rw [e]
      rw [IScalar.min_def, IScalarTy.I128_numBits_eq] at this
      omega
    · rw [WP.spec_ok]; exact hk v hv
  by_cases rp : raw > 0#i64
  · have : 0 < raw.val := rp
    rw [ite_eq_left rp, WP.spec_ok]
    refine Or.inr (Or.inr (Or.inr ⟨yv, rv, Or.inl this, m.val, hm, ?_⟩))
    simp only [Option.map_some]
    rw [ite_eq_right (fun h => absurd h.1 (by omega))]
  have rn : raw.val < 0 := by have : ¬ 0 < raw.val := rp; omega
  rw [ite_eq_right rp]
  have par : ∀ k : Option Std.I128 → Prop, y.val % 2 ^ fy.val = 0 →
      (∀ r, (y.val ≠ 0 ∧ raw.val ≠ 0 ∧ (0 < raw.val ∨ y.val % 2 ^ fy.val = 0) ∧ ∃ m : ℤ,
        powOk f.val raw.val.natAbs y.val fy.val m ∧
        r.map (·.val) = some (if raw.val < 0 ∧ y.val / 2 ^ fy.val % 2 = 1 then -m else m)) → k r) →
      (do
        let i4 ← y >>> fy
        let i5 ← lift (i4 &&& 1#i64)
        if i5 = 1#i64 then do let m1 ← -. m; ok (some m1) else ok (some m)) ⦃ k ⦄ := by
    intro k hz hk
    refine WP.spec_bind (IScalar.ShiftRight_spec y fy (by rw [IScalarTy.I64_numBits_eq]; omega)) fun i4 ⟨h4, _⟩ => ?_
    rw [shr_eq_div] at h4
    rw [lift, bind_ok]
    have i5v : (i4 &&& 1#i64).val = y.val / 2 ^ fy.val % 2 := by
      rw [i64_and_mask_val i4 1#i64 1 (by norm_num) rfl, h4, pow_one]
    by_cases o : i4 &&& 1#i64 = 1#i64
    · have ov : y.val / 2 ^ fy.val % 2 = 1 := by rw [← i5v, o]; rfl
      rw [ite_eq_left o]
      refine negm k fun v hv => hk _ ⟨yv, rv, Or.inr hz, m.val, hm, ?_⟩
      simp only [Option.map_some]
      rw [ite_eq_left ⟨rn, ov⟩, hv]
    · have ov : ¬ y.val / 2 ^ fy.val % 2 = 1 := fun e => o (IScalar.eq_imp _ _ (by rw [i5v, e]; rfl))
      rw [ite_eq_right o, WP.spec_ok]
      refine hk _ ⟨yv, rv, Or.inr hz, m.val, hm, ?_⟩
      simp only [Option.map_some]
      rw [ite_eq_right (fun h => ov h.2)]
  by_cases fp : fy > 0#u32
  · have fy1 : 0 < fy.val := fp
    rw [ite_eq_left fp]
    refine WP.spec_bind (IScalar.ShiftLeft_spec 1#i64 fy (by rw [IScalarTy.I64_numBits_eq]; omega)) fun i1 ⟨h1, _⟩ => ?_
    have i1v : i1.val = 2 ^ fy.val := by
      rw [h1, show ((1#i64 : Std.I64).val) = 1 from rfl, Int.shiftLeft_eq, one_mul, IScalarTy.I64_numBits_eq]
      refine Int.bmod_eq_of_le ?_ ?_
      · exact (neg_nonpos.mpr (by positivity)).trans (by positivity)
      · exact (pow_lt_pow_right₀ (by norm_num) (by omega : fy.val < 63)).trans_le (by norm_num)
    have mn : IScalar.min .I64 = -2 ^ 63 := min_eq_neg_pow IScalarTy.I64_numBits_eq
    have mx : IScalar.max .I64 = 2 ^ 63 - 1 := max_eq_pow_sub_one IScalarTy.I64_numBits_eq
    have p32 : (2 : ℤ) ^ fy.val ≤ 2 ^ 32 := pow_le_pow_right₀ (by norm_num) (by omega)
    have one : (1#i64 : Std.I64).val = 1 := rfl
    have pp : (0 : ℤ) < 2 ^ fy.val := by positivity
    refine WP.spec_bind (IScalar.sub_spec (x := i1) (y := 1#i64) (by rw [i1v, mn, one]; omega)
      (by rw [i1v, mx, one]; omega)) fun i2 h2 => ?_
    rw [i1v, show ((1#i64 : Std.I64).val) = 1 from rfl] at h2
    rw [lift, bind_ok]
    have i3v : (y &&& i2).val = y.val % 2 ^ fy.val := by
      rw [i64_and_mask_val y i2 fy.val (by omega) (by rw [h2])]
    by_cases nz : (y &&& i2 != 0#i64) = true
    · have : y.val % 2 ^ fy.val ≠ 0 := by
        rw [← i3v]; intro e; exact (bne_iff_ne.mp nz) (IScalar.eq_imp _ _ (by rw [e]; rfl))
      rw [ite_eq_left nz, WP.spec_ok]
      exact Or.inr (Or.inr (Or.inl ⟨yv, rn, this, rfl⟩))
    · have z : y.val % 2 ^ fy.val = 0 := by
        rw [← i3v]
        have := not_not.mp (fun h => nz (bne_iff_ne.mpr h))
        rw [this]; rfl
      rw [ite_eq_right nz]
      exact par _ z fun r h => Or.inr (Or.inr (Or.inr h))
  · have fy0 : fy.val = 0 := by have : ¬ 0 < fy.val := fp; omega
    rw [ite_eq_right fp]
    exact par _ (by rw [fy0, pow_zero, Int.emod_one]) fun r h => Or.inr (Or.inr (Or.inr h))

end Fulcrum

end
