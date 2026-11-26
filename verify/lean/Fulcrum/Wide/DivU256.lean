module

public import Fulcrum.Kernel.Funs
import Fulcrum.Lemmas.Scalar
import Fulcrum.Math.DivU256
import Fulcrum.Wide.Div3by2

/-!
# `wide::div_rem_u256`

On the code extracted by Aeneas. For `hi < d`, `div_rem_u256(hi, lo, d)` never fails and returns
`⌊N / d⌋` and `N mod d` for `N = hi · 2^128 + lo` (`div_rem_u256_spec`).

`hi = 0` is one `u128` division. Otherwise `leading_zeros` gives `s = 127 - ⌊log₂ d⌋`, the
divisor and the dividend are shifted by `s` (`norm_pair_spec`, the branch `s = 0` included), two
steps of `div_rem_3by2` give the digits, joined by a shift and an or (`join_digits_spec`), and
the remainder is shifted back; `two_steps_norm` of `Math/DivU256.lean` closes the arithmetic.
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace Fulcrum

/-- `x << s` on `u128` for `s < 128` is `x · 2^s mod 2^128`. -/
theorem shl_u32_spec (x : Std.U128) (s : Std.U32) (hs : s.val < 128) :
    (x <<< s) ⦃ z => z.val = x.val * 2 ^ s.val % 2 ^ 128 ⦄ :=
  WP.spec_mono (UScalar.ShiftLeft_spec x s _ hs rfl) fun z ⟨hz, _⟩ => by
    rw [hz, Nat.shiftLeft_eq, UScalar.size_def]; rfl

/-- `x >> s` on `u128` for `s < 128` is `⌊x / 2^s⌋`. -/
theorem shr_u32_spec (x : Std.U128) (s : Std.U32) (hs : s.val < 128) :
    (x >>> s) ⦃ z => z.val = x.val / 2 ^ s.val ⦄ :=
  WP.spec_mono (UScalar.ShiftRight_spec x s hs) fun z ⟨hz, _⟩ => by
    rw [hz, Nat.shiftRight_eq_div_pow]

/-- The dividend shifted by `s < 128`, with the branch `s = 0`: the words
`hi · 2^s + ⌊lo / 2^(128 - s)⌋` and `lo · 2^s mod 2^128`. -/
theorem norm_pair_spec (hi lo : Std.U128) (s : Std.U32) (hs : s.val < 128)
    (hh : hi.val * 2 ^ s.val < 2 ^ 128) :
    (if s = 0#u32 then ok (hi, lo) else do
        let i ← hi <<< s
        let i1 ← 128#u32 - s
        let i2 ← lo >>> i1
        let i3 ← lift (i ||| i2)
        let i4 ← lo <<< s
        ok (i3, i4)) ⦃ p => p.1.val = hi.val * 2 ^ s.val + lo.val / 2 ^ (128 - s.val) ∧
          p.2.val = lo.val * 2 ^ s.val % 2 ^ 128 ⦄ := by
  have ll : lo.val < 2 ^ 128 := lo.bv.isLt
  by_cases h0 : s = 0#u32
  · have sv : s.val = 0 := by rw [h0]; rfl
    rw [ite_eq_left h0, WP.spec_ok, sv, pow_zero, Nat.mul_one, Nat.mul_one, Nat.div_eq_of_lt ll,
      Nat.add_zero, Nat.mod_eq_of_lt ll]
    exact ⟨rfl, rfl⟩
  have sp : 0 < s.val := Nat.pos_of_ne_zero fun e => h0 (UScalar.eq_of_val_eq (by rw [e]; rfl))
  rw [ite_eq_right h0]
  refine WP.spec_bind (shl_u32_spec hi s hs) fun i hi' => ?_
  rw [Nat.mod_eq_of_lt hh] at hi'
  refine WP.spec_bind (UScalar.sub_spec (x := 128#u32) (y := s) (by rw [lit_val]; omega))
    fun i1 ⟨h1, _⟩ => ?_
  rw [lit_val] at h1
  refine WP.spec_bind (shr_u32_spec lo i1 (by omega)) fun i2 h2 => ?_
  rw [lift, bind_ok]
  refine WP.spec_bind (shl_u32_spec lo s hs) fun i4 h4 => ?_
  rw [WP.spec_ok]
  refine ⟨?_, h4⟩
  have t : i2.val < 2 ^ s.val := by
    rw [h2, h1, ← shl_top lo.val s.val hs.le, Nat.div_lt_iff_lt_mul (by positivity), ← pow_add,
      Nat.add_comm, pow_add]
    exact Nat.mul_lt_mul_of_pos_right ll (by positivity)
  rw [UScalar.val_or, hi', Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt t, h2, h1, Nat.mul_comm]

/-- `(q₁ << 64) | q₀` of two digits is `q₁ · 2^64 + q₀`. -/
theorem join_digits_spec (q1 q0 : Std.U128) (h1 : q1.val < 2 ^ 64) (h0 : q0.val < 2 ^ 64) :
    (q1 <<< 64#i32) ⦃ i3 => (i3 ||| q0).val = q1.val * 2 ^ 64 + q0.val ⦄ :=
  WP.spec_mono (shl_i32_spec q1 64#i32 64 rfl (by decide) (by
    rw [show UScalarTy.U128.numBits = 128 from rfl]
    exact (Nat.mul_lt_mul_of_pos_right h1 (by positivity)).trans_le (by norm_num))) fun i3 h3 => by
    rw [UScalar.val_or, h3, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt h0, Nat.mul_comm]

/-- A `u128` below `2^64` narrowed to `u64` keeps its value. -/
theorem cast_u64_of_lt (x : Std.U128) (h : x.val < 2 ^ 64) : (UScalar.cast .U64 x).val = x.val := by
  rw [UScalar.cast_val_eq, UScalarTy.U64_numBits_eq, Nat.mod_eq_of_lt h]

/-- On the code: for `hi < d`, `wide::div_rem_u256(hi, lo, d)` never fails and returns
`⌊N / d⌋` and `N mod d` for `N = hi · 2^128 + lo`. -/
theorem div_rem_u256_spec (hi lo d : Std.U128) (h : hi.val < d.val) :
    fulcrum.wide.div_rem_u256 hi lo d ⦃ p => p.1.val = (hi.val * 2 ^ 128 + lo.val) / d.val ∧
      p.2.val = (hi.val * 2 ^ 128 + lo.val) % d.val ⦄ := by
  have hd : 0 < d.val := Nat.zero_lt_of_lt h
  have dl : d.val < 2 ^ 128 := d.bv.isLt
  have ll : lo.val < 2 ^ 128 := lo.bv.isLt
  unfold fulcrum.wide.div_rem_u256
  by_cases h0 : hi = 0#u128
  · have hv : hi.val = 0 := by rw [h0]; rfl
    rw [ite_eq_left h0]
    obtain ⟨q, hq, hqv⟩ := UScalar.div_spec lo (Nat.pos_iff_ne_zero.mp hd)
    rw [hq, bind_ok]
    refine WP.spec_bind (UScalar.rem_spec lo (Nat.pos_iff_ne_zero.mp hd)) fun r hr => ?_
    rw [WP.spec_ok, hv, Nat.zero_mul, Nat.zero_add]
    exact ⟨hqv, hr⟩
  rw [ite_eq_right h0, lift, bind_ok]
  have hs : (core.num.U128.leading_zeros d).val = 128 - Nat.log 2 d.val - 1 :=
    leading_zeros_val d (Nat.pos_iff_ne_zero.mp hd) (Nat.le_of_ble_eq_true rfl)
  have ⟨nlo, nhi⟩ := norm_bounds d.val hd.ne' dl
  rw [← hs] at nlo nhi
  generalize core.num.U128.leading_zeros d = s at hs nlo nhi ⊢
  have s128 : s.val < 128 := by omega
  refine WP.spec_bind (shl_u32_spec d s s128) fun d1 hd1 => ?_
  rw [Nat.mod_eq_of_lt nhi] at hd1
  have hh : hi.val * 2 ^ s.val < 2 ^ 128 :=
    (Nat.mul_lt_mul_of_pos_right h (by positivity)).trans nhi
  refine WP.spec_bind (norm_pair_spec hi lo s s128 hh) fun p ⟨hp1, hp2⟩ => ?_
  obtain ⟨hi1, lo1⟩ := p
  dsimp only at hp1 hp2 ⊢
  refine WP.spec_bind (shr_i32_spec lo1 64#i32 64 rfl (by decide)) fun i hi' => ?_
  rw [lift, bind_ok]
  have il : i.val < 2 ^ 64 := by
    rw [hi', Nat.div_lt_iff_lt_mul (by positivity)]; exact lo1.bv.isLt
  have c1 : (UScalar.cast .U64 i).val = lo1.val / 2 ^ 64 := by rw [cast_u64_of_lt i il, hi']
  have d64 : 2 ^ 64 ≤ d1.val := by rw [hd1]; exact le_trans (by norm_num) nlo
  have h1l : hi1.val < d1.val := by
    rw [hp1, hd1]; exact norm_hi_lt hi.val lo.val d.val s.val s128.le ll h
  refine WP.spec_bind (div_rem_3by2_spec hi1 (UScalar.cast .U64 i) d1 d64 h1l) fun p1 ⟨hq1, hr⟩ => ?_
  obtain ⟨q1, r⟩ := p1
  dsimp only at hq1 hr
  simp only [lift, bind_ok]
  have rl : r.val < d1.val := by rw [hr]; exact Nat.mod_lt _ (Nat.zero_lt_of_lt h1l)
  refine WP.spec_bind (div_rem_3by2_spec r (UScalar.cast .U64 lo1) d1 d64 rl) fun p0 ⟨hq0, hr1⟩ => ?_
  obtain ⟨q0, r1⟩ := p0
  dsimp only at hq0 hr1 ⊢
  rw [c1] at hq1 hr
  rw [cast_u64_val] at hq0 hr1
  have q1l : q1.val < 2 ^ 64 := by
    rw [hq1]; exact quot_lt _ _ _ h1l (by rw [← c1]; exact (UScalar.cast .U64 i).bv.isLt)
  have q0l : q0.val < 2 ^ 64 := by
    rw [hq0]; exact quot_lt _ _ _ rl (Nat.mod_lt _ (by positivity))
  refine WP.spec_bind (join_digits_spec q1 q0 q1l q0l) fun i3 h3 => ?_
  refine WP.spec_bind (shr_u32_spec r1 s s128) fun i5 h5 => ?_
  rw [WP.spec_ok]
  have hX : (hi1.val * 2 ^ 64 + lo1.val / 2 ^ 64) * 2 ^ 64 + lo1.val % 2 ^ 64 =
      (hi.val * 2 ^ 128 + lo.val) * 2 ^ s.val := by
    rw [words_join, hp1, hp2]; exact norm_join hi.val lo.val s.val s128.le
  have ⟨eq, er⟩ := two_steps_norm _ d.val s.val _ _ hd hX
  rw [← hd1, ← hr] at eq er
  refine ⟨?_, ?_⟩
  · rw [h3, hq1, hq0]; exact eq
  · rw [h5, hr1]; exact er

end Fulcrum

end
