module

public import Fulcrum.Lemmas.Scalar
public import Fulcrum.Math.MulWide

/-!
# `wide::widening_mul_u128`

On the code extracted by Aeneas: the full product of two `u128` as two words, from four
`u64 × u64` products (`widening_mul_u128_spec`, the math in `Math/MulWide.lean`).
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace Fulcrum

set_option maxRecDepth 10000

/-- On the code: `wide::widening_mul_u128(a, b)` never fails and returns the words
`⌊a · b / 2^128⌋` and `a · b mod 2^128`. -/
theorem widening_mul_u128_spec (a b : Std.U128) :
    fulcrum.wide.widening_mul_u128 a b ⦃ p => p.1.val = a.val * b.val / 2 ^ 128 ∧
      p.2.val = a.val * b.val % 2 ^ 128 ⦄ := by
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
    fun i10 ⟨h10s, _⟩ => ?_
  rw [lift, bind_ok]
  have hlo : (UScalar.cast .U128 (UScalar.cast .U64 p00) ||| i10).val =
      mid.val % 2 ^ 64 * 2 ^ 64 + p00.val % 2 ^ 64 := by
    have i10v : i10.val = mid.val % 2 ^ 64 * 2 ^ 64 := by
      rw [h10s, show (64#i32).toNat = 64 from rfl, Nat.shiftLeft_eq, UScalar.size_def,
        show UScalarTy.U128.numBits = 64 + 64 from rfl, pow_add, Nat.mul_mod_mul_right]
    have ll : (UScalar.cast .U128 (UScalar.cast .U64 p00)).val < 2 ^ 64 := by
      rw [cast_u128_val, cast_u64_val]; exact Nat.mod_lt _ (by positivity)
    rw [UScalar.val_or, Nat.lor_comm, i10v, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt ll,
      cast_u128_val, cast_u64_val, Nat.mul_comm]
  generalize UScalar.cast .U128 (UScalar.cast .U64 p00) ||| i10 = lo at hlo ⊢
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
  rw [WP.spec_ok]
  refine ⟨?_, ?_⟩
  · rw [hhi, h15, h13, h11, h12, h14, h16, hmid, h01, h10, h00]
    exact top
  · have low := widening_lo a.val b.val
    rw [← ha1, ← hb1, ← a0v, ← b0v] at low
    rw [hlo, hmid, h01, h10, h00]
    exact low

end Fulcrum

end
