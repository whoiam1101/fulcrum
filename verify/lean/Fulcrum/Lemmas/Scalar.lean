module

public import Fulcrum.Kernel.Funs

/-!
# Facts about the scalars of Aeneas used by several modules

The values of literals, the largest value of the unsigned types as a power of
two, `MIN`, `MAX` and the values of a signed type of `m + 1` bits, casts that
keep the value, the bound of `usize`, shifts of an unsigned value by an `i32`
amount, the last bit of an `i128`, `leading_zeros` of every unsigned width as
`BITS - 1 - ⌊log₂ n⌋`, and the `unsigned_abs` of `FunsExternal.lean` as the
natural absolute value.
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace Fulcrum

/-- A literal `x#u16`, `x#u32`, `x#u64`, `x#u128` or `x#usize` has the value `x`. -/
theorem lit_val {U : UScalarTy} (x : ℕ) (h : x ≤ UScalar.cMax U) : (UScalar.ofNat x h).val = x :=
  rfl

/-- The largest `u16` is `2^16 - 1`. -/
theorem U16_max_val : UScalar.max .U16 = 2 ^ 16 - 1 := by
  rw [UScalar.max_def, UScalarTy.U16_numBits_eq]

/-- The largest `u32` is `2^32 - 1`. -/
theorem U32_max_val : UScalar.max .U32 = 2 ^ 32 - 1 := by
  rw [UScalar.max_def, UScalarTy.U32_numBits_eq]

/-- The largest `u64` is `2^64 - 1`. -/
theorem U64_max_val : UScalar.max .U64 = 2 ^ 64 - 1 := by
  rw [UScalar.max_def, UScalarTy.U64_numBits_eq]

/-- The largest `u128` is `2^128 - 1`. -/
theorem U128_max_val : UScalar.max .U128 = 2 ^ 128 - 1 := by
  rw [UScalar.max_def, UScalarTy.U128_numBits_eq]

/-- A value of a signed type of `n + 1` bits is in `[-2^n, 2^n)`. -/
theorem val_bounds {B} (a : IScalar B) {n : ℕ} (hB : B.numBits = n + 1) :
    -2 ^ n ≤ a.val ∧ a.val < 2 ^ n := by
  have h := a.hBounds
  rwa [hB, Nat.add_sub_cancel] at h

/-- A signed `x` of `k + 1` bits has magnitude at most `2^k`. -/
theorem natAbs_le_pow {S} (x : IScalar S) (k : ℕ) (hk : S.numBits = k + 1) :
    x.val.natAbs ≤ 2 ^ k := by
  have ⟨l, u⟩ := val_bounds x hk
  rw [← Int.ofNat_le, Int.natCast_natAbs, Nat.cast_pow, Nat.cast_ofNat]
  exact abs_le.mpr ⟨l, u.le⟩

/-- `MIN` of a signed type of `m + 1` bits is `-2^m`. -/
theorem min_eq_neg_pow {W} {m : ℕ} (hW : W.numBits = m + 1) : IScalar.min W = -2 ^ m := by
  rw [IScalar.min_def, hW, Nat.add_sub_cancel]

/-- `MAX` of a signed type of `m + 1` bits is `2^m - 1`. -/
theorem max_eq_pow_sub_one {W} {m : ℕ} (hW : W.numBits = m + 1) : IScalar.max W = 2 ^ m - 1 := by
  rw [IScalar.max_def, hW, Nat.add_sub_cancel]

/-- A value in `[-2^m, 2^m)` is in `[MIN, MAX]` of a signed type of `m + 1`
bits. -/
theorem in_bounds_of_pow {W} {m : ℕ} (hW : W.numBits = m + 1) {x : ℤ} (lo : -2 ^ m ≤ x)
    (hi : x < 2 ^ m) : IScalar.min W ≤ x ∧ x ≤ IScalar.max W :=
  ⟨min_eq_neg_pow hW ▸ lo, max_eq_pow_sub_one hW ▸ Int.le_sub_one_of_lt hi⟩

/-- `usize` holds every `u32`. -/
theorem usize_max_ge : 2 ^ 32 - 1 ≤ UScalar.max .Usize := by
  rw [UScalar.max_def, UScalarTy.Usize_numBits_eq]
  rcases System.Platform.numBits_eq with h | h
  · rw [h]
  · rw [h]; exact Nat.le_of_ble_eq_true rfl

/-- A cast to `usize` keeps every value below `2^32`. -/
theorem usize_cast_val {U} (x : UScalar U) (h : x.val < 2 ^ 32) :
    (UScalar.cast .Usize x).val = x.val :=
  UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by
    rw [UScalarTy.Usize_numBits_eq]
    rcases System.Platform.numBits_eq with e | e <;> rw [e]
    exacts [h, h.trans (Nat.pow_lt_pow_right one_lt_two (Nat.le_of_ble_eq_true rfl))])

/-- `x >>> k` of an unsigned `x` by an `i32` of value `n` below the width is
`⌊x / 2^n⌋`. -/
theorem shr_i32_spec {U} (x : UScalar U) (k : Std.I32) (n : ℕ) (hk : k.val = n)
    (hn : n < U.numBits) : (x >>> k) ⦃ z => z.val = x.val / 2 ^ n ⦄ :=
  WP.spec_mono (UScalar.ShiftRight_IScalar_spec x k (hk ▸ Int.natCast_nonneg n)
    (hk ▸ Int.ofNat_lt.mpr hn)) fun z ⟨hz, _⟩ => by
    rw [hz, IScalar.toNat, hk, Int.toNat_natCast, Nat.shiftRight_eq_div_pow]

/-- `x <<< k` of an unsigned `x` by an `i32` of value `n` below the width is
`x · 2^n` when the product fits. -/
theorem shl_i32_spec {U} (x : UScalar U) (k : Std.I32) (n : ℕ) (hk : k.val = n)
    (hn : n < U.numBits) (hx : x.val * 2 ^ n < 2 ^ U.numBits) :
    (x <<< k) ⦃ z => z.val = x.val * 2 ^ n ⦄ :=
  WP.spec_mono (UScalar.ShiftLeft_IScalar_spec x k _ (hk ▸ Int.natCast_nonneg n)
    (hk ▸ Int.ofNat_lt.mpr hn) rfl) fun z ⟨hz, _⟩ => by
    rw [hz, IScalar.toNat, hk, Int.toNat_natCast, Nat.shiftLeft_eq, UScalar.size_def]
    exact Nat.mod_eq_of_lt hx

/-- `x &&& 1` of an `i128` is its last bit, `x mod 2`. -/
theorem and_one_val (x : Std.I128) : (x &&& 1#i128).val = x.val % 2 := by
  have one : (1#i128 : Std.I128).bv.toNat = 1 := rfl
  have d : (2 : ℤ) ∣ ((2 ^ IScalarTy.I128.numBits : ℕ) : ℤ) := ⟨2 ^ 127, rfl⟩
  have small : ((x.bv.toNat % 2 : ℕ) : ℤ).bmod (2 ^ IScalarTy.I128.numBits) = ((x.bv.toNat % 2 : ℕ) : ℤ) :=
    Int.bmod_eq_of_le (by rw [IScalarTy.I128_numBits_eq]; omega) (by rw [IScalarTy.I128_numBits_eq]; omega)
  rw [IScalar.val, IScalar.val, IScalar.bv_and, BitVec.toInt_and, one, Nat.and_one_is_mod,
    small, BitVec.toInt_eq_toNat_bmod, ← Int.emod_emod_of_dvd _ d, Int.bmod_emod,
    Int.emod_emod_of_dvd _ d]
  exact Int.natCast_emod _ 2

/-- The bits of `BitVec.abs` read as unsigned are the natural absolute value. -/
theorem toNat_abs_eq_natAbs {w : ℕ} (x : BitVec w) : x.abs.toNat = x.toInt.natAbs := by
  have lt := x.isLt
  rw [BitVec.toNat_abs, BitVec.toInt_eq_msb_cond]
  cases x.msb
  · exact (Int.natAbs_natCast _).symm
  · rw [ite_eq_left rfl, ite_eq_left rfl]
    omega

/-- `i8::unsigned_abs` is `natAbs`. -/
theorem I8_unsigned_abs_spec (x : Std.I8) :
    core.num.I8.unsigned_abs x ⦃ u => u.val = x.val.natAbs ⦄ :=
  (WP.spec_ok _).mpr (toNat_abs_eq_natAbs x.bv)

/-- `i16::unsigned_abs` is `natAbs`. -/
theorem I16_unsigned_abs_spec (x : Std.I16) :
    core.num.I16.unsigned_abs x ⦃ u => u.val = x.val.natAbs ⦄ :=
  (WP.spec_ok _).mpr (toNat_abs_eq_natAbs x.bv)

/-- `i32::unsigned_abs` is `natAbs`. -/
theorem I32_unsigned_abs_spec (x : Std.I32) :
    core.num.I32.unsigned_abs x ⦃ u => u.val = x.val.natAbs ⦄ :=
  (WP.spec_ok _).mpr (toNat_abs_eq_natAbs x.bv)

/-- `i64::unsigned_abs` is `natAbs`. -/
theorem I64_unsigned_abs_spec (x : Std.I64) :
    core.num.I64.unsigned_abs x ⦃ u => u.val = x.val.natAbs ⦄ :=
  (WP.spec_ok _).mpr (toNat_abs_eq_natAbs x.bv)

/-- `leading_zeros` of a non-zero `n` of every unsigned width is
`BITS - 1 - ⌊log₂ n⌋`. -/
theorem leading_zeros_val {U} (n : UScalar U) (hn : n.val ≠ 0) (hU : U.numBits < 2 ^ 32) :
    (⟨BitVec.leadingZeros n.bv⟩ : Std.U32).val = U.numBits - Nat.log 2 n.val - 1 := by
  have hb : n.bv ≠ 0 := fun h => hn ((congrArg BitVec.toNat h).trans rfl)
  rw [UScalar.val, BitVec.leadingZeros, ite_eq_right hb, show n.bv.toNat = n.val from rfl]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _)
    (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hU))

end Fulcrum

end
