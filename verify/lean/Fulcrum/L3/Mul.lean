module

public import Fulcrum.Kernel.Funs
public import Fulcrum.Spec
import Fulcrum.L1.ShrRound
import Fulcrum.Lemmas.Scalar
import Fulcrum.Math.Range
import Fulcrum.Math.Round

/-!
# L3: `kernel::kN::mul`

`mul(a, b)` of the kernel of every width, as Aeneas extracts it, never fails
and is `round(a · b / 2^F)`, to nearest with ties toward `+∞`, of the exact
product of the raw operands. `k8`..`k32` add `HALF = 2^(F-1)` and shift
(`round_frac_shape`); `k64` takes the floor and the first dropped bit, the form
of `shr_round`. Every width goes through `half_shape` and `mul_shape`: a raw
value has `n + 1` bits, the wide type `2n + 2`, and `F = k + 1` with
`k + (k + 1) = n`.
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace Fulcrum

/-- The product of two raw values of `n + 1` bits is at most `2^n · 2^n` in
magnitude. -/
theorem prod_abs_le {B} (a b : IScalar B) {n : ℕ} (hB : B.numBits = n + 1) :
    |a.val * b.val| ≤ 2 ^ n * 2 ^ n := by
  have ⟨la, ua⟩ := val_bounds a hB
  have ⟨lb, ub⟩ := val_bounds b hB
  rw [abs_mul]
  exact mul_le_mul (abs_le.mpr ⟨la, ua.le⟩) (abs_le.mpr ⟨lb, ub.le⟩) (abs_nonneg _)
    (pow_pos zero_lt_two _).le

/-- A value at most `2^n · 2^n` in magnitude, plus `2^k` with `k < n`, stays in
`[-2^(2n+1), 2^(2n+1))`. -/
theorem prod_bounds (x : ℤ) (n k : ℕ) (hk : k < n) (hx : |x| ≤ 2 ^ n * 2 ^ n) :
    -2 ^ (n + n + 1) ≤ x ∧ x + 2 ^ k < 2 ^ (n + n + 1) := by
  have ⟨lo, hi⟩ := abs_le.mp hx
  have sq : (0 : ℤ) ≤ 2 ^ n * 2 ^ n :=
    (mul_pos (pow_pos zero_lt_two n) (pow_pos zero_lt_two n)).le
  have one : (2 : ℤ) ^ n ≤ 2 ^ n * 2 ^ n :=
    le_mul_of_one_le_left (pow_pos zero_lt_two n).le (one_le_pow₀ one_le_two)
  rw [pow_succ, pow_add, mul_two]
  exact ⟨(neg_le_neg (le_add_of_nonneg_right sq)).trans lo,
    add_lt_add_of_le_of_lt hi ((pow_lt_pow_right₀ one_lt_two hk).trans_le one)⟩

/-- `x - 1` of an `i32` literal `x = k + 1` is `k`. -/
theorem sub_one_spec (f : Std.I32) (k : ℕ) (hf : f.val = k + 1) :
    (f - 1#i32) ⦃ i => i.val = k ⦄ := by
  have e : f.val - (1#i32 : Std.I32).val = k := by rw [hf]; exact Int.add_sub_cancel _ _
  have ⟨fl, fu⟩ := in_bounds_of_pow (W := .I32) (m := 31) rfl (x := k)
    ((neg_nonpos.mpr (pow_pos zero_lt_two 31).le).trans (Int.natCast_nonneg k))
    ((lt_add_one _).trans (hf ▸ (val_bounds f (n := 31) rfl).2))
  exact WP.spec_mono (IScalar.sub_spec (e ▸ fl) (e ▸ fu)) fun i hi => hi.trans e

/-- The body of `kernel::kN::HALF`: `1 << (F - 1)` is `2^k` for `F = k + 1` and
`k` below the top bit of the type. -/
theorem half_shape {W} (f : Std.I32) (one : IScalar W) (k m : ℕ) (hf : f.val = k + 1)
    (hone : one.val = 1) (hW : W.numBits = m + 1) (hk : k < m) :
    (do let i ← f - 1#i32; one <<< i) ⦃ h => h.val = 2 ^ k ⦄ := by
  refine WP.spec_bind (sub_one_spec f k hf) fun i hi => ?_
  refine WP.spec_mono (IScalar.ShiftLeft_IScalar_spec one i (hi ▸ Int.natCast_nonneg k)
    (hi ▸ Int.ofNat_lt.mpr (hW ▸ Nat.lt_succ_of_lt hk))) fun h ⟨hv, _⟩ => ?_
  rw [hv, IScalar.toNat, hi, Int.toNat_natCast, hone, Int.shiftLeft_eq, one_mul, hW]
  exact (wrap_eq_self_iff m _).2 ⟨(neg_nonpos.mpr (pow_pos zero_lt_two m).le).trans
    (pow_pos zero_lt_two k).le, Int.le_sub_one_of_lt (pow_lt_pow_right₀ one_lt_two hk)⟩

/-- `(p + h) >> sh` with `h = 2^k` and `sh = k + 1` rounds `p / 2^(k+1)` to
nearest, ties toward `+∞`, when the sum fits. -/
theorem add_half_shape {W} (p h : IScalar W) (sh : IScalar .I32) (k : ℕ) (hh : h.val = 2 ^ k)
    (hs : sh.val = ((k + 1 : ℕ) : ℤ)) (hk : k + 1 < W.numBits) (hfit : p.val + 2 ^ k ≤ IScalar.max W) :
    (do let i1 ← p + h; i1 >>> sh) ⦃ r => r.val = roundHalfUp (exact (k + 1) p.val) ⦄ := by
  have lo : IScalar.min W ≤ p.val + h.val :=
    hh ▸ (IScalar.min_def W ▸ p.hmin).trans (le_add_of_nonneg_right (pow_pos zero_lt_two k).le)
  refine WP.spec_bind (IScalar.add_spec lo (hh ▸ hfit)) fun i1 hi1 => ?_
  refine WP.spec_mono (IScalar.ShiftRight_IScalar_spec i1 sh (hs ▸ Int.natCast_nonneg _)
    (hs ▸ Int.ofNat_lt.mpr hk)) fun r ⟨hr, _⟩ => ?_
  rw [hr, IScalar.toNat, hs, hi1, hh, Int.toNat_natCast, add_half_shr]

/-- The body of `kernel::kN::round_frac` for `k8`..`k32`: the branch of `i128`
is not taken, and `HALF` is added before the shift. -/
theorem round_frac_shape {W} {c : Prop} [Decidable c] (hc : ¬c) (x half : Result (IScalar W))
    (p : IScalar W) (sh : IScalar .I32) (k : ℕ) (hhalf : half ⦃ h => h.val = 2 ^ k ⦄)
    (hs : sh.val = ((k + 1 : ℕ) : ℤ)) (hk : k + 1 < W.numBits)
    (hfit : p.val + 2 ^ k ≤ IScalar.max W) :
    (if c then x else do let i ← half; let i1 ← p + i; i1 >>> sh)
      ⦃ r => r.val = roundHalfUp (exact (k + 1) p.val) ⦄ := by
  rw [ite_eq_right hc]
  exact WP.spec_bind hhalf fun h hh => add_half_shape p h sh k hh hs hk hfit

/-- The body of `kernel::kN::mul`: both operands of `n + 1` bits are cast to
the wide type of `2n + 2` bits, multiplied without overflow and rounded by
`round_frac`. -/
theorem mul_shape {B W} (a b : IScalar B) (n k : ℕ) (hn : k + (k + 1) = n)
    (hB : B.numBits = n + 1) (hW : W.numBits = n + n + 1 + 1)
    (rf : IScalar W → Result (IScalar W))
    (hrf : ∀ p : IScalar W, p.val + 2 ^ k ≤ IScalar.max W →
      rf p ⦃ r => r.val = roundHalfUp (exact (k + 1) p.val) ⦄) :
    (do
        let i ← lift (IScalar.cast W a)
        let i1 ← lift (IScalar.cast W b)
        let i2 ← i * i1
        rf i2)
      ⦃ r => r.val = roundHalfUp (exact (k + 1) (a.val * b.val)) ⦄ := by
  have hBW : B.numBits ≤ W.numBits := hB ▸ hW ▸ Nat.succ_le_succ (Nat.le_add_right n (n + 1))
  have ca := IScalar.val_mod_pow_greater_numBits W a hBW
  have cb := IScalar.val_mod_pow_greater_numBits W b hBW
  have ⟨lo, hi⟩ := prod_bounds _ n k (hn ▸ Nat.lt_add_of_pos_right (Nat.succ_pos k))
    (prod_abs_le a b hB)
  have ⟨fl, fu⟩ := in_bounds_of_pow hW lo
    ((le_add_of_nonneg_right (pow_pos zero_lt_two k).le).trans_lt hi)
  rw [lift, bind_ok, lift, bind_ok]
  refine WP.spec_bind (IScalar.mul_spec (ca ▸ cb ▸ fl) (ca ▸ cb ▸ fu)) fun p hp => ?_
  rw [ca, cb] at hp
  exact hp ▸ hrf p (hp ▸ max_eq_pow_sub_one hW ▸ Int.le_sub_one_of_lt hi)

/-- `kernel::k8::HALF` is `2^3`. -/
theorem k8_half_spec : fulcrum.kernel.k8.HALF ⦃ h => h.val = 2 ^ 3 ⦄ := by
  unfold fulcrum.kernel.k8.HALF
  exact half_shape 4#i32 1#i16 3 15 rfl rfl rfl (Nat.le_of_ble_eq_true rfl)

/-- `kernel::k8::round_frac` rounds `p / 2^4` when `p + 2^3` fits. -/
theorem k8_round_frac_spec (p : Std.I16) (hfit : p.val + 2 ^ 3 ≤ IScalar.max .I16) :
    fulcrum.kernel.k8.round_frac p ⦃ r => r.val = roundHalfUp (exact 4 p.val) ⦄ :=
  round_frac_shape (fun h => Nat.ne_of_beq_eq_false rfl (congrArg UScalar.val h)) _ _ p
    4#i32 3 k8_half_spec rfl (Nat.le_of_ble_eq_true rfl) hfit

/-- L3 on the code: `kernel::k8::mul` is `round(a · b / 2^4)`. -/
theorem k8_mul_spec (a b : Std.I8) :
    fulcrum.kernel.k8.mul a b ⦃ r => r.val = roundHalfUp (exact 4 (a.val * b.val)) ⦄ :=
  mul_shape a b 7 3 rfl rfl rfl _ k8_round_frac_spec

/-- `kernel::k16::HALF` is `2^7`. -/
theorem k16_half_spec : fulcrum.kernel.k16.HALF ⦃ h => h.val = 2 ^ 7 ⦄ := by
  unfold fulcrum.kernel.k16.HALF
  exact half_shape 8#i32 1#i32 7 31 rfl rfl rfl (Nat.le_of_ble_eq_true rfl)

/-- `kernel::k16::round_frac` rounds `p / 2^8` when `p + 2^7` fits. -/
theorem k16_round_frac_spec (p : Std.I32) (hfit : p.val + 2 ^ 7 ≤ IScalar.max .I32) :
    fulcrum.kernel.k16.round_frac p ⦃ r => r.val = roundHalfUp (exact 8 p.val) ⦄ :=
  round_frac_shape (fun h => Nat.ne_of_beq_eq_false rfl (congrArg UScalar.val h)) _ _ p
    8#i32 7 k16_half_spec rfl (Nat.le_of_ble_eq_true rfl) hfit

/-- L3 on the code: `kernel::k16::mul` is `round(a · b / 2^8)`. -/
theorem k16_mul_spec (a b : Std.I16) :
    fulcrum.kernel.k16.mul a b ⦃ r => r.val = roundHalfUp (exact 8 (a.val * b.val)) ⦄ :=
  mul_shape a b 15 7 rfl rfl rfl _ k16_round_frac_spec

/-- `kernel::k32::HALF` is `2^15`. -/
theorem k32_half_spec : fulcrum.kernel.k32.HALF ⦃ h => h.val = 2 ^ 15 ⦄ := by
  unfold fulcrum.kernel.k32.HALF
  exact half_shape 16#i32 1#i64 15 63 rfl rfl rfl (Nat.le_of_ble_eq_true rfl)

/-- `kernel::k32::round_frac` rounds `p / 2^16` when `p + 2^15` fits. -/
theorem k32_round_frac_spec (p : Std.I64) (hfit : p.val + 2 ^ 15 ≤ IScalar.max .I64) :
    fulcrum.kernel.k32.round_frac p ⦃ r => r.val = roundHalfUp (exact 16 p.val) ⦄ :=
  round_frac_shape (fun h => Nat.ne_of_beq_eq_false rfl (congrArg UScalar.val h)) _ _ p
    16#i32 15 k32_half_spec rfl (Nat.le_of_ble_eq_true rfl) hfit

/-- L3 on the code: `kernel::k32::mul` is `round(a · b / 2^16)`. -/
theorem k32_mul_spec (a b : Std.I32) :
    fulcrum.kernel.k32.mul a b ⦃ r => r.val = roundHalfUp (exact 16 (a.val * b.val)) ⦄ :=
  mul_shape a b 31 15 rfl rfl rfl _ k32_round_frac_spec

/-- `kernel::k64::round_frac` is `shr_round(p, 32)` for every `i128`: the floor
and the first dropped bit. -/
theorem k64_round_frac_spec (p : Std.I128) :
    fulcrum.kernel.k64.round_frac p ⦃ r => r.val = roundHalfUp (exact 32 p.val) ⦄ := by
  unfold fulcrum.kernel.k64.round_frac
  rw [ite_eq_left (c := core.num.I128.BITS = 128#u32) rfl]
  refine WP.spec_bind (IScalar.ShiftRight_IScalar_spec p 32#i32 (Int.natCast_nonneg 32)
    (Int.ofNat_lt.mpr (Nat.le_of_ble_eq_true rfl)))
    fun i ⟨hi, _⟩ => ?_
  refine WP.spec_bind (sub_one_spec 32#i32 31 rfl) fun i1 hi1 => ?_
  refine WP.spec_bind (IScalar.ShiftRight_IScalar_spec p i1 (hi1 ▸ Int.natCast_nonneg 31)
    (hi1 ▸ Int.ofNat_lt.mpr (Nat.le_of_ble_eq_true rfl))) fun i2 ⟨hi2, _⟩ => ?_
  rw [IScalar.toNat, hi1, Int.toNat_natCast] at hi2
  exact add_bit_spec p.val 32 126 rfl (Nat.succ_ne_zero 31) p.hmin p.hmax 1#i128 rfl i i2 hi hi2

/-- L3 on the code: `kernel::k64::mul` is `round(a · b / 2^32)`. -/
theorem k64_mul_spec (a b : Std.I64) :
    fulcrum.kernel.k64.mul a b ⦃ r => r.val = roundHalfUp (exact 32 (a.val * b.val)) ⦄ :=
  mul_shape a b 63 31 rfl rfl rfl _ fun p _ => k64_round_frac_spec p

end Fulcrum

end
