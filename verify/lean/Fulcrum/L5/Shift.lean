module

public import Fulcrum.L1.ShrRound
public import Fulcrum.Math.Range

/-!
# L5: `kernel::kN::midpoint`, `kernel::kN::shr` and `kernel::kN::shl`

On the storage type of every width, as Aeneas extracts them, none fails:
`midpoint(a, b) = (a | b) - ((a ^ b) >> 1)` is `round((a + b) / 2)`, since
`a + b = (a ^ b) + 2 (a & b)` and `a | b = (a & b) + (a ^ b)` hold for the
signed values too (`bits_split`, `midpoint_toInt`); `shr(a, n)` is
`round(a / 2^n)` for every `n`, the rule of `shr_round` on the storage type;
`shl(a, n)` is `a · 2^n` wrapped to the storage type, with the flag set exactly
when `a · 2^n` is out of range.
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace Fulcrum

/-- `a | b = (a & b) + (a ^ b)` and `a + b = (a ^ b) + 2 (a & b)` on naturals. -/
theorem bits_split (a b : ℕ) :
    a ||| b = (a &&& b) + (a ^^^ b) ∧ a + b = (a ^^^ b) + 2 * (a &&& b) := by
  induction b using Nat.div2Induction generalizing a with
  | ind b hb =>
    obtain (rfl|h) := Nat.eq_zero_or_pos b
    · simp
    · have ⟨h1, h2⟩ := hb h (a / 2)
      have o := Nat.mod_add_div (a ||| b) 2
      have n := Nat.mod_add_div (a &&& b) 2
      have x := Nat.mod_add_div (a ^^^ b) 2
      have sa := Nat.mod_add_div a 2
      have sb := Nat.mod_add_div b 2
      rw [Nat.or_div_two] at o
      rw [Nat.and_div_two] at n
      rw [Nat.xor_div_two] at x
      have om : (a ||| b) % 2 = a % 2 ||| b % 2 := Nat.or_mod_two
      have nm : (a &&& b) % 2 = a % 2 &&& b % 2 := by
        simpa using Nat.and_mod_two_pow (n := 1) (a := a) (b := b)
      have xm : (a ^^^ b) % 2 = a % 2 ^^^ b % 2 := by
        simpa using Nat.xor_mod_two_pow (n := 1) (a := a) (b := b)
      obtain (ha|ha) := Nat.mod_two_eq_zero_or_one a <;>
        obtain (hc|hc) := Nat.mod_two_eq_zero_or_one b <;> rw [ha, hc] at om nm xm
      all_goals
        generalize a ||| b = O at *
        generalize a &&& b = N at *
        generalize a ^^^ b = X at *
        generalize a / 2 ||| b / 2 = O' at *
        generalize a / 2 &&& b / 2 = N' at *
        generalize a / 2 ^^^ b / 2 = X' at *
        norm_num at om nm xm
        omega

/-- `(x | y) - ((x ^ y) >> 1)` of signed bit vectors is `⌊(x + y + 1) / 2⌋`. -/
theorem midpoint_toInt {w : ℕ} (x y : BitVec w) (m : ℕ) (hw : w = m + 1) :
    (x ||| y).toInt - (x ^^^ y).toInt >>> 1 = (x.toInt + y.toInt + 1) / 2 := by
  have ⟨h1, h2⟩ := bits_split x.toNat y.toNat
  have hP : ((2 ^ w : ℕ) : ℤ) = 2 * 2 ^ m := by rw [hw, pow_succ]; push_cast; ring
  rw [BitVec.toInt_eq_msb_cond (x ||| y), BitVec.toInt_eq_msb_cond (x ^^^ y),
    BitVec.toInt_eq_msb_cond x, BitVec.toInt_eq_msb_cond y, BitVec.msb_or, BitVec.msb_xor,
    BitVec.toNat_or, BitVec.toNat_xor, shr_eq_div, hP]
  generalize x.toNat ||| y.toNat = O at *
  generalize x.toNat ^^^ y.toNat = X at *
  generalize x.toNat &&& y.toNat = N at *
  generalize (2 : ℤ) ^ m = Q
  cases x.msb <;> cases y.msb <;> simp <;> omega

/-- The body of `kernel::kN::midpoint` on a storage type of `m + 2` bits:
`round((a + b) / 2)`, which fits. -/
theorem midpoint_shape {B} (a b : IScalar B) (m : ℕ) (hB : B.numBits = m + 1 + 1) :
    (do
        let i ← lift (a ||| b)
        let i1 ← lift (a ^^^ b)
        let i2 ← i1 >>> 1#i32
        i - i2)
      ⦃ r => r.val = roundHalfUp (exact 1 (a.val + b.val)) ⦄ := by
  have e : (a ||| b).val - (a ^^^ b).val >>> 1 = (a.val + b.val + 1) / 2 :=
    midpoint_toInt a.bv b.bv (m + 1) hB
  have ⟨la, ua⟩ := val_bounds a hB
  have ⟨lb, ub⟩ := val_bounds b hB
  have r1 : roundHalfUp (exact 1 (a.val + b.val)) = (a.val + b.val + 1) / 2 := by
    rw [← add_half_shr, shr_eq_div, pow_zero, pow_one]
  rw [pow_succ] at la ua lb ub
  have ⟨fl, fu⟩ := in_bounds_of_pow hB (x := (a.val + b.val + 1) / 2) (by omega) (by omega)
  rw [lift, bind_ok, lift, bind_ok]
  refine WP.spec_bind (IScalar.ShiftRight_IScalar_spec (a ^^^ b) 1#i32 (by decide)
    (by rw [hB, show (1#i32 : Std.I32).val = 1 from rfl]; omega)) fun i2 ⟨hi2, _⟩ => ?_
  have hv : (a ||| b).val - i2.val = (a.val + b.val + 1) / 2 := by
    rw [hi2, show (1#i32 : Std.I32).toNat = 1 from rfl]; exact e
  refine WP.spec_mono (IScalar.sub_spec (hv ▸ fl) (hv ▸ fu)) fun r hr => ?_
  rw [hr, hv, r1]

/-- The body of `kernel::kN::shr` on a storage type of `m + 2` bits: the rule of
`shr_round`, with `0` for shifts of `BITS = m + 2` and more. -/
theorem shr_shape {B} (a zero one : IScalar B) (n bits : Std.U32) (m : ℕ)
    (hB : B.numBits = m + 1 + 1) (hbits : bits.val = m + 2) (hzero : zero.val = 0)
    (hone : one.bv.toNat = 1) :
    (if n = 0#u32 then ok a
      else if n >= bits then ok zero
      else do
        let i ← a >>> n
        let i1 ← n - 1#u32
        let i2 ← a >>> i1
        let i3 ← lift (i2 &&& one)
        i + i3)
      ⦃ r => r.val = roundHalfUp (exact n.val a.val) ⦄ := by
  have ⟨la, ua⟩ := val_bounds a hB
  by_cases h0 : n = 0#u32
  · rw [ite_eq_left h0, WP.spec_ok, ← shrRound_eq, shrRound,
      ite_eq_left (c := n.val = 0) (congrArg UScalar.val h0)]
  have v0 : n.val ≠ 0 := fun e => h0 (UScalar.eq_of_val_eq e)
  rw [ite_eq_right h0]
  by_cases hs : n >= bits
  · have hs' : m + 1 + 1 ≤ n.val := hbits ▸ hs
    rw [ite_eq_left hs, WP.spec_ok, hzero, round_eq_zero_of_ge a.val n.val (m + 1) hs' la ua]
  have lt : n.val < B.numBits := hB ▸ hbits ▸ Nat.lt_of_not_le hs
  rw [ite_eq_right hs]
  refine WP.spec_bind (IScalar.ShiftRight_spec a n lt) fun i ⟨hi, _⟩ => ?_
  refine WP.spec_bind (U32.sub_spec (x := n) (y := 1#u32) (Nat.one_le_iff_ne_zero.mpr v0))
    fun i1 ⟨hi1, _⟩ => ?_
  refine WP.spec_bind (IScalar.ShiftRight_spec a i1 (hi1 ▸ Nat.sub_lt_of_lt lt))
    fun i2 ⟨hi2, _⟩ => ?_
  exact add_bit_spec a.val n.val m hB v0 la ua one hone i i2 hi (hi1 ▸ hi2)

/-- `a · 2^n` of a signed `a` of `m + 1` bits wraps to `0` when `n ≥ m + 1`,
and is in range only for `a = 0`. -/
theorem shl_big (a : ℤ) (n m : ℕ) (hn : m + 1 ≤ n) (la : -2 ^ m ≤ a) (ua : a < 2 ^ m) :
    wrap m (a * 2 ^ n) = 0 ∧ (InRange m (a * 2 ^ n) ↔ a = 0) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
  have p0 : (0 : ℤ) < 2 ^ m := pow_pos zero_lt_two m
  have pj : (1 : ℤ) ≤ 2 ^ j := one_le_pow₀ one_le_two
  have e : a * 2 ^ (m + 1 + j) = a * (2 ^ j * (2 * 2 ^ m)) := by rw [pow_add, pow_succ]; ring
  have hT : 2 * 2 ^ m ≤ (2 : ℤ) ^ j * (2 * 2 ^ m) := le_mul_of_one_le_left (by positivity) pj
  refine ⟨Int.bmod_eq_zero_of_dvd ⟨a * 2 ^ j, by rw [e]; push_cast; ring⟩, ?_⟩
  rw [e, InRange, minOf, maxOf]
  constructor
  · rintro ⟨lo, hi⟩
    by_contra h
    rcases lt_or_gt_of_ne h with h | h
    · nlinarith [mul_le_mul_of_nonneg_right (show a ≤ -1 by omega)
        (show (0 : ℤ) ≤ 2 ^ j * (2 * 2 ^ m) by positivity)]
    · nlinarith [mul_le_mul_of_nonneg_right (show 1 ≤ a by omega)
        (show (0 : ℤ) ≤ 2 ^ j * (2 * 2 ^ m) by positivity)]
  · rintro rfl
    simp only [zero_mul]
    exact ⟨neg_nonpos.mpr p0.le, sub_nonneg.mpr (one_le_pow₀ one_le_two)⟩

/-- `⌊wrap(a · 2^n) / 2^n⌋ = a` exactly when `a · 2^n` is in range, for
`n ≤ m`. -/
theorem shl_back_iff (a : ℤ) (n m : ℕ) (hn : n ≤ m) :
    (wrap m (a * 2 ^ n)) >>> n = a ↔ InRange m (a * 2 ^ n) := by
  rw [← wrap_eq_self_iff]
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hpow : (0 : ℤ) < 2 ^ n := pow_pos zero_lt_two n
  have pj : (0 : ℤ) < 2 ^ (j + 1) := pow_pos zero_lt_two _
  have dv : ((2 ^ (n + j + 1) : ℕ) : ℤ) ∣ a * 2 ^ n - wrap (n + j) (a * 2 ^ n) :=
    Int.ModEq.dvd (Int.bmod_emod (x := a * 2 ^ n) (m := 2 ^ (n + j + 1)))
  obtain ⟨q, hq⟩ := dv
  have hw : wrap (n + j) (a * 2 ^ n) = (a - q * 2 ^ (j + 1)) * 2 ^ n := by
    have : ((2 ^ (n + j + 1) : ℕ) : ℤ) = 2 ^ n * 2 ^ (j + 1) := by
      push_cast; rw [← pow_add]; ring_nf
    rw [this] at hq; linarith
  rw [hw, shr_eq_div, Int.mul_ediv_cancel _ hpow.ne']
  constructor
  · intro h
    have : q * 2 ^ (j + 1) = 0 := by linarith
    have hq0 : q = 0 := (mul_eq_zero.mp this).resolve_right pj.ne'
    rw [hq0]; ring
  · intro h
    have : (q * 2 ^ (j + 1)) * 2 ^ n = 0 := by linarith
    have hq0 : q = 0 := (mul_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hpow.ne')).resolve_right
      pj.ne'
    rw [hq0]; ring

/-- The body of `kernel::kN::shl` on a storage type of `m + 1` bits: `a · 2^n`
wrapped, and whether it is out of range. -/
theorem shl_shape {B} (a zero : IScalar B) (n bits : Std.U32) (m : ℕ)
    (hB : B.numBits = m + 1) (hbits : bits.val = m + 1) (hzero : zero.val = 0) :
    (if n >= bits then ok (zero, a != zero)
      else do
        let r ← a <<< n
        let i ← r >>> n
        ok (r, i != a))
      ⦃ p => p.1.val = wrap m (a.val * 2 ^ n.val) ∧
        (p.2 = true ↔ ¬InRange m (a.val * 2 ^ n.val)) ⦄ := by
  have ⟨la, ua⟩ := val_bounds a hB
  have ne_iff : ∀ x y : IScalar B, x ≠ y ↔ x.val ≠ y.val :=
    fun x y => ⟨fun h e => h (IScalar.eq_of_val_eq e), fun h e => h (congrArg IScalar.val e)⟩
  by_cases hs : n >= bits
  · have ⟨w0, hr⟩ := shl_big a.val n.val m (hbits ▸ hs) la ua
    rw [ite_eq_left hs, WP.spec_ok, hzero, w0, hr, bne_iff_ne, ne_iff, hzero]
    exact ⟨rfl, Iff.rfl⟩
  have lt : n.val < B.numBits := hB ▸ hbits ▸ Nat.lt_of_not_le hs
  rw [ite_eq_right hs]
  refine WP.spec_bind (IScalar.ShiftLeft_spec a n lt) fun r ⟨hr, _⟩ => ?_
  refine WP.spec_bind (IScalar.ShiftRight_spec r n lt) fun i ⟨hi, _⟩ => ?_
  have hw : r.val = wrap m (a.val * 2 ^ n.val) := by rw [hr, Int.shiftLeft_eq, hB]; rfl
  rw [WP.spec_ok, bne_iff_ne, ne_iff, hi, hw,
    ← shl_back_iff a.val n.val m (Nat.lt_succ_iff.mp (hB ▸ lt : n.val < m + 1))]
  exact ⟨rfl, Iff.rfl⟩

/-- L5 on the code: `kernel::k8::midpoint` is `round((a + b) / 2)`. -/
theorem k8_midpoint_spec (a b : Std.I8) :
    fulcrum.kernel.k8.midpoint a b ⦃ r => r.val = roundHalfUp (exact 1 (a.val + b.val)) ⦄ :=
  midpoint_shape a b 6 rfl

/-- L5 on the code: `kernel::k8::shr` is `round(a / 2^n)` for every `n`. -/
theorem k8_shr_spec (a : Std.I8) (n : Std.U32) :
    fulcrum.kernel.k8.shr a n ⦃ r => r.val = roundHalfUp (exact n.val a.val) ⦄ :=
  shr_shape a 0#i8 1#i8 n _ 6 rfl rfl rfl rfl

/-- L5 on the code: `kernel::k8::shl` is `a · 2^n` wrapped, with the flag set
exactly when it is out of range. -/
theorem k8_shl_spec (a : Std.I8) (n : Std.U32) :
    fulcrum.kernel.k8.shl a n ⦃ p => p.1.val = wrap 7 (a.val * 2 ^ n.val) ∧
      (p.2 = true ↔ ¬InRange 7 (a.val * 2 ^ n.val)) ⦄ :=
  shl_shape a 0#i8 n _ 7 rfl rfl rfl

/-- L5 on the code: `kernel::k16::midpoint` is `round((a + b) / 2)`. -/
theorem k16_midpoint_spec (a b : Std.I16) :
    fulcrum.kernel.k16.midpoint a b ⦃ r => r.val = roundHalfUp (exact 1 (a.val + b.val)) ⦄ :=
  midpoint_shape a b 14 rfl

/-- L5 on the code: `kernel::k16::shr` is `round(a / 2^n)` for every `n`. -/
theorem k16_shr_spec (a : Std.I16) (n : Std.U32) :
    fulcrum.kernel.k16.shr a n ⦃ r => r.val = roundHalfUp (exact n.val a.val) ⦄ :=
  shr_shape a 0#i16 1#i16 n _ 14 rfl rfl rfl rfl

/-- L5 on the code: `kernel::k16::shl` is `a · 2^n` wrapped, with the flag set
exactly when it is out of range. -/
theorem k16_shl_spec (a : Std.I16) (n : Std.U32) :
    fulcrum.kernel.k16.shl a n ⦃ p => p.1.val = wrap 15 (a.val * 2 ^ n.val) ∧
      (p.2 = true ↔ ¬InRange 15 (a.val * 2 ^ n.val)) ⦄ :=
  shl_shape a 0#i16 n _ 15 rfl rfl rfl

/-- L5 on the code: `kernel::k32::midpoint` is `round((a + b) / 2)`. -/
theorem k32_midpoint_spec (a b : Std.I32) :
    fulcrum.kernel.k32.midpoint a b ⦃ r => r.val = roundHalfUp (exact 1 (a.val + b.val)) ⦄ :=
  midpoint_shape a b 30 rfl

/-- L5 on the code: `kernel::k32::shr` is `round(a / 2^n)` for every `n`. -/
theorem k32_shr_spec (a : Std.I32) (n : Std.U32) :
    fulcrum.kernel.k32.shr a n ⦃ r => r.val = roundHalfUp (exact n.val a.val) ⦄ :=
  shr_shape a 0#i32 1#i32 n _ 30 rfl rfl rfl rfl

/-- L5 on the code: `kernel::k32::shl` is `a · 2^n` wrapped, with the flag set
exactly when it is out of range. -/
theorem k32_shl_spec (a : Std.I32) (n : Std.U32) :
    fulcrum.kernel.k32.shl a n ⦃ p => p.1.val = wrap 31 (a.val * 2 ^ n.val) ∧
      (p.2 = true ↔ ¬InRange 31 (a.val * 2 ^ n.val)) ⦄ :=
  shl_shape a 0#i32 n _ 31 rfl rfl rfl

/-- L5 on the code: `kernel::k64::midpoint` is `round((a + b) / 2)`. -/
theorem k64_midpoint_spec (a b : Std.I64) :
    fulcrum.kernel.k64.midpoint a b ⦃ r => r.val = roundHalfUp (exact 1 (a.val + b.val)) ⦄ :=
  midpoint_shape a b 62 rfl

/-- L5 on the code: `kernel::k64::shr` is `round(a / 2^n)` for every `n`. -/
theorem k64_shr_spec (a : Std.I64) (n : Std.U32) :
    fulcrum.kernel.k64.shr a n ⦃ r => r.val = roundHalfUp (exact n.val a.val) ⦄ :=
  shr_shape a 0#i64 1#i64 n _ 62 rfl rfl rfl rfl

/-- L5 on the code: `kernel::k64::shl` is `a · 2^n` wrapped, with the flag set
exactly when it is out of range. -/
theorem k64_shl_spec (a : Std.I64) (n : Std.U32) :
    fulcrum.kernel.k64.shl a n ⦃ p => p.1.val = wrap 63 (a.val * 2 ^ n.val) ∧
      (p.2 = true ↔ ¬InRange 63 (a.val * 2 ^ n.val)) ⦄ :=
  shl_shape a 0#i64 n _ 63 rfl rfl rfl

end Fulcrum

end
