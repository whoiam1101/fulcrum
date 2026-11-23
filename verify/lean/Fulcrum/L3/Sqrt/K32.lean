module

public import Fulcrum.L3.Sqrt.RsqrtTable
public import Fulcrum.Math.Rsqrt
public import Fulcrum.Lemmas.Loop
public import Fulcrum.Lemmas.Int

/-!
# L3: `kernel::k32::isqrt`

`isqrt(n)` of `k32`, as Aeneas extracts it, never fails and is `⌊√n⌋` on its
domain `n ≤ 3 · 2^62`. `n` is shifted left by an even `z` to
`m ∈ [2^62, 2^64)`; the start from `RSQRT_START`, one Newton step for the
reciprocal root and the Karp–Markstein step give `s₁² ≤ m + 2^57`
(`Math/Rsqrt.lean`), so `(x + 1)²` fits `u64`, and the loops up and down end at
`⌊√n⌋` (`ascend64_spec`, `check_descend_spec`).
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace Fulcrum

/-- The upward loop of `k32::isqrt`: from `x² ≤ n`, step up while `(x + 1)² ≤ n`. -/
theorem ascend64_spec (n x : Std.U64) (hn : n.val ≤ 3 * 2 ^ 62) (hx : x.val * x.val ≤ n.val) :
    fulcrum.kernel.k32.isqrt_loop0 n x ⦃ r => r.val = Nat.sqrt n.val ⦄ := by
  have sq32 : Nat.sqrt n.val < 2 ^ 32 - 1 := Nat.sqrt_lt.mpr (hn.trans_lt (Nat.le_of_ble_eq_true rfl))
  unfold fulcrum.kernel.k32.isqrt_loop0
  refine loop.spec_decr_nat (fun y => Nat.sqrt n.val + 1 - y.val)
    (fun y => y.val * y.val ≤ n.val) _ _ x ?_ hx
  intro y hy
  have ys : y.val ≤ Nat.sqrt n.val := Nat.le_sqrt.mpr hy
  unfold fulcrum.kernel.k32.isqrt_loop0.body
  refine WP.spec_bind (UScalar.add_spec (x := y) (y := 1#u64)
    (by rw [lit_val, U64_max_val]; omega)) fun i hi => ?_
  rw [lit_val] at hi
  have i32 : i.val ≤ 2 ^ 32 - 1 := hi ▸ ys.trans_lt sq32
  refine WP.spec_bind (UScalar.mul_spec (x := i) (y := i)
    (by rw [U64_max_val]; exact (Nat.mul_le_mul i32 i32).trans (Nat.le_of_ble_eq_true rfl))) fun i1 hi1 => ?_
  by_cases hle : i1 ≤ n
  · rw [ite_eq_left hle, WP.spec_ok]
    have : i.val * i.val ≤ n.val := hi1 ▸ hle
    exact ⟨this, Nat.sub_lt_sub_left (Nat.lt_succ_of_le ys) (hi ▸ Nat.lt_succ_self _)⟩
  · rw [ite_eq_right hle, WP.spec_ok]
    exact Nat.eq_sqrt.mpr ⟨hy, hi ▸ hi1 ▸ not_le.mp hle⟩

/-- `k32::NEWTON_STEPS = 0`. -/
theorem k32_newton_steps : fulcrum.kernel.k32.NEWTON_STEPS = 0#u32 := by
  unfold fulcrum.kernel.k32.NEWTON_STEPS; rfl

/-- `k32::NEWTON_STEPS = 0`: the Newton loop returns its start. -/
theorem k32_newton1_spec (n x : Std.U64) :
    fulcrum.kernel.k32.isqrt_loop1 n x 0#u32 ⦃ r => r = x ⦄ := by
  unfold fulcrum.kernel.k32.isqrt_loop1
  refine loop_done_spec _ (fun y i => ?_) x _
  unfold fulcrum.kernel.k32.isqrt_loop1.body
  dsimp only
  rw [k32_newton_steps, ite_eq_right (show ¬ i < 0#u32 from Nat.not_lt_zero _)]

/-- `k32::NEWTON_STEPS = 0`: the second Newton loop returns its start. -/
theorem k32_newton3_spec (n x : Std.U64) :
    fulcrum.kernel.k32.isqrt_loop3 n x 0#u32 ⦃ r => r = x ⦄ := by
  unfold fulcrum.kernel.k32.isqrt_loop3
  refine loop_done_spec _ (fun y i => ?_) x _
  unfold fulcrum.kernel.k32.isqrt_loop3.body
  dsimp only
  rw [k32_newton_steps, ite_eq_right (show ¬ i < 0#u32 from Nat.not_lt_zero _)]

/-- Clearing the last bit of a small `u32`. -/
theorem clear_low_bit (k : ℕ) (hk : k < 64) : k &&& (2 ^ 32 - 2) = 2 * (k / 2) := by
  have m2 : 2 * (k / 2) = (k / 2) <<< 1 := by rw [Nat.shiftLeft_eq, pow_one, Nat.mul_comm]
  rw [show 2 ^ 32 - 2 = (2 ^ 31 - 1) <<< 1 from rfl, m2]
  refine Nat.eq_of_testBit_eq fun i => ?_
  rw [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one,
    Nat.testBit_div_two]
  rcases i with _ | j
  · rw [decide_eq_false (Nat.not_succ_le_zero 0), Bool.false_and, Bool.false_and, Bool.and_false]
  rw [Nat.add_sub_cancel, decide_eq_true (Nat.le_add_left 1 j), Bool.true_and, Bool.true_and]
  by_cases hj : j < 31
  · rw [decide_eq_true hj, Bool.and_true]
  · rw [decide_eq_false hj, Bool.and_false, Nat.testBit_lt_two_pow ((hk.trans_le
      (Nat.le_of_ble_eq_true rfl : 64 ≤ 2 ^ (31 + 1))).trans_le
      (Nat.pow_le_pow_right two_pos (Nat.succ_le_succ (le_of_not_gt hj))))]

/-- L3 on the code: `kernel::k32::isqrt` is `⌊√n⌋` for `n ≤ 3 · 2^62`. -/
theorem k32_isqrt_spec (n : Std.U64) (hn : n.val ≤ 3 * 2 ^ 62) :
    fulcrum.kernel.k32.isqrt n ⦃ r => r.val = Nat.sqrt n.val ⦄ := by
  unfold fulcrum.kernel.k32.isqrt
  by_cases h2 : n < 2#u64
  · rw [ite_eq_left h2, WP.spec_ok]
    exact sqrt_eq_self_of_lt_two n.val h2
  rw [ite_eq_right h2]
  have hn2 : 2 ≤ n.val := Nat.le_of_not_lt h2
  obtain ⟨L, hL⟩ : ∃ L, L = Nat.log 2 n.val := ⟨_, rfl⟩
  have hlo : 2 ^ L ≤ n.val := hL ▸ Nat.pow_log_le_self 2 (Nat.ne_zero_of_lt hn2)
  have hhi : n.val < 2 ^ (L + 1) := hL ▸ Nat.lt_pow_succ_log_self Nat.one_lt_two _
  have L63 : L ≤ 63 := Nat.le_of_lt_succ ((Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp
    (hlo.trans_lt (hn.trans_lt (Nat.le_of_ble_eq_true rfl))))
  have hlz : (core.num.U64.leading_zeros n).val = 64 - Nat.log 2 n.val - 1 :=
    leading_zeros_val n (Nat.ne_zero_of_lt hn2) (Nat.le_of_ble_eq_true rfl)
  rw [← hL] at hlz
  rw [lift, bind_ok, lift, bind_ok, lift, bind_ok]
  have hz : (core.num.U64.leading_zeros n &&& ~~~1#u32).val = 2 * ((63 - L) / 2) := by
    rw [UScalar.val_and, hlz]
    have : (~~~1#u32 : Std.U32).val = 2 ^ 32 - 2 := rfl
    rw [this, show 64 - L - 1 = 63 - L by omega]
    exact clear_low_bit _ (by omega)
  obtain ⟨z, hzd⟩ : ∃ z, z = 2 * ((63 - L) / 2) := ⟨_, rfl⟩
  rw [← hzd] at hz
  have z1 : L + z ≤ 63 := by omega
  have z2 : 62 ≤ L + z := by omega
  have mlo : 2 ^ 62 ≤ n.val * 2 ^ z :=
    calc 2 ^ 62 ≤ 2 ^ (L + z) := Nat.pow_le_pow_right two_pos z2
      _ = 2 ^ L * 2 ^ z := pow_add _ _ _
      _ ≤ n.val * 2 ^ z := Nat.mul_le_mul_right _ hlo
  have mhi : n.val * 2 ^ z < 2 ^ 64 :=
    calc n.val * 2 ^ z < 2 ^ (L + 1) * 2 ^ z := Nat.mul_lt_mul_of_pos_right hhi (Nat.two_pow_pos _)
      _ = 2 ^ (L + 1 + z) := (pow_add _ _ _).symm
      _ ≤ 2 ^ 64 := Nat.pow_le_pow_right two_pos
        ((Nat.add_right_comm L 1 z).trans_le (Nat.succ_le_succ z1))
  refine WP.spec_bind (UScalar.ShiftLeft_spec n (core.num.U64.leading_zeros n &&& ~~~1#u32) _
    (by rw [hz, UScalarTy.U64_numBits_eq]; omega) rfl) fun m ⟨hm, _⟩ => ?_
  have hm' : m.val = n.val * 2 ^ z := by
    rw [hm, hz, Nat.shiftLeft_eq, UScalar.size_def, UScalarTy.U64_numBits_eq]
    exact Nat.mod_eq_of_lt mhi
  refine WP.spec_bind (shr_i32_spec m 32#i32 32 rfl (Nat.le_of_ble_eq_true rfl))
    fun a ha => ?_
  refine WP.spec_bind rsqrt_start_spec fun tab htab => ?_
  refine WP.spec_bind (shr_i32_spec m 56#i32 56 rfl (Nat.le_of_ble_eq_true rfl))
    fun i2 hi2 => ?_
  have t1 : 64 ≤ i2.val := hi2 ▸ (Nat.le_div_iff_mul_le (Nat.two_pow_pos 56)).mpr (hm' ▸ mlo)
  have t2 : i2.val < 256 := hi2 ▸ (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 56)).mpr (hm' ▸ mhi)
  rw [lift, bind_ok]
  have c3 : (UScalar.cast .Usize i2).val = i2.val := usize_cast_val i2 (t2.trans (Nat.le_of_ble_eq_true rfl))
  refine WP.spec_bind (UScalar.sub_spec (x := UScalar.cast .Usize i2) (y := 64#usize)
    (by rw [c3]; exact t1)) fun i4 ⟨hi4, _⟩ => ?_
  rw [c3, lit_val] at hi4
  have k192 : i4.val < 192 := hi4 ▸ Nat.sub_lt_left_of_lt_add t1 t2
  refine WP.spec_bind (Array.index_usize_spec tab i4 (by rw [Array.length, tab.property]; exact k192))
    fun i5 hi5 => ?_
  have e1 : i5 = tab.val[i4.val]! := by
    rw [hi5]; exact (getElem!_pos tab.val _ (by rw [tab.property]; exact k192)).symm
  obtain ⟨Yt1, Yt2⟩ := htab i4.val k192
  rw [← e1, show i4.val + 64 = i2.val from hi4 ▸ Nat.sub_add_cancel t1] at Yt1 Yt2
  rw [lift, bind_ok]
  have Y32 : i5.val < 2 ^ 32 := i5.hmax
  have cy : (UScalar.cast .U64 i5).val = i5.val :=
    UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (Y32.trans (Nat.le_of_ble_eq_true rfl))
  obtain ⟨At1, At2⟩ := div_pow_bounds (q := i2.val) (a := a.val) (k := 24)
    (by rw [hi2, ha, Nat.div_div_eq_div_mul, ← pow_add])
  obtain ⟨Am1, Am2⟩ := div_pow_bounds ha
  have A32 : a.val < 2 ^ 32 := At2.trans_le (Nat.mul_le_mul_right _ t2)
  refine WP.spec_bind (shl_i32_spec 3#u64 62#i32 62 rfl (Nat.le_of_ble_eq_true rfl)
    (by rw [lit_val]; exact Nat.le_of_ble_eq_true rfl)) fun i6 hi6' => ?_
  rw [lit_val] at hi6'
  have YY : i5.val * i5.val < 2 ^ 64 := Nat.mul_self_lt_mul_self Y32
  refine WP.spec_bind (UScalar.mul_spec (by rw [cy, U64_max_val]; exact Nat.le_sub_one_of_lt YY))
    fun i7 hi7 => ?_
  rw [cy] at hi7
  refine WP.spec_bind (shr_i32_spec i7 32#i32 32 rfl (Nat.le_of_ble_eq_true rfl))
    fun i8 hi8 => ?_
  rw [hi7] at hi8
  obtain ⟨c1, c2⟩ := div_pow_bounds hi8
  have Y33 : (i5.val : ℤ) < 2 ^ 33 := by exact_mod_cast Y32.trans (Nat.le_of_ble_eq_true rfl : 2 ^ 32 < 2 ^ 33)
  have R1 : a.val * i8.val ≤ 3 * 2 ^ 62 := by
    have := rsqrt_r1 a.val i2.val i5.val i8.val (by exact_mod_cast t1) (by exact_mod_cast t2)
      (by exact_mod_cast At1) (by exact_mod_cast At2) Y33
      (by rw [sq]; exact_mod_cast Yt1) (by rw [sq]; exact_mod_cast Yt2) (by rw [sq]; exact_mod_cast c1)
    exact_mod_cast this
  refine WP.spec_bind (UScalar.mul_spec (x := a) (y := i8)
    (by rw [U64_max_val]; exact R1.trans (Nat.le_of_ble_eq_true rfl))) fun i9 hi9 => ?_
  refine WP.spec_bind (UScalar.sub_spec (x := i6) (y := i9) (by rw [hi6', hi9]; exact R1))
    fun i10 ⟨hi10, _⟩ => ?_
  rw [hi6', hi9] at hi10
  refine WP.spec_bind (shr_i32_spec i10 32#i32 32 rfl (Nat.le_of_ble_eq_true rfl))
    fun i11 hi11 => ?_
  have i30 : i11.val ≤ 3 * 2 ^ 30 :=
    hi11 ▸ Nat.div_le_of_le_mul (hi10 ▸ (Nat.sub_le _ _).trans_eq rfl)
  have Yi : i5.val * i11.val ≤ 2 ^ 32 * (3 * 2 ^ 30) := Nat.mul_le_mul Y32.le i30
  refine WP.spec_bind (UScalar.mul_spec (x := UScalar.cast .U64 i5) (y := i11)
    (by rw [cy, U64_max_val]; exact Yi.trans (Nat.le_of_ble_eq_true rfl))) fun i12 hi12 => ?_
  rw [cy] at hi12
  refine WP.spec_bind (shr_i32_spec i12 31#i32 31 rfl (Nat.le_of_ble_eq_true rfl))
    fun y1 hy1 => ?_
  rw [hi12] at hy1
  obtain ⟨y1a, y1b⟩ := div_pow_bounds hy1
  obtain ⟨i11a, i11b⟩ := div_pow_bounds hi11
  obtain ⟨sN, hsN⟩ : ∃ sN, sN = a.val * y1.val / 2 ^ 31 := ⟨_, rfl⟩
  obtain ⟨sNa, sNb⟩ := div_pow_bounds hsN
  have core := rsqrt_core (m.val : ℤ) a.val i2.val i5.val i8.val i10.val i11.val y1.val sN
    (by exact_mod_cast t1) (by exact_mod_cast t2) (by exact_mod_cast Am1) (by exact_mod_cast Am2)
    (by exact_mod_cast At1) (by exact_mod_cast At2) (Int.natCast_nonneg _) Y33
    (by rw [sq]; exact_mod_cast Yt1) (by rw [sq]; exact_mod_cast Yt2)
    (by rw [sq]; exact_mod_cast c1) (by rw [sq]; exact_mod_cast c2)
    (by rw [hi10, Nat.cast_sub R1]; push_cast; rfl)
    (by exact_mod_cast i11a) (by exact_mod_cast i11b)
    (by exact_mod_cast y1a) (by exact_mod_cast y1b) (Int.natCast_nonneg _)
    (by exact_mod_cast sNa) (by exact_mod_cast sNb) (Int.natCast_nonneg _)
  obtain ⟨_, G2, G3, G4, G5⟩ := core
  have G2' : a.val * y1.val < 2 ^ 64 := by exact_mod_cast G2
  refine WP.spec_bind (UScalar.mul_spec (x := a) (y := y1)
    (by rw [U64_max_val]; exact Nat.le_sub_one_of_lt G2')) fun i13 hi13 => ?_
  refine WP.spec_bind (shr_i32_spec i13 31#i32 31 rfl (Nat.le_of_ble_eq_true rfl))
    fun sc hsc => ?_
  rw [hi13, ← hsN] at hsc
  have A30 : 2 ^ 30 ≤ a.val := (Nat.mul_le_mul_right (2 ^ 24) t1).trans At1
  obtain ⟨eZ, heZ⟩ : ∃ eZ : ℤ, eZ = (m.val : ℤ) - (sN : ℤ) ^ 2 := ⟨_, rfl⟩
  obtain ⟨cZ, hcZ⟩ : ∃ cZ : ℤ, cZ = (y1.val : ℤ) * eZ / 2 ^ 64 := ⟨_, rfl⟩
  have km := km_core (m.val : ℤ) sN y1.val a.val eZ cZ (by rw [hm']; exact_mod_cast mlo)
    (by rw [hm']; exact_mod_cast mhi) (by exact_mod_cast A30)
    (by exact_mod_cast G2') (Int.natCast_nonneg _) (Int.natCast_nonneg _) G4 G5 heZ
    (by rw [hcZ]; exact Int.ediv_mul_le _ (pow_ne_zero _ two_ne_zero))
    (by rw [hcZ]; exact Int.lt_ediv_add_one_mul_self _ (pow_pos zero_lt_two _))
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9⟩ := km
  rw [lift, bind_ok, lift, bind_ok, lift, bind_ok, lift, bind_ok, lift, bind_ok, lift, bind_ok]
  have hw : ((core.num.U64.wrapping_sub m (core.num.U64.wrapping_mul sc sc)).val : ℤ) %
      ((2 ^ 64 : ℕ) : ℤ) = eZ % ((2 ^ 64 : ℕ) : ℤ) := by
    rw [core.num.U64.wrapping_sub_val_eq, core.num.U64.wrapping_mul_val_eq, hsc, UScalar.size_def,
      UScalarTy.U64_numBits_eq, heZ, sq]
    push_cast
    omega
  have he : (UScalar.hcast .I64 (core.num.U64.wrapping_sub m (core.num.U64.wrapping_mul sc sc))).val
      = eZ := by
    rw [UScalar.hcast_val_eq, IScalarTy.I64_numBits_eq, bmod_congr _ _ _ hw]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  have hs16 : (UScalar.hcast .I64 sc).val = sN := by
    rw [UScalar.hcast_val_eq, hsc, IScalarTy.I64_numBits_eq]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  have hy17 : (UScalar.hcast .I128 y1).val = y1.val := by
    rw [UScalar.hcast_val_eq, IScalarTy.I128_numBits_eq]
    exact Int.bmod_eq_of_le (by omega) (by omega)
  have he18 : (IScalar.cast .I128 (UScalar.hcast .I64 (core.num.U64.wrapping_sub m
      (core.num.U64.wrapping_mul sc sc)))).val = eZ := by
    rw [IScalar.val_mod_pow_greater_numBits _ _ (Nat.le_of_ble_eq_true rfl), he]
  have b19 := in_bounds_of_pow (W := .I128) (m := 127) rfl k3 k4
  rw [← hy17, ← he18] at b19
  refine WP.spec_bind (IScalar.mul_spec b19.1 b19.2)
    fun i19 hi19 => ?_
  rw [hy17, he18] at hi19
  refine WP.spec_bind (IScalar.ShiftRight_IScalar_spec i19 64#i32 (Int.natCast_nonneg 64)
    (Int.ofNat_lt.mpr (Nat.le_of_ble_eq_true rfl)))
    fun i20 ⟨hi20, _⟩ => ?_
  rw [show (64#i32 : Std.I32).toNat = 64 from rfl, shr_eq_div, hi19, ← hcZ] at hi20
  rw [lift, bind_ok]
  have hc21 : (IScalar.cast .I64 i20).val = cZ := by
    rw [IScalar.cast_val_eq, hi20, IScalarTy.I64_numBits_eq, IScalarTy.I128_numBits_eq,
      show min 64 128 = 64 from rfl]
    exact Int.bmod_eq_of_le (by push_cast; omega) (by push_cast; omega)
  have b22 := in_bounds_of_pow (W := .I64) (m := 63) rfl
    ((neg_nonpos.mpr (pow_pos zero_lt_two 63).le).trans k7) k8
  rw [← hs16, ← hc21] at b22
  refine WP.spec_bind (IScalar.add_spec b22.1 b22.2)
    fun i22 hi22 => ?_
  rw [hs16, hc21] at hi22
  rw [lift, bind_ok]
  have hs1 : ((IScalar.hcast .U64 i22).val : ℤ) = sN + cZ := by
    rw [IScalar.hcast_val_eq, hi22, UScalarTy.U64_numBits_eq, Int.emod_eq_of_lt (by omega) (by omega)]
    exact Int.toNat_of_nonneg k7
  obtain ⟨S1, hS1⟩ : ∃ S1 : ℕ, S1 = (IScalar.hcast .U64 i22).val := ⟨_, rfl⟩
  rw [← hS1] at hs1
  have S1sq : S1 * S1 ≤ m.val + 2 ^ 57 := by
    have : ((S1 * S1 : ℕ) : ℤ) ≤ (m.val : ℤ) + 2 ^ 57 := by push_cast; rw [hs1, ← sq]; exact k9
    exact_mod_cast this
  obtain ⟨i23, hi23, hi23v⟩ := UScalar.div_spec (core.num.U64.leading_zeros n &&& ~~~1#u32)
    (y := 2#u32) (Nat.succ_ne_zero _)
  rw [hi23, bind_ok]
  rw [hz, lit_val] at hi23v
  have zh : 2 ^ (i23.val) * 2 ^ (i23.val) = 2 ^ z := by rw [← pow_add]; congr 1; omega
  refine WP.spec_bind (UScalar.ShiftRight_spec (IScalar.hcast .U64 i22) i23
    (by rw [UScalarTy.U64_numBits_eq]; omega)) fun x ⟨hx, _⟩ => ?_
  rw [← hS1, Nat.shiftRight_eq_div_pow] at hx
  have xsq : x.val * x.val ≤ n.val + 2 ^ 57 := by
    have h1 : x.val * 2 ^ i23.val ≤ S1 := hx ▸ Nat.div_mul_le_self _ _
    refine Nat.le_of_mul_le_mul_right ?_ (Nat.two_pow_pos z)
    calc x.val * x.val * 2 ^ z = (x.val * 2 ^ i23.val) * (x.val * 2 ^ i23.val) := by
          rw [← zh]; ring
      _ ≤ S1 * S1 := Nat.mul_le_mul h1 h1
      _ ≤ n.val * 2 ^ z + 2 ^ 57 := hm' ▸ S1sq
      _ ≤ n.val * 2 ^ z + 2 ^ 57 * 2 ^ z := Nat.add_le_add_left (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)) _
      _ = (n.val + 2 ^ 57) * 2 ^ z := (Nat.add_mul _ _ _).symm
  have x32 : x.val ≤ 2 ^ 32 - 2 := Nat.le_sub_one_of_lt (Nat.mul_self_lt_mul_self_iff.mp
    ((xsq.trans (Nat.add_le_add_right hn _)).trans_lt (Nat.le_of_ble_eq_true rfl)))
  refine WP.spec_bind (UScalar.add_spec (x := x) (y := 1#u64)
    (by rw [lit_val, U64_max_val]; exact Nat.add_le_add_right x32 1 |>.trans (Nat.le_of_ble_eq_true rfl)))
    fun i24 hi24 => ?_
  rw [lit_val] at hi24
  have i24m : i24.val ≤ 2 ^ 32 - 1 := hi24 ▸ Nat.add_le_add_right x32 1
  refine WP.spec_bind (UScalar.mul_spec (x := i24) (y := i24)
    (by rw [U64_max_val]; exact (Nat.mul_le_mul i24m i24m).trans (Nat.le_of_ble_eq_true rfl))) fun i25 hi25 => ?_
  by_cases hle : i25 ≤ n
  · rw [ite_eq_left hle]
    refine WP.spec_bind (ascend64_spec n i24 hn (hi25 ▸ hle)) fun x1 hx1 => ?_
    refine WP.spec_bind (k32_newton1_spec n x1) fun x2 hx2 => ?_
    subst hx2
    have s2 : x2.val * x2.val ≤ n.val := hx1 ▸ Nat.sqrt_le n.val
    unfold fulcrum.kernel.k32.isqrt_loop2
    exact check_descend_spec n x2 1#u64 rfl hx1.ge
      (s2.trans (hn.trans (by rw [U64_max_val]; exact Nat.le_of_ble_eq_true rfl)))
  · have gt : n.val < (x.val + 1) * (x.val + 1) := hi24 ▸ hi25 ▸ not_le.mp hle
    rw [ite_eq_right hle]
    refine WP.spec_bind (k32_newton3_spec n x) fun x1 hx1 => ?_
    subst hx1
    unfold fulcrum.kernel.k32.isqrt_loop4
    exact check_descend_spec n x1 1#u64 rfl (Nat.le_of_lt_succ (Nat.sqrt_lt.mpr gt))
      ((Nat.mul_le_mul x32 x32).trans (by rw [U64_max_val]; exact Nat.le_of_ble_eq_true rfl))

end Fulcrum

end
