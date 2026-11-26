module

public import Fulcrum.Kernel.Funs
public import Fulcrum.Spec
import Fulcrum.L3.Mul
import Fulcrum.Lemmas.Scalar
import Fulcrum.Math.Round

/-!
# L3: `kernel::kN::mul_add` and `kernel::kN::lerp`

`mul_add(a, b, c)` is `round((a · b + c · 2^F) / 2^F)`, the product plus a raw
value rounded once, and `lerp(a, b, t)` is `a + round((b - a) · t / 2^F)`, for
every width, as Aeneas extracts them: neither fails. Every width goes through
`mul_add_shape` and `lerp_shape`, with the widths of `mul_shape`.
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace Fulcrum

/-- `2^n · 2^j + 2^n ≤ 2^(2n+1)` for `j ≤ n`: a raw value of `n + 1` bits plus
one `2^j` times larger fits `2n + 2` bits. -/
theorem add_mul_pow_le (n j : ℕ) (hj : j < n + 1) :
    (2 : ℤ) ^ n * 2 ^ j + 2 ^ n ≤ 2 ^ (n + n + 1) := by
  rw [← mul_add_one, pow_succ, pow_add, mul_assoc, ← pow_succ]
  exact mul_le_mul_of_nonneg_left (Int.add_one_le_of_lt (pow_lt_pow_right₀ one_lt_two hj))
    (pow_pos zero_lt_two n).le

/-- The body of `kernel::kN::mul_add`: the rounded product plus `c` cast to the
wide type, without overflow, is the product plus `c · 2^F` rounded once. -/
theorem mul_add_shape {B W} (a b c : IScalar B) (n k : ℕ) (hn : k + (k + 1) = n)
    (hB : B.numBits = n + 1) (hW : W.numBits = n + n + 1 + 1) (m : Result (IScalar W))
    (hm : m ⦃ r => r.val = roundHalfUp (exact (k + 1) (a.val * b.val)) ⦄) :
    (do let i ← m; let i1 ← lift (IScalar.cast W c); i + i1)
      ⦃ r => r.val = roundHalfUp (exact (k + 1) (a.val * b.val + c.val * 2 ^ (k + 1))) ⦄ := by
  have hk : k < n := hn ▸ Nat.lt_add_of_pos_right (Nat.succ_pos k)
  have cc := IScalar.val_mod_pow_greater_numBits W c
    (hB ▸ hW ▸ Nat.succ_le_succ (Nat.le_add_right n (n + 1)))
  have ⟨lo, hi⟩ := abs_le.mp (prod_abs_le a b hB)
  have hR : (2 : ℤ) ^ n * 2 ^ k * 2 ^ (k + 1) = 2 ^ n * 2 ^ n := by
    rw [mul_assoc, ← pow_add, hn]
  have ⟨ml, mu⟩ := roundHalfUp_bounds (a.val * b.val) (-(2 ^ n * 2 ^ k)) (2 ^ n * 2 ^ k + 1) k
    (by rw [neg_mul, hR]; exact lo.trans (le_add_of_nonneg_right (pow_pos zero_lt_two k).le))
    (by
      rw [add_mul, one_mul, hR]
      exact add_lt_add_of_le_of_lt hi (pow_lt_pow_right₀ one_lt_two (Nat.lt_succ_self k)))
  have ⟨cl, cu⟩ := val_bounds c hB
  have top := add_mul_pow_le n k (Nat.lt_succ_of_lt hk)
  have ⟨fl, fu⟩ := in_bounds_of_pow hW
    ((neg_le_neg top).trans ((neg_add _ _).trans_le (add_le_add ml cl)))
    ((add_lt_add_of_le_of_lt (Int.lt_add_one_iff.mp mu) cu).trans_le top)
  refine WP.spec_bind hm fun x hx => ?_
  rw [lift, bind_ok]
  refine WP.spec_mono (IScalar.add_spec (hx ▸ cc ▸ fl) (hx ▸ cc ▸ fu)) fun r hr => ?_
  rw [hr, hx, cc, roundHalfUp_add_int]

/-- The body of `kernel::kN::lerp`: `b - a`, its product with `t` and `a` plus
the rounded product fit the wide type, so it is `a + round((b - a) · t / 2^F)`. -/
theorem lerp_shape {B W} (a b t : IScalar B) (n k : ℕ) (hn : k + (k + 1) = n)
    (hB : B.numBits = n + 1) (hW : W.numBits = n + n + 1 + 1)
    (rf : IScalar W → Result (IScalar W))
    (hrf : ∀ p : IScalar W, p.val + 2 ^ k ≤ IScalar.max W →
      rf p ⦃ r => r.val = roundHalfUp (exact (k + 1) p.val) ⦄) :
    (do
        let i ← lift (IScalar.cast W a)
        let i1 ← lift (IScalar.cast W b)
        let i2 ← lift (IScalar.cast W a)
        let i3 ← i1 - i2
        let i4 ← lift (IScalar.cast W t)
        let i5 ← i3 * i4
        let i6 ← rf i5
        i + i6)
      ⦃ r => r.val = a.val + roundHalfUp (exact (k + 1) ((b.val - a.val) * t.val)) ⦄ := by
  have hk : k < n := hn ▸ Nat.lt_add_of_pos_right (Nat.succ_pos k)
  have hBW : B.numBits ≤ W.numBits := hB ▸ hW ▸ Nat.succ_le_succ (Nat.le_add_right n (n + 1))
  have ca := IScalar.val_mod_pow_greater_numBits W a hBW
  have cb := IScalar.val_mod_pow_greater_numBits W b hBW
  have ct := IScalar.val_mod_pow_greater_numBits W t hBW
  have ⟨la, ua⟩ := val_bounds a hB
  have ⟨lb, ub⟩ := val_bounds b hB
  have ⟨lt, ut⟩ := val_bounds t hB
  have two : (2 : ℤ) ^ n - -2 ^ n = 2 ^ n * 2 := by rw [sub_neg_eq_add, ← mul_two]
  have hd : |b.val - a.val| < 2 ^ n * 2 := abs_sub_lt_iff.mpr
    ⟨((sub_lt_sub_right ub _).trans_le (sub_le_sub_left la _)).trans_eq two,
      ((sub_lt_sub_right ua _).trans_le (sub_le_sub_left lb _)).trans_eq two⟩
  have hp : |(b.val - a.val) * t.val| ≤ 2 ^ (n + n + 1) - 2 ^ n := by
    rw [abs_mul, pow_succ, pow_add, mul_right_comm, ← sub_one_mul]
    exact mul_le_mul (Int.le_sub_one_of_lt hd) (abs_le.mpr ⟨lt, ut.le⟩) (abs_nonneg _)
      ((abs_nonneg _).trans (Int.le_sub_one_of_lt hd))
  have ⟨pl, pu⟩ := abs_le.mp hp
  have p0 : (0 : ℤ) ≤ 2 ^ k := (pow_pos zero_lt_two k).le
  have plo : -2 ^ (n + n + 1) ≤ (b.val - a.val) * t.val :=
    (neg_le_neg (sub_le_self _ (pow_pos zero_lt_two n).le)).trans pl
  have phi : (b.val - a.val) * t.val + 2 ^ k < 2 ^ (n + n + 1) :=
    lt_sub_iff_add_lt.mp (pu.trans_lt (sub_lt_sub_left (pow_lt_pow_right₀ one_lt_two hk) _))
  have ⟨dl, du⟩ := abs_lt.mp (hd.trans_le (pow_succ (2 : ℤ) n ▸
    pow_le_pow_right₀ one_le_two (Nat.succ_le_succ (Nat.le_add_right n n))))
  have hV : (2 : ℤ) ^ n * 2 ^ (k + 1) * 2 ^ (k + 1) = 2 ^ (n + n + 1) := by
    rw [mul_assoc, ← pow_add, Nat.add_right_comm k 1 (k + 1), hn, ← pow_add, Nat.add_assoc]
  have ⟨ql, qu⟩ := roundHalfUp_bounds ((b.val - a.val) * t.val) (-(2 ^ n * 2 ^ (k + 1)))
    (2 ^ n * 2 ^ (k + 1)) k
    (by rw [neg_mul, hV]; exact plo.trans (le_add_of_nonneg_right p0)) (hV ▸ phi)
  have top := (add_comm _ _).trans_le (add_mul_pow_le n (k + 1) (Nat.succ_lt_succ hk))
  have ⟨dfl, dfu⟩ := in_bounds_of_pow hW dl.le du
  have ⟨pfl, pfu⟩ := in_bounds_of_pow hW plo ((le_add_of_nonneg_right p0).trans_lt phi)
  have ⟨sfl, sfu⟩ := in_bounds_of_pow hW
    ((neg_le_neg top).trans ((neg_add _ _).trans_le (add_le_add la ql)))
    ((add_lt_add ua qu).trans_le top)
  rw [lift, bind_ok, lift, bind_ok, bind_ok]
  refine WP.spec_bind (IScalar.sub_spec (ca ▸ cb ▸ dfl) (ca ▸ cb ▸ dfu)) fun d hd => ?_
  rw [lift, bind_ok]
  rw [ca, cb] at hd
  refine WP.spec_bind (IScalar.mul_spec (hd ▸ ct ▸ pfl) (hd ▸ ct ▸ pfu)) fun p hp => ?_
  rw [hd, ct] at hp
  refine WP.spec_bind (hrf p (hp ▸ max_eq_pow_sub_one hW ▸ Int.le_sub_one_of_lt phi))
    fun q hq => ?_
  refine WP.spec_mono (IScalar.add_spec (ca ▸ hq ▸ hp ▸ sfl) (ca ▸ hq ▸ hp ▸ sfu))
    fun r hr => ?_
  rw [hr, ca, hq, hp]

/-- L3 on the code: `kernel::k8::mul_add` is `round((a · b + c · 2^4) / 2^4)`. -/
theorem k8_mul_add_spec (a b c : Std.I8) :
    fulcrum.kernel.k8.mul_add a b c
      ⦃ r => r.val = roundHalfUp (exact 4 (a.val * b.val + c.val * 2 ^ 4)) ⦄ :=
  mul_add_shape a b c 7 3 rfl rfl rfl _ (k8_mul_spec a b)

/-- L3 on the code: `kernel::k8::lerp` is `a + round((b - a) · t / 2^4)`. -/
theorem k8_lerp_spec (a b t : Std.I8) :
    fulcrum.kernel.k8.lerp a b t
      ⦃ r => r.val = a.val + roundHalfUp (exact 4 ((b.val - a.val) * t.val)) ⦄ :=
  lerp_shape a b t 7 3 rfl rfl rfl _ k8_round_frac_spec

/-- L3 on the code: `kernel::k16::mul_add` is `round((a · b + c · 2^8) / 2^8)`. -/
theorem k16_mul_add_spec (a b c : Std.I16) :
    fulcrum.kernel.k16.mul_add a b c
      ⦃ r => r.val = roundHalfUp (exact 8 (a.val * b.val + c.val * 2 ^ 8)) ⦄ :=
  mul_add_shape a b c 15 7 rfl rfl rfl _ (k16_mul_spec a b)

/-- L3 on the code: `kernel::k16::lerp` is `a + round((b - a) · t / 2^8)`. -/
theorem k16_lerp_spec (a b t : Std.I16) :
    fulcrum.kernel.k16.lerp a b t
      ⦃ r => r.val = a.val + roundHalfUp (exact 8 ((b.val - a.val) * t.val)) ⦄ :=
  lerp_shape a b t 15 7 rfl rfl rfl _ k16_round_frac_spec

/-- L3 on the code: `kernel::k32::mul_add` is `round((a · b + c · 2^16) / 2^16)`. -/
theorem k32_mul_add_spec (a b c : Std.I32) :
    fulcrum.kernel.k32.mul_add a b c
      ⦃ r => r.val = roundHalfUp (exact 16 (a.val * b.val + c.val * 2 ^ 16)) ⦄ :=
  mul_add_shape a b c 31 15 rfl rfl rfl _ (k32_mul_spec a b)

/-- L3 on the code: `kernel::k32::lerp` is `a + round((b - a) · t / 2^16)`. -/
theorem k32_lerp_spec (a b t : Std.I32) :
    fulcrum.kernel.k32.lerp a b t
      ⦃ r => r.val = a.val + roundHalfUp (exact 16 ((b.val - a.val) * t.val)) ⦄ :=
  lerp_shape a b t 31 15 rfl rfl rfl _ k32_round_frac_spec

/-- L3 on the code: `kernel::k64::mul_add` is `round((a · b + c · 2^32) / 2^32)`. -/
theorem k64_mul_add_spec (a b c : Std.I64) :
    fulcrum.kernel.k64.mul_add a b c
      ⦃ r => r.val = roundHalfUp (exact 32 (a.val * b.val + c.val * 2 ^ 32)) ⦄ :=
  mul_add_shape a b c 63 31 rfl rfl rfl _ (k64_mul_spec a b)

/-- L3 on the code: `kernel::k64::lerp` is `a + round((b - a) · t / 2^32)`. -/
theorem k64_lerp_spec (a b t : Std.I64) :
    fulcrum.kernel.k64.lerp a b t
      ⦃ r => r.val = a.val + roundHalfUp (exact 32 ((b.val - a.val) * t.val)) ⦄ :=
  lerp_shape a b t 63 31 rfl rfl rfl _ fun p _ => k64_round_frac_spec p

end Fulcrum

end
