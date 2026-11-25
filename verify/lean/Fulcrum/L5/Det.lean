module

public import Fulcrum.L3.Mul

/-!
# L5: `kernel::kN::det`

`det(a, b, c, d)` is `round((a · d - b · c) / 2^F)`, the 2×2 determinant
rounded once, for every width, as Aeneas extracts it: it never fails. Every
width goes through `det_shape`, with the widths of `mul_shape`.
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace Fulcrum

/-- The difference of two products of raw values of `n + 1` bits lies in
`[-(2^(2n+1) - 2^n), 2^(2n+1) - 2^n]`. -/
theorem det_bounds (a b c d : ℤ) (n : ℕ) (la : -2 ^ n ≤ a) (ua : a < 2 ^ n) (lb : -2 ^ n ≤ b)
    (ub : b < 2 ^ n) (lc : -2 ^ n ≤ c) (uc : c < 2 ^ n) (ld : -2 ^ n ≤ d) (ud : d < 2 ^ n) :
    -(2 ^ (n + n + 1) - 2 ^ n) ≤ a * d - b * c ∧ a * d - b * c ≤ 2 ^ (n + n + 1) - 2 ^ n := by
  have e : (2 : ℤ) ^ (n + n + 1) = 2 * (2 ^ n * 2 ^ n) := by rw [pow_succ, pow_add, mul_comm]
  rw [e]
  have p : (0 : ℤ) < 2 ^ n := pow_pos zero_lt_two n
  constructor <;> nlinarith [mul_nonneg (sub_nonneg.2 la) (sub_nonneg.2 ld),
    mul_nonneg (sub_nonneg.2 ua.le) (sub_nonneg.2 ud.le),
    mul_nonneg (sub_nonneg.2 la) (sub_nonneg.2 (Int.le_sub_one_of_lt ud)),
    mul_nonneg (sub_nonneg.2 ld) (sub_nonneg.2 (Int.le_sub_one_of_lt ua)),
    mul_nonneg (sub_nonneg.2 lb) (sub_nonneg.2 lc),
    mul_nonneg (sub_nonneg.2 ub.le) (sub_nonneg.2 uc.le),
    mul_nonneg (sub_nonneg.2 lb) (sub_nonneg.2 (Int.le_sub_one_of_lt uc)),
    mul_nonneg (sub_nonneg.2 lc) (sub_nonneg.2 (Int.le_sub_one_of_lt ub))]

/-- The body of `kernel::kN::det`: both products and their difference fit the
wide type, and so does the difference plus the half, so it is
`round((a · d - b · c) / 2^F)`. -/
theorem det_shape {B W} (a b c d : IScalar B) (n k : ℕ) (hn : k + (k + 1) = n)
    (hB : B.numBits = n + 1) (hW : W.numBits = n + n + 1 + 1)
    (rf : IScalar W → Result (IScalar W))
    (hrf : ∀ p : IScalar W, p.val + 2 ^ k ≤ IScalar.max W →
      rf p ⦃ r => r.val = roundHalfUp (exact (k + 1) p.val) ⦄) :
    (do
        let i ← lift (IScalar.cast W a)
        let i1 ← lift (IScalar.cast W d)
        let i2 ← i * i1
        let i3 ← lift (IScalar.cast W b)
        let i4 ← lift (IScalar.cast W c)
        let i5 ← i3 * i4
        let i6 ← i2 - i5
        rf i6)
      ⦃ r => r.val = roundHalfUp (exact (k + 1) (a.val * d.val - b.val * c.val)) ⦄ := by
  have hk : k < n := hn ▸ Nat.lt_add_of_pos_right (Nat.succ_pos k)
  have hBW : B.numBits ≤ W.numBits := hB ▸ hW ▸ Nat.succ_le_succ (Nat.le_add_right n (n + 1))
  have ca := IScalar.val_mod_pow_greater_numBits W a hBW
  have cb := IScalar.val_mod_pow_greater_numBits W b hBW
  have cc := IScalar.val_mod_pow_greater_numBits W c hBW
  have cd := IScalar.val_mod_pow_greater_numBits W d hBW
  have ⟨la, ua⟩ := val_bounds a hB
  have ⟨lb, ub⟩ := val_bounds b hB
  have ⟨lc, uc⟩ := val_bounds c hB
  have ⟨ld, ud⟩ := val_bounds d hB
  have ⟨lo1, hi1⟩ := prod_bounds _ n k hk (prod_abs_le a d hB)
  have ⟨lo2, hi2⟩ := prod_bounds _ n k hk (prod_abs_le b c hB)
  have p0 : (0 : ℤ) ≤ 2 ^ k := (pow_pos zero_lt_two k).le
  have ⟨f1l, f1u⟩ := in_bounds_of_pow hW lo1 ((le_add_of_nonneg_right p0).trans_lt hi1)
  have ⟨f2l, f2u⟩ := in_bounds_of_pow hW lo2 ((le_add_of_nonneg_right p0).trans_lt hi2)
  have ⟨dl, du⟩ := det_bounds a.val b.val c.val d.val n la ua lb ub lc uc ld ud
  have pk : (2 : ℤ) ^ k < 2 ^ n := pow_lt_pow_right₀ one_lt_two hk
  have dhi : a.val * d.val - b.val * c.val + 2 ^ k < 2 ^ (n + n + 1) := by linarith
  have ⟨fdl, fdu⟩ := in_bounds_of_pow hW (by linarith [pow_pos (zero_lt_two (α := ℤ)) n])
    ((le_add_of_nonneg_right p0).trans_lt dhi)
  rw [lift, bind_ok, lift, bind_ok]
  refine WP.spec_bind (IScalar.mul_spec (ca ▸ cd ▸ f1l) (ca ▸ cd ▸ f1u)) fun p hp => ?_
  rw [lift, bind_ok, lift, bind_ok]
  rw [ca, cd] at hp
  refine WP.spec_bind (IScalar.mul_spec (cb ▸ cc ▸ f2l) (cb ▸ cc ▸ f2u)) fun q hq => ?_
  rw [cb, cc] at hq
  refine WP.spec_bind (IScalar.sub_spec (hp ▸ hq ▸ fdl) (hp ▸ hq ▸ fdu)) fun s hs => ?_
  rw [hp, hq] at hs
  exact hs ▸ hrf s (hs ▸ max_eq_pow_sub_one hW ▸ Int.le_sub_one_of_lt dhi)

/-- L5 on the code: `kernel::k8::det` is `round((a · d - b · c) / 2^4)`. -/
theorem k8_det_spec (a b c d : Std.I8) :
    fulcrum.kernel.k8.det a b c d
      ⦃ r => r.val = roundHalfUp (exact 4 (a.val * d.val - b.val * c.val)) ⦄ :=
  det_shape a b c d 7 3 rfl rfl rfl _ k8_round_frac_spec

/-- L5 on the code: `kernel::k16::det` is `round((a · d - b · c) / 2^8)`. -/
theorem k16_det_spec (a b c d : Std.I16) :
    fulcrum.kernel.k16.det a b c d
      ⦃ r => r.val = roundHalfUp (exact 8 (a.val * d.val - b.val * c.val)) ⦄ :=
  det_shape a b c d 15 7 rfl rfl rfl _ k16_round_frac_spec

/-- L5 on the code: `kernel::k32::det` is `round((a · d - b · c) / 2^16)`. -/
theorem k32_det_spec (a b c d : Std.I32) :
    fulcrum.kernel.k32.det a b c d
      ⦃ r => r.val = roundHalfUp (exact 16 (a.val * d.val - b.val * c.val)) ⦄ :=
  det_shape a b c d 31 15 rfl rfl rfl _ k32_round_frac_spec

/-- L5 on the code: `kernel::k64::det` is `round((a · d - b · c) / 2^32)`. -/
theorem k64_det_spec (a b c d : Std.I64) :
    fulcrum.kernel.k64.det a b c d
      ⦃ r => r.val = roundHalfUp (exact 32 (a.val * d.val - b.val * c.val)) ⦄ :=
  det_shape a b c d 63 31 rfl rfl rfl _ fun p _ => k64_round_frac_spec p

end Fulcrum

end
