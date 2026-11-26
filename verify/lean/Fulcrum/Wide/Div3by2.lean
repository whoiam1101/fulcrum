module

public import Fulcrum.Lemmas.Scalar
public import Fulcrum.Math.DivWide

/-!
# `wide::div_rem_3by2`

On the code extracted by Aeneas. For `2^64 ≤ d` and `u < d`, `div_rem_3by2(u, v, d)` never fails
and returns `⌊N / d⌋` and `N mod d` for `N = u · 2^64 + v` (`div_rem_3by2_spec`).

The loop keeps `q · d₁ + r = u` and `Q ≤ q < 2^64` (`Inv3by2`), and its measure is `q`. A pass
with `r ≥ 2^64` stops (`body_wide_spec`), as does a pass whose test fails (`body_stop_spec`):
then `q = Q` by `test_iff` and `wide_r_le` of `Math/DivWide.lean`. A pass whose test holds
lowers `q` by one (`body_step_spec`).
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace Fulcrum

/-- The invariant of the loop of `div_rem_3by2`, on the values: `q · d₁ + r = u` and
`⌊N / D⌋ ≤ q < 2^64` for `N = u · 2^64 + v`, `D = d₁ · 2^64 + d₀`. -/
def Inv3by2 (u v d1 d0 q r : ℕ) : Prop :=
  q * d1 + r = u ∧ (u * 2 ^ 64 + v) / (d1 * 2 ^ 64 + d0) ≤ q ∧ q < 2 ^ 64

/-- `q = Q` once `q · D ≤ N` under the invariant. -/
theorem inv3by2_eq {u v d1 d0 q r : ℕ} (h : Inv3by2 u v d1 d0 q r) (hD : 0 < d1 * 2 ^ 64 + d0)
    (le : q * (d1 * 2 ^ 64 + d0) ≤ u * 2 ^ 64 + v) : q = (u * 2 ^ 64 + v) / (d1 * 2 ^ 64 + d0) :=
  Nat.le_antisymm ((Nat.le_div_iff_mul_le hD).mpr le) h.2.1

/-- A pass with `r ≥ 2^64` stops, and then `q = Q`. -/
theorem inv3by2_wide_eq {u v d1 d0 q r : ℕ} (h : Inv3by2 u v d1 d0 q r) (hD : 0 < d1 * 2 ^ 64 + d0)
    (hd0 : d0 < 2 ^ 64) (hr : 2 ^ 64 ≤ r) : q = (u * 2 ^ 64 + v) / (d1 * 2 ^ 64 + d0) :=
  inv3by2_eq h hD (wide_r_le q d1 d0 r u v h.1 h.2.2 hd0 hr)

/-- `(r << 64) | v` on `u128` is `(r mod 2^64) · 2^64 + v`. -/
theorem shl_or_val (r : Std.U128) (v : Std.U64) :
    (r <<< 64#i32) ⦃ i2 => (i2 ||| UScalar.cast .U128 v).val = r.val % 2 ^ 64 * 2 ^ 64 + v.val ⦄ := by
  have vl : (UScalar.cast .U128 v).val < 2 ^ 64 := by rw [cast_u128_val]; exact v.bv.isLt
  refine WP.spec_mono (UScalar.ShiftLeft_IScalar_spec r 64#i32 _ (by decide) (by decide) rfl)
    fun i2 ⟨h2, _⟩ => ?_
  have e : i2.val = r.val % 2 ^ 64 * 2 ^ 64 := by
    rw [h2, show (64#i32).toNat = 64 from rfl, Nat.shiftLeft_eq, UScalar.size_def,
      show UScalarTy.U128.numBits = 64 + 64 from rfl, pow_add, Nat.mul_mod_mul_right]
  rw [UScalar.val_or, e, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt vl, cast_u128_val]

/-- The product `q · d₀` of two digits fits `u128`. -/
theorem digit_mul_le (q d0 : ℕ) (hq : q < 2 ^ 64) (hd0 : d0 < 2 ^ 64) : q * d0 ≤ UScalar.max .U128 := by
  rw [U128_max_val]
  have := Nat.mul_lt_mul'' hq hd0
  omega

/-- A pass whose test fails stops at `Q`. -/
theorem body_stop_spec (v : Std.U64) (d1 d0 q r i1 i4 : Std.U128) (u : ℕ)
    (hD : 0 < d1.val * 2 ^ 64 + d0.val) (h : Inv3by2 u v.val d1.val d0.val q.val r.val)
    (h1 : i1.val = q.val * d0.val) (h4 : i4.val = r.val * 2 ^ 64 + v.val) (ht : ¬ i1 > i4) :
    q.val = (u * 2 ^ 64 + v.val) / (d1.val * 2 ^ 64 + d0.val) := by
  have le : ¬ r.val * 2 ^ 64 + v.val < q.val * d0.val := by
    rw [← h1, ← h4]; exact ht
  exact inv3by2_eq h hD (Nat.not_lt.mp (mt (test_iff _ _ _ _ _ _ h.1).mpr le))

/-- A pass whose test holds steps to `q - 1`, `r + d₁` under the invariant. -/
theorem body_step_spec (v : Std.U64) (d1 d0 q r i1 i4 : Std.U128) (u : ℕ) (hd1 : d1.val < 2 ^ 64)
    (hD : 0 < d1.val * 2 ^ 64 + d0.val) (h : Inv3by2 u v.val d1.val d0.val q.val r.val)
    (hr : r.val < 2 ^ 64) (h1 : i1.val = q.val * d0.val) (h4 : i4.val = r.val * 2 ^ 64 + v.val)
    (ht : i1 > i4) :
    (do
      let q1 ← q - 1#u128
      let r1 ← r + d1
      ok (ControlFlow.cont (q1, r1) : ControlFlow (Std.U128 × Std.U128) Std.U128)) ⦃ c => match c with
      | .done _ => False
      | .cont p => Inv3by2 u v.val d1.val d0.val p.1.val p.2.val ∧ p.1.val < q.val ⦄ := by
  have lt : (u * 2 ^ 64 + v.val) / (d1.val * 2 ^ 64 + d0.val) < q.val := by
    rw [Nat.div_lt_iff_lt_mul hD]
    refine (test_iff _ _ _ _ _ _ h.1).mp ?_
    rw [← h1, ← h4]; exact ht
  have qp : 1 ≤ q.val := Nat.one_le_of_lt lt
  refine WP.spec_bind (UScalar.sub_spec (x := q) (y := 1#u128) (by rw [lit_val]; exact qp))
    fun q1 ⟨hq1, _⟩ => ?_
  refine WP.spec_bind (UScalar.add_spec (x := r) (y := d1) (by rw [U128_max_val]; omega)) fun r1 hr1 => ?_
  rw [WP.spec_ok, lit_val] at *
  dsimp only
  have e := h.1
  have hq := h.2.2
  refine ⟨⟨?_, hq1 ▸ Nat.le_sub_one_of_lt lt, by omega⟩, by omega⟩
  rw [hq1, hr1, Nat.sub_mul, Nat.one_mul, ← e]
  have : d1.val ≤ q.val * d1.val := Nat.le_mul_of_pos_left _ qp
  omega

/-- One pass of the loop under the invariant: it stops at `Q`, or keeps the invariant and
lowers `q`. -/
theorem body3by2_spec (v : Std.U64) (d1 d0 q r : Std.U128) (u : ℕ) (hd1 : d1.val < 2 ^ 64)
    (hd0 : d0.val < 2 ^ 64) (hD : 0 < d1.val * 2 ^ 64 + d0.val)
    (h : Inv3by2 u v.val d1.val d0.val q.val r.val) :
    fulcrum.wide.div_rem_3by2_loop.body v d1 d0 q r ⦃ c => match c with
      | .done y => y.val = (u * 2 ^ 64 + v.val) / (d1.val * 2 ^ 64 + d0.val)
      | .cont p => Inv3by2 u v.val d1.val d0.val p.1.val p.2.val ∧ p.1.val < q.val ⦄ := by
  unfold fulcrum.wide.div_rem_3by2_loop.body
  refine WP.spec_bind (shr_i32_spec r 64#i32 64 rfl (by decide)) fun i hi => ?_
  by_cases hr : r.val < 2 ^ 64
  · have i0 : i = 0#u128 := UScalar.eq_of_val_eq (by rw [hi, Nat.div_eq_of_lt hr]; rfl)
    rw [ite_eq_left i0]
    refine WP.spec_bind (UScalar.mul_spec (digit_mul_le _ _ h.2.2 hd0)) fun i1 h1 => ?_
    refine WP.spec_bind (shl_or_val r v) fun i2 h4 => ?_
    rw [Nat.mod_eq_of_lt hr] at h4
    rw [lift, bind_ok, lift, bind_ok]
    generalize i2 ||| UScalar.cast .U128 v = i4 at h4 ⊢
    by_cases ht : i1 > i4
    · rw [ite_eq_left ht]
      refine WP.spec_mono (body_step_spec v d1 d0 q r i1 i4 u hd1 hD h hr h1 h4 ht) fun c hc => ?_
      cases c <;> dsimp only at hc ⊢
      exact hc
    · rw [ite_eq_right ht, WP.spec_ok]
      exact body_stop_spec v d1 d0 q r i1 i4 u hD h h1 h4 ht
  · have i0 : ¬ i = 0#u128 := fun e => hr (by
      have := congrArg UScalar.val e
      rw [hi] at this
      exact (Nat.div_eq_zero_iff_lt (by positivity)).mp this)
    rw [ite_eq_right i0, WP.spec_ok]
    exact inv3by2_wide_eq h hD hd0 (Nat.le_of_not_lt hr)

/-- The loop of `div_rem_3by2` from the invariant returns `Q`. -/
theorem loop3by2_spec (v : Std.U64) (d1 d0 q r : Std.U128) (u : ℕ) (hd1 : d1.val < 2 ^ 64)
    (hd0 : d0.val < 2 ^ 64) (hD : 0 < d1.val * 2 ^ 64 + d0.val)
    (h : Inv3by2 u v.val d1.val d0.val q.val r.val) :
    fulcrum.wide.div_rem_3by2_loop v d1 d0 q r ⦃ y =>
      y.val = (u * 2 ^ 64 + v.val) / (d1.val * 2 ^ 64 + d0.val) ⦄ := by
  unfold fulcrum.wide.div_rem_3by2_loop
  refine loop.spec_decr_nat (fun p : Std.U128 × Std.U128 => p.1.val)
    (fun p => Inv3by2 u v.val d1.val d0.val p.1.val p.2.val)
    _ _ (q, r) ?_ h
  rintro ⟨q1, r1⟩ hp
  refine WP.spec_mono (body3by2_spec v d1 d0 q1 r1 u hd1 hd0 hD hp) fun c hc => ?_
  cases c <;> dsimp only at hc ⊢ <;> exact hc

/-- The estimate of `div_rem_3by2`, `u / d₁` capped at `u64::MAX`, is `knuthEst`. -/
theorem est3by2_spec (u d1 i1 : Std.U128) (hi : i1.val = u.val / 2 ^ 64) (hd1 : 0 < d1.val) :
    (if i1 >= d1 then ok (UScalar.cast .U128 core.num.U64.MAX) else u / d1) ⦃ q =>
      q.val = knuthEst u.val d1.val ⦄ := by
  unfold knuthEst
  by_cases c : d1.val ≤ u.val / 2 ^ 64
  · rw [ite_eq_left (show i1 ≥ d1 from show d1.val ≤ i1.val by rw [hi]; exact c), ite_eq_left c, WP.spec_ok, cast_u128_val]
    rfl
  · rw [ite_eq_right (show ¬ i1 ≥ d1 from show ¬ d1.val ≤ i1.val by rw [hi]; exact c), ite_eq_right c]
    obtain ⟨z, hz, hzv⟩ := UScalar.div_spec u (Nat.pos_iff_ne_zero.mp hd1)
    rw [hz, WP.spec_ok]
    exact hzv

/-- `d >> 64` and `d mod 2^64` are the digits of `d`. -/
theorem digits_val (d : Std.U128) :
    d.val / 2 ^ 64 * 2 ^ 64 + (UScalar.cast .U128 (UScalar.cast .U64 d)).val = d.val := by
  rw [cast_u128_val, cast_u64_val]
  exact Nat.div_add_mod' d.val (2 ^ 64)

/-- The remainder of `div_rem_3by2`: `((u << 64) | v) - q · d`, wrapped, is `N mod d` for
`q = ⌊N / d⌋`. -/
theorem rem3by2_spec (u q d : Std.U128) (v : Std.U64) (hd : 0 < d.val)
    (hq : q.val = (u.val * 2 ^ 64 + v.val) / d.val) :
    (do
      let i3 ← u <<< 64#i32
      let i4 ← lift (UScalar.cast .U128 v)
      let i5 ← lift (i3 ||| i4)
      let i6 ← lift (core.num.U128.wrapping_mul q d)
      let rem ← lift (core.num.U128.wrapping_sub i5 i6)
      ok (q, rem)) ⦃ p => p.1.val = (u.val * 2 ^ 64 + v.val) / d.val ∧
        p.2.val = (u.val * 2 ^ 64 + v.val) % d.val ⦄ := by
  refine WP.spec_bind (shl_or_val u v) fun i3 h5 => ?_
  rw [lift, bind_ok, lift, bind_ok, lift, bind_ok, lift, bind_ok, WP.spec_ok]
  refine ⟨hq, ?_⟩
  rw [core.num.U128.wrapping_sub_val_eq, core.num.U128.wrapping_mul_val_eq, h5, hq, UScalar.size_def,
    show UScalarTy.U128.numBits = 128 from rfl]
  refine wrap_rem u.val v.val _ _ (Nat.div_add_mod' _ _).symm ?_
  exact (Nat.mod_lt _ hd).trans d.bv.isLt

/-- On the code: for `2^64 ≤ d` and `u < d`, `wide::div_rem_3by2(u, v, d)` never fails and
returns `⌊N / d⌋` and `N mod d` for `N = u · 2^64 + v`. -/
theorem div_rem_3by2_spec (u : Std.U128) (v : Std.U64) (d : Std.U128) (hd : 2 ^ 64 ≤ d.val)
    (hu : u.val < d.val) :
    fulcrum.wide.div_rem_3by2 u v d ⦃ p => p.1.val = (u.val * 2 ^ 64 + v.val) / d.val ∧
      p.2.val = (u.val * 2 ^ 64 + v.val) % d.val ⦄ := by
  have ul : u.val < 2 ^ 128 := u.bv.isLt
  have dl : d.val < 2 ^ 128 := d.bv.isLt
  have vl : v.val < 2 ^ 64 := v.bv.isLt
  unfold fulcrum.wide.div_rem_3by2
  refine WP.spec_bind (shr_i32_spec d 64#i32 64 rfl (by decide)) fun d1 hd1 => ?_
  rw [lift, bind_ok, lift, bind_ok]
  have dd := digits_val d
  have d0l : (UScalar.cast .U128 (UScalar.cast .U64 d)).val < 2 ^ 64 := by
    rw [cast_u128_val]; exact (UScalar.cast .U64 d).bv.isLt
  rw [← hd1] at dd
  generalize UScalar.cast .U128 (UScalar.cast .U64 d) = d0 at dd d0l ⊢
  have d1p : 0 < d1.val := by rw [hd1]; exact Nat.div_pos hd (Nat.two_pow_pos 64)
  have d1l : d1.val < 2 ^ 64 := by rw [hd1, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos 64)]; exact dl
  refine WP.spec_bind (shr_i32_spec u 64#i32 64 rfl (by decide)) fun i1 hi1 => ?_
  refine WP.spec_bind (est3by2_spec u d1 i1 hi1 d1p) fun q hq => ?_
  have qm : q.val * d1.val ≤ u.val := hq ▸ est_mul_le u.val d1.val
  refine WP.spec_bind (UScalar.mul_spec (x := q) (y := d1) (by rw [U128_max_val]; omega)) fun i2 h2 => ?_
  refine WP.spec_bind (UScalar.sub_spec (x := u) (y := i2) (h2 ▸ qm)) fun r ⟨hr, _⟩ => ?_
  have inv : Inv3by2 u.val v.val d1.val d0.val q.val r.val :=
    ⟨by rw [hr, h2]; omega, hq ▸ quot_le_est _ _ _ _ d1p (dd ▸ hu) vl, hq ▸ est_lt _ _⟩
  refine WP.spec_bind (loop3by2_spec v d1 d0 q r u.val d1l d0l (by omega) inv) fun q1 h1 => ?_
  rw [dd] at h1
  exact rem3by2_spec u q1 d v (by omega) h1

end Fulcrum

end
