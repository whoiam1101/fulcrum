module

public import Fulcrum.L5.Scale
public import Fulcrum.Math.ScaleTo
public import Fulcrum.Wide.Mul
public import Fulcrum.Wide.DivU256

/-!
# L5: `kernel::k64::scale_to`, `kernel::k64::scale_vec`

`scale_to(x, k, s)` for `s > 0`, `x² ≤ s`, `k ≥ 0` and no tie takes `q = ⌊p² / s⌋` and its
remainder `r` for `p = |x| · k` from the exact 256-bit product (`widening_mul_u128`,
`div_rem_u256`), `t = ⌊√q⌋` from the `isqrt` of L3, and rounds up when `q - t² - t > 0`, or
`= 0` with `r > ⌊s / 4⌋` (`up_spec`). The magnitude `t + up` is the `m` of `ScaleRound` and at
most `k` (`magnitude_round`), and the sign of `x` is put back (`sign64_spec`).
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace Fulcrum

/-- The magnitude of `scale_to`: `t = ⌊√Q⌋` for `p² = Q · s + R`, plus one when `Q > t² + t`,
or `Q = t² + t` and `4R > s`, is the `m` of `ScaleRound p s` and at most `k`. -/
theorem magnitude_round (p s k Q R t : ℕ) (up : Bool) (hs : 0 < s) (hP : p * p = Q * s + R)
    (hR : R < s) (ht : t = Nat.sqrt Q) (hup : up = true ↔ (t * t + t < Q ∨ (Q = t * t + t ∧ s < 4 * R)))
    (hpk : p * p ≤ k * k * s) (hnt : ∀ o, Odd o → o * o * s ≠ 4 * p * p) :
    ScaleRound p s (t + up.toNat) ∧ t + up.toNat ≤ k := by
  have t1 : t * t ≤ Q := ht ▸ Nat.sqrt_le Q
  have t2 : Q < (t + 1) * (t + 1) := ht ▸ Nat.lt_succ_sqrt Q
  have key : (4 * p * p ≤ (2 * (t + up.toNat) + 1) * (2 * (t + up.toNat) + 1) * s) ∧
      (t + up.toNat = 0 ∨ (2 * (t + up.toNat) - 1) * (2 * (t + up.toNat) - 1) * s ≤ 4 * p * p) := by
    cases up
    · have h : ¬ (t * t + t < Q ∨ (Q = t * t + t ∧ s < 4 * R)) := fun h => Bool.false_ne_true (hup.mpr h)
      refine ⟨?_, Or.inr (down_hlo p s Q R t hP t1)⟩
      rcases Nat.lt_or_ge Q (t * t + t) with c | c
      · exact down_hup_neg p s Q R t hP hR c
      · exact down_hup_mid p s Q R t hP (by omega) (by omega)
    · have h := hup.mp rfl
      refine ⟨up_hup p s Q R t hP hR t2, Or.inr ?_⟩
      rcases h with c | ⟨c, d⟩
      · exact up_hlo_pos p s Q R t hP c
      · exact up_hlo_mid p s Q R t hP c d
  have mk := round_le p s k _ hs hpk key.2
  exact ⟨scaleRound_of_walk p s k _ hs hpk mk hnt (Or.inr key.1) key.2, mk⟩

/-- The rounding decision of `scale_to`: up when `d > 0`, or `d = 0` and `r > ⌊s / 4⌋`, that is
`4r > s`. -/
theorem up_spec (d : Std.I128) (r s : Std.U128) :
    (if d > 0#i128 then ok true else if d = 0#i128 then do
        let i8 ← s >>> 2#i32
        ok (r > i8)
      else ok false) ⦃ up => (up = true ↔ (0 < d.val ∨ (d.val = 0 ∧ s.val < 4 * r.val))) ⦄ := by
  by_cases hp : d > 0#i128
  · rw [ite_eq_left hp, WP.spec_ok]
    exact ⟨fun _ => Or.inl hp, fun _ => rfl⟩
  have hp' : ¬ 0 < d.val := hp
  rw [ite_eq_right hp]
  by_cases hz : d = 0#i128
  · have hz' : d.val = 0 := by rw [hz]; rfl
    rw [ite_eq_left hz]
    refine WP.spec_bind (shr_i32_spec s 2#i32 2 rfl (by decide)) fun i8 h8 => ?_
    rw [WP.spec_ok, decide_eq_true_iff]
    show i8.val < r.val ↔ _
    rw [h8]
    omega
  · have hz' : d.val ≠ 0 := fun e => hz (IScalar.eq_of_val_eq (by rw [e]; rfl))
    rw [ite_eq_right hz, WP.spec_ok]
    exact ⟨fun e => absurd e Bool.false_ne_true, fun h => by omega⟩

/-- The sign of `x` put on the magnitude `m ≥ 0`. -/
theorem sign64_spec (x m : Std.I64) (hm : 0 ≤ m.val) :
    (if x < 0#i64 then -. m else ok m) ⦃ w => w.val = if x.val < 0 then -m.val else m.val ⦄ := by
  by_cases neg : x < 0#i64
  · have neg' : x.val < 0 := neg
    rw [ite_eq_left neg]
    have hmin : (m : ℤ) ≠ IScalar.min .I64 := by
      rw [min_eq_neg_pow (m := 63) rfl]; omega
    exact WP.spec_mono (HNeg.hNeg.step _ hmin) fun w hw => by rw [hw, ite_eq_left neg']
  · have neg' : ¬ x.val < 0 := neg
    rw [ite_eq_right neg, WP.spec_ok, ite_eq_right neg']

/-- The start of `scale_to`: `q = ⌊p² / s⌋` and `r = p² mod s` for `p = |x| · k`, from the squares
on `u128`, their exact product and the division of `div_rem_u256`. -/
theorem square_div_bind {β} (x k : Std.I64) (s : Std.U128) (hk : 0 ≤ k.val) (hs : 0 < s.val)
    (hx : x.val.natAbs * x.val.natAbs ≤ s.val) (f : Std.U128 → Std.U128 → Result β) (P : β → Prop)
    (hf : ∀ q r : Std.U128,
      q.val = x.val.natAbs * k.val.toNat * (x.val.natAbs * k.val.toNat) / s.val →
      r.val = x.val.natAbs * k.val.toNat * (x.val.natAbs * k.val.toNat) % s.val → f q r ⦃ P ⦄) :
    (do
      let i ← core.num.I64.unsigned_abs x
      let ux ← lift (UScalar.cast .U128 i)
      let i1 ← core.num.I64.unsigned_abs k
      let k1 ← lift (UScalar.cast .U128 i1)
      let i2 ← ux * ux
      let i3 ← k1 * k1
      let (hi, lo) ← fulcrum.wide.widening_mul_u128 i2 i3
      let (q, r) ← fulcrum.wide.div_rem_u256 hi lo s
      f q r) ⦃ P ⦄ := by
  have xa := natAbs_le_pow x 63 rfl
  have kn : k.val.natAbs = k.val.toNat := by omega
  have ka : k.val.toNat ≤ 2 ^ 63 := kn ▸ natAbs_le_pow k 63 rfl
  have sq : ∀ n : ℕ, n ≤ 2 ^ 63 → n * n ≤ UScalar.max .U128 := fun n hn => by
    rw [U128_max_val]
    exact (Nat.mul_le_mul hn hn).trans (by norm_num)
  refine WP.spec_bind (I64_unsigned_abs_spec x) fun i hi => ?_
  rw [lift, bind_ok]
  refine WP.spec_bind (I64_unsigned_abs_spec k) fun i1 hi1 => ?_
  rw [lift, bind_ok]
  rw [kn] at hi1
  have cx : (UScalar.cast .U128 i).val = x.val.natAbs := by rw [cast_u128_val, hi]
  have ck : (UScalar.cast .U128 i1).val = k.val.toNat := by rw [cast_u128_val, hi1]
  refine WP.spec_bind (UScalar.mul_spec (by rw [cx]; exact sq _ xa)) fun i2 h2 => ?_
  refine WP.spec_bind (UScalar.mul_spec (by rw [ck]; exact sq _ ka)) fun i3 h3 => ?_
  rw [cx] at h2
  rw [ck] at h3
  refine WP.spec_bind (widening_mul_u128_spec i2 i3) fun w ⟨wh, wl⟩ => ?_
  obtain ⟨hi', lo⟩ := w
  simp only at wh wl ⊢
  have e : x.val.natAbs * k.val.toNat * (x.val.natAbs * k.val.toNat) = i2.val * i3.val := by
    rw [h2, h3]; ring
  have hlt : hi'.val < s.val := by
    rw [wh, Nat.div_lt_iff_lt_mul (by positivity)]
    calc i2.val * i3.val ≤ s.val * i3.val := Nat.mul_le_mul_right _ (h2 ▸ hx)
      _ < s.val * 2 ^ 128 := Nat.mul_lt_mul_of_pos_left
          (h3 ▸ (Nat.mul_le_mul ka ka).trans_lt (by norm_num)) hs
  refine WP.spec_bind (div_rem_u256_spec hi' lo s hlt) fun v ⟨vq, vr⟩ => ?_
  obtain ⟨q, r⟩ := v
  simp only at vq vr ⊢
  rw [wh, wl, Nat.div_add_mod', ← e] at vq vr
  exact hf q r vq vr

/-- L5 on the code: `kernel::k64::scale_to(x, k, s)` for `s > 0`, `x² ≤ s`, `k ≥ 0` and no tie
never fails and is the magnitude `m ≤ k` of `ScaleRound (|x| · k) s m` with the sign of `x`. -/
theorem k64_scale_to_spec (x k : Std.I64) (s : Std.U128) (hk : 0 ≤ k.val) (hs : 0 < s.val)
    (hx : x.val.natAbs * x.val.natAbs ≤ s.val)
    (hnt : ∀ o, Odd o → o * o * s.val ≠ 4 * (x.val.natAbs * k.val.toNat) * (x.val.natAbs * k.val.toNat)) :
    fulcrum.kernel.k64.scale_to x k s ⦃ w => ScaleOut x.val k.val.toNat s.val w.val ⦄ := by
  unfold fulcrum.kernel.k64.scale_to
  refine square_div_bind x k s hk hs hx _ _ fun q r hq hr => ?_
  have ka : k.val.toNat < 2 ^ 63 := by have := (val_bounds k (n := 63) rfl).2; omega
  have hpk : x.val.natAbs * k.val.toNat * (x.val.natAbs * k.val.toNat) ≤
      k.val.toNat * k.val.toNat * s.val := by
    calc x.val.natAbs * k.val.toNat * (x.val.natAbs * k.val.toNat)
        = x.val.natAbs * x.val.natAbs * (k.val.toNat * k.val.toNat) := by ring
      _ ≤ s.val * (k.val.toNat * k.val.toNat) := Nat.mul_le_mul_right _ hx
      _ = k.val.toNat * k.val.toNat * s.val := Nat.mul_comm _ _
  generalize hp : x.val.natAbs * k.val.toNat = p at hq hr hnt hpk
  generalize k.val.toNat = K at ka hpk hp ⊢
  have qk : q.val ≤ K * K := by rw [hq]; exact Nat.div_le_of_le_mul (Nat.mul_comm s.val _ ▸ hpk)
  have kk : K * K < 2 ^ 126 := (Nat.mul_lt_mul'' ka ka).trans_le (by norm_num)
  refine WP.spec_bind (k64_isqrt_spec q (by omega)) fun t ht => ?_
  rw [lift, bind_ok]
  have t1 : t.val * t.val ≤ q.val := ht ▸ Nat.sqrt_le _
  have tk : t.val ≤ K := by
    rw [ht, ← Nat.sqrt_eq K]; exact Nat.sqrt_le_sqrt qk
  have c4 : (UScalar.hcast .I128 q).val = q.val := hcast_small q 127 rfl (by omega)
  refine WP.spec_bind (UScalar.mul_spec (x := t) (y := t) (by rw [U128_max_val]; omega)) fun i5 h5 => ?_
  refine WP.spec_bind (UScalar.add_spec (x := i5) (y := t) (by rw [U128_max_val]; omega)) fun i6 h6 => ?_
  rw [lift, bind_ok]
  have c7 : (UScalar.hcast .I128 i6).val = i6.val := hcast_small i6 127 rfl (by omega)
  refine WP.spec_bind (IScalar.sub_spec (x := UScalar.hcast .I128 q) (y := UScalar.hcast .I128 i6)
    (by rw [c4, c7, min_eq_neg_pow (m := 127) rfl]; omega)
    (by rw [c4, c7, max_eq_pow_sub_one (m := 127) rfl]; omega)) fun d hd => ?_
  rw [c4, c7, h6, h5] at hd
  refine WP.spec_bind (up_spec d r s) fun up hup => ?_
  rw [lift, bind_ok]
  have cb := UScalar.cast_fromBool_val_eq .U128 up
  have ub : up.toNat ≤ 1 := by cases up <;> decide
  refine WP.spec_bind (UScalar.add_spec (x := t) (y := UScalar.cast_fromBool .U128 up)
    (by rw [cb, U128_max_val]; omega)) fun i9 h9 => ?_
  rw [cb] at h9
  rw [lift, bind_ok]
  have hup' : up = true ↔ (t.val * t.val + t.val < q.val ∨
      (q.val = t.val * t.val + t.val ∧ s.val < 4 * r.val)) := by
    rw [hup, hd]; omega
  obtain ⟨sr, mk⟩ := magnitude_round p s.val K q.val r.val t.val up hs
    (by rw [hq, hr, Nat.mul_comm (p * p / s.val)]; exact (Nat.div_add_mod _ _).symm)
    (hr ▸ Nat.mod_lt _ hs) ht hup' hpk hnt
  have cm : (UScalar.hcast .I64 i9).val = i9.val := hcast_small i9 63 rfl (by omega)
  refine WP.spec_mono (sign64_spec x _ (by rw [cm]; positivity)) fun w hw => ?_
  exact ⟨t.val + up.toNat, by rw [hp]; exact sr, mk, by rw [hw, cm, h9]⟩

/-- The hypotheses of `scale_to` on the first component `a` of a vector with squared length
`S = a² + b² + c² > 0`: `a² ≤ S` and no tie. -/
theorem first_ok (a b c : ℤ) (k : ℕ)
    (hs : 0 < a.natAbs * a.natAbs + b.natAbs * b.natAbs + c.natAbs * c.natAbs) :
    a.natAbs * a.natAbs ≤ a.natAbs * a.natAbs + b.natAbs * b.natAbs + c.natAbs * c.natAbs ∧
      ∀ o, Odd o → o * o * (a.natAbs * a.natAbs + b.natAbs * b.natAbs + c.natAbs * c.natAbs) ≠
        4 * (a.natAbs * k) * (a.natAbs * k) :=
  ⟨by omega, fun o ho => no_tie o k ho _ _ _ hs⟩

/-- One component of `k64::scale_vec` is `scaled`. -/
theorem k64_component_spec (x k : Std.I64) (s : Std.U128) (S : ℕ) (hk : 0 ≤ k.val) (hS : s.val = S)
    (h0 : 0 < S) (h : x.val.natAbs * x.val.natAbs ≤ S ∧
      ∀ o, Odd o → o * o * S ≠ 4 * (x.val.natAbs * k.val.toNat) * (x.val.natAbs * k.val.toNat)) :
    fulcrum.kernel.k64.scale_to x k s ⦃ w => w.val = scaled x.val k.val.toNat S ⦄ := by
  subst hS
  exact WP.spec_mono (k64_scale_to_spec x k s hk h0 h.1 h.2) fun w hw =>
    scaleOut_scaled _ _ _ _ h0 hw

/-- L5 on the code: `kernel::k64::scale_vec` scales `(a, b, c)` to the raw length
`k ≥ 0`: every component is `round(|x| · k / √(a² + b² + c²))` with the sign of `x`. -/
theorem k64_scale_vec_spec (a b c k : Std.I64) (hk : 0 ≤ k.val) :
    fulcrum.kernel.k64.scale_vec a b c k ⦃ r => ∀ j < 3, (r.val[j]!).val =
      scaled ([a.val, b.val, c.val][j]!) k.val.toNat
        (a.val.natAbs * a.val.natAbs + b.val.natAbs * b.val.natAbs + c.val.natAbs * c.val.natAbs) ⦄ := by
  unfold fulcrum.kernel.k64.scale_vec
  set S := a.val.natAbs * a.val.natAbs + b.val.natAbs * b.val.natAbs + c.val.natAbs * c.val.natAbs
    with hS
  have Sz : (S : ℤ) = a.val ^ 2 + b.val ^ 2 + c.val ^ 2 := by
    rw [hS]; push_cast
    rw [abs_mul_abs_self, abs_mul_abs_self, abs_mul_abs_self]; ring
  refine WP.spec_bind (k64_norm_sq_spec a b c) fun s hs => ?_
  have sv : s.val = S := by exact_mod_cast hs.trans Sz.symm
  by_cases z : s = 0#u128
  · have z' : S = 0 := by rw [← sv]; exact congrArg UScalar.val z
    have a0 : a.val = 0 := by have : a.val.natAbs * a.val.natAbs = 0 := by omega
                              simpa using this
    have b0 : b.val = 0 := by have : b.val.natAbs * b.val.natAbs = 0 := by omega
                              simpa using this
    have c0 : c.val = 0 := by have : c.val.natAbs * c.val.natAbs = 0 := by omega
                              simpa using this
    rw [ite_eq_left z, WP.spec_ok]
    intro j hj
    have : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases this with rfl | rfl | rfl <;> simp [Array.make, a0, b0, c0, scaled_zero]
  have S0 : 0 < S := by
    have : s.val ≠ 0 := fun e => z (UScalar.eq_of_val_eq e)
    omega
  rw [ite_eq_right z]
  have oa := first_ok a.val b.val c.val k.val.toNat S0
  have ob := first_ok b.val a.val c.val k.val.toNat (by omega)
  have oc := first_ok c.val a.val b.val k.val.toNat (by omega)
  rw [show b.val.natAbs * b.val.natAbs + a.val.natAbs * a.val.natAbs + c.val.natAbs * c.val.natAbs = S
    by rw [hS]; ring] at ob
  rw [show c.val.natAbs * c.val.natAbs + a.val.natAbs * a.val.natAbs + b.val.natAbs * b.val.natAbs = S
    by rw [hS]; ring] at oc
  refine WP.spec_bind (k64_component_spec a k s S hk sv S0 oa) fun x0 h0 => ?_
  refine WP.spec_bind (k64_component_spec b k s S hk sv S0 ob) fun x1 h1 => ?_
  refine WP.spec_bind (k64_component_spec c k s S hk sv S0 oc) fun x2 h2 => ?_
  rw [WP.spec_ok]
  intro j hj
  have : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases this with rfl | rfl | rfl
  · rw [Array.make_val]; simp only [List.getElem!_cons_zero]; exact h0
  · rw [Array.make_val]; simp only [List.getElem!_cons_succ, List.getElem!_cons_zero]; exact h1
  · rw [Array.make_val]; simp only [List.getElem!_cons_succ, List.getElem!_cons_zero]; exact h2

end Fulcrum

end
