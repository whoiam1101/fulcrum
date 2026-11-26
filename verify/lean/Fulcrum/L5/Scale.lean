module

public import Fulcrum.Kernel.Funs
public import Fulcrum.Math.Scale
import Fulcrum.L3.Sqrt.K32
import Fulcrum.L5.Length
import Fulcrum.Lemmas.List
import Fulcrum.Lemmas.Scalar

/-!
# L5: `kernel::kN::scale_vec`

`scale_vec(a, b, c, k)` scales the raw vector `(a, b, c)` to the raw length
`k ≥ 0`: every component is `round(x · k / √s)` with the sign of `x`, for
`s = a² + b² + c² > 0`, and the zero vector stays zero. For `k8`..`k32` it runs
`scale_narrow`: from any estimate below `2^64`, clamped to `k`, the walks up and
down stop at the `m` of `ScaleRound` (`Math/Scale.lean`), with no tie on the way
(`no_tie`), so the estimate only decides the number of steps.
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace Fulcrum

/-- `o² · s` of `scale_narrow` for `o < 2^32` and `s ≤ 3 · 2^62`: the square on
`u64`, both factors cast to `u128`, the product on `u128`. -/
theorem sq_s_bind {β} (o1 o2 s : Std.U64) (o : ℕ) (h1 : o1.val = o) (h2 : o2.val = o)
    (ho : o < 2 ^ 32) (hs : s.val ≤ 3 * 2 ^ 62) (f : Std.U128 → Result β) (P : β → Prop)
    (hf : ∀ r : Std.U128, r.val = o * o * s.val → f r ⦃ x => P x ⦄) :
    (do
        let i3 ← o1 * o2
        let i4 ← lift (UScalar.cast .U128 i3)
        let i5 ← lift (UScalar.cast .U128 s)
        let i6 ← i4 * i5
        f i6) ⦃ x => P x ⦄ := by
  have oo : o * o < 2 ^ 64 := by
    have := Nat.mul_lt_mul'' ho ho; rwa [← pow_add] at this
  refine WP.spec_bind (UScalar.mul_spec (by rw [h1, h2, U64_max_val]; omega)) fun i3 hi3 => ?_
  rw [lift, bind_ok, lift, bind_ok]
  have c3 := UScalar.cast_val_mod_pow_greater_numBits_eq .U128 i3 (by decide)
  have cs := UScalar.cast_val_mod_pow_greater_numBits_eq .U128 s (by decide)
  have big : o * o * s.val < 2 ^ 128 - 1 := by
    have := Nat.mul_le_mul (show o * o ≤ 2 ^ 64 - 1 by omega) hs
    have : (2 ^ 64 - 1) * (3 * 2 ^ 62) < 2 ^ 128 - 1 := by norm_num
    omega
  refine WP.spec_bind (UScalar.mul_spec (by rw [c3, cs, hi3, h1, h2, U128_max_val]; omega))
    fun i6 hi6 => hf i6 (by rw [hi6, c3, cs, hi3, h1, h2])

/-- The walk up of `scale_narrow`: from `1 ≤ m ≤ k` with `(2m - 1)² s < P`, step
up while `m < k` and `(2m + 1)² s < P`. -/
theorem up_loop_spec (k s m : Std.U64) (four : Std.U128) (P : ℕ) (hfour : four.val = P)
    (hk : k.val < 2 ^ 31) (hs : s.val ≤ 3 * 2 ^ 62) (hm : m.val ≤ k.val) (hm1 : 1 ≤ m.val)
    (hlo : (2 * m.val - 1) * (2 * m.val - 1) * s.val < P) :
    fulcrum.kernel.scale_narrow_loop0_loop0 k s four m ⦃ r =>
      r.val ≤ k.val ∧ 1 ≤ r.val ∧ (2 * r.val - 1) * (2 * r.val - 1) * s.val < P ∧
        (r.val = k.val ∨ P ≤ (2 * r.val + 1) * (2 * r.val + 1) * s.val) ⦄ := by
  unfold fulcrum.kernel.scale_narrow_loop0_loop0
  refine loop.spec_decr_nat (fun y => k.val - y.val)
    (fun y => y.val ≤ k.val ∧ 1 ≤ y.val ∧ (2 * y.val - 1) * (2 * y.val - 1) * s.val < P) _ _ _
    ?_ ⟨hm, hm1, hlo⟩
  intro y ⟨yk, y1, ylo⟩
  unfold fulcrum.kernel.scale_narrow_loop0_loop0.body
  by_cases lt : y < k
  · have lt' : y.val < k.val := lt
    rw [ite_eq_left lt]
    refine WP.spec_bind (UScalar.mul_spec (by rw [lit_val, U64_max_val]; omega)) fun i hi => ?_
    rw [lit_val] at hi
    refine WP.spec_bind (UScalar.add_spec (by rw [hi, lit_val, U64_max_val]; omega)) fun i1 hi1 => ?_
    refine WP.spec_bind (UScalar.add_spec (by rw [hi, lit_val, U64_max_val]; omega)) fun i2 hi2 => ?_
    rw [lit_val, hi] at hi1 hi2
    refine sq_s_bind i1 i2 s (2 * y.val + 1) hi1 hi2 (by omega) hs _ _ fun r hr => ?_
    by_cases c : r < four
    · have c' : (2 * y.val + 1) * (2 * y.val + 1) * s.val < P := by
        have : r.val < four.val := c; rwa [hr, hfour] at this
      rw [ite_eq_left c]
      refine WP.spec_bind (UScalar.add_spec (by rw [lit_val, U64_max_val]; omega)) fun y1 hy1 => ?_
      rw [lit_val] at hy1
      rw [WP.spec_ok]
      have e : 2 * y1.val - 1 = 2 * y.val + 1 := by omega
      refine ⟨⟨by omega, by omega, ?_⟩, by omega⟩
      rw [e]; exact c'
    · have c' : P ≤ (2 * y.val + 1) * (2 * y.val + 1) * s.val := by
        have : ¬ r.val < four.val := c; rw [hr, hfour] at this; omega
      rw [ite_eq_right c, WP.spec_ok]
      exact ⟨yk, y1, ylo, Or.inr c'⟩
  · have : y.val = k.val := by have : ¬ y.val < k.val := lt; omega
    rw [ite_eq_right lt, WP.spec_ok]
    exact ⟨yk, y1, ylo, Or.inl this⟩

/-- The walk down of `scale_narrow`, for either of its two copies `f`: from
`m ≤ k` with `P < (2m + 1)² s`, step down while `m > 0` and `(2m - 1)² s > P`. -/
theorem down_loop_spec (f : Std.U64 → Result (ControlFlow Std.U64 Std.U64)) (k s m : Std.U64)
    (four : Std.U128) (P : ℕ)
    (hf : ∀ m : Std.U64, f m = (if m > 0#u64 then do
        let i ← 2#u64 * m
        let i1 ← i - 1#u64
        let i2 ← i - 1#u64
        let i3 ← i1 * i2
        let i4 ← lift (UScalar.cast .U128 i3)
        let i5 ← lift (UScalar.cast .U128 s)
        let i6 ← i4 * i5
        if i6 > four then do
          let m1 ← m - 1#u64
          ok (ControlFlow.cont m1)
        else ok (ControlFlow.done m)
      else ok (ControlFlow.done m)))
    (hfour : four.val = P) (hk : k.val < 2 ^ 31) (hs : s.val ≤ 3 * 2 ^ 62) (hm : m.val ≤ k.val)
    (hup : P < (2 * m.val + 1) * (2 * m.val + 1) * s.val) :
    loop f m ⦃ r => r.val ≤ k.val ∧ P < (2 * r.val + 1) * (2 * r.val + 1) * s.val ∧
      (r.val = 0 ∨ (2 * r.val - 1) * (2 * r.val - 1) * s.val ≤ P) ⦄ := by
  refine loop.spec_decr_nat (fun y => y.val)
    (fun y => y.val ≤ k.val ∧ P < (2 * y.val + 1) * (2 * y.val + 1) * s.val) _ _ _
    ?_ ⟨hm, hup⟩
  intro y ⟨yk, yup⟩
  rw [hf]
  by_cases gt : y > 0#u64
  · have gt' : 0 < y.val := gt
    rw [ite_eq_left gt]
    refine WP.spec_bind (UScalar.mul_spec (by rw [lit_val, U64_max_val]; omega)) fun i hi => ?_
    rw [lit_val] at hi
    refine WP.spec_bind (UScalar.sub_spec (by rw [hi, lit_val]; omega)) fun i1 ⟨hi1, _⟩ => ?_
    refine WP.spec_bind (UScalar.sub_spec (by rw [hi, lit_val]; omega)) fun i2 ⟨hi2, _⟩ => ?_
    rw [lit_val, hi] at hi1 hi2
    refine sq_s_bind i1 i2 s (2 * y.val - 1) hi1 hi2 (by omega) hs _ _ fun r hr => ?_
    by_cases c : r > four
    · have c' : P < (2 * y.val - 1) * (2 * y.val - 1) * s.val := by
        have : four.val < r.val := c; rwa [hr, hfour] at this
      rw [ite_eq_left c]
      refine WP.spec_bind (UScalar.sub_spec (by rw [lit_val]; omega)) fun y1 ⟨hy1, _⟩ => ?_
      rw [lit_val] at hy1
      rw [WP.spec_ok]
      have e : 2 * y1.val + 1 = 2 * y.val - 1 := by omega
      refine ⟨⟨by omega, ?_⟩, by omega⟩
      rw [e]; exact c'
    · have c' : (2 * y.val - 1) * (2 * y.val - 1) * s.val ≤ P := by
        have : ¬ four.val < r.val := c; rw [hr, hfour] at this; omega
      rw [ite_eq_right c, WP.spec_ok]
      exact ⟨yk, yup, Or.inr c'⟩
  · have : y.val = 0 := by have : ¬ 0 < y.val := gt; omega
    rw [ite_eq_right gt, WP.spec_ok]
    exact ⟨yk, yup, Or.inl this⟩

/-- A component `w` of `scale_narrow` for the input `x`: the magnitude `m ≤ k` of
`ScaleRound (|x| k) s m` with the sign of `x`. -/
def ScaleOut (x : ℤ) (k s : ℕ) (w : ℤ) : Prop :=
  ∃ m, ScaleRound (x.natAbs * k) s m ∧ m ≤ k ∧ w = if x < 0 then -(m : ℤ) else m

/-- The end of every branch of the loop of `scale_narrow`: the magnitude `m3`
with the sign of `x`, stored at `i`, and the next index. -/
theorem sign_update_spec (x : Std.I64) (m3 : Std.U64) (out : Std.Array Std.I64 3#usize)
    (i : Std.Usize) (hi : i.val < 3) (hm : m3.val < 2 ^ 63) :
    (do
        let w ← if x < 0#i64 then do
            let i20 ← lift (UScalar.hcast .I64 m3)
            -. i20
          else ok (UScalar.hcast .I64 m3)
        let a ← Array.update out i w
        let i' ← i + 1#usize
        ok (ControlFlow.cont (β := Std.Array Std.I64 3#usize) (a, i')))
      ⦃ r => ∃ w : Std.I64, w.val = (if x.val < 0 then -(m3.val : ℤ) else m3.val) ∧
        ∃ i' : Std.Usize, i'.val = i.val + 1 ∧ r = ControlFlow.cont (out.set i w, i') ⦄ := by
  have hc : (UScalar.hcast .I64 m3).val = m3.val := hcast_small m3 63 rfl hm
  have hl : i.val < out.length := by rw [Array.length, out.property]; exact hi
  have tail : ∀ w : Std.I64, (do
      let a ← Array.update out i w
      let i' ← i + 1#usize
      ok (ControlFlow.cont (β := Std.Array Std.I64 3#usize) (a, i'))) ⦃ r =>
        ∃ i' : Std.Usize, i'.val = i.val + 1 ∧ r = ControlFlow.cont (out.set i w, i') ⦄ := fun w =>
    WP.spec_bind (Array.update_spec out i w hl) fun a ha =>
      WP.spec_bind (UScalar.add_spec (x := i) (y := 1#usize) (by
        have := usize_max_ge; rw [lit_val]; omega)) fun i' hi' => by
        rw [WP.spec_ok]; exact ⟨i', by rw [hi', lit_val], by rw [ha]⟩
  by_cases neg : x < 0#i64
  · have neg' : x.val < 0 := neg
    rw [ite_eq_left neg, lift, bind_ok]
    have hmin : ((UScalar.hcast .I64 m3 : Std.I64) : ℤ) ≠ IScalar.min .I64 := by
      rw [hc, min_eq_neg_pow (m := 63) rfl]; omega
    refine WP.spec_bind (HNeg.hNeg.step _ hmin) fun w hw => ?_
    refine WP.spec_mono (tail w) fun r hr => ⟨w, by rw [hw, hc, ite_eq_left neg'], hr⟩
  · have neg' : ¬ x.val < 0 := neg
    rw [ite_eq_right neg, bind_ok]
    exact WP.spec_mono (tail _) fun r hr => ⟨_, by rw [hc, ite_eq_right neg'], hr⟩

/-- The magnitude of a branch that stops at `m`: the strict sides of
`ScaleRound` from the weak ones of the walks, since there is no tie. -/
theorem scaleRound_of_walk (p s k m : ℕ) (hs : 0 < s) (hpk : p * p ≤ k * k * s) (hmk : m ≤ k)
    (hnt : ∀ o, Odd o → o * o * s ≠ 4 * p * p)
    (hup : m = k ∨ 4 * p * p ≤ (2 * m + 1) * (2 * m + 1) * s)
    (hlo : m = 0 ∨ (2 * m - 1) * (2 * m - 1) * s ≤ 4 * p * p) : ScaleRound p s m := by
  constructor
  · have e4 : 4 * p * p = 4 * (p * p) := by ring
    rcases hup with rfl | hup
    · have : 4 * (m * m * s) < (2 * m + 1) * (2 * m + 1) * s := by
        have : 4 * (m * m) < (2 * m + 1) * (2 * m + 1) := by ring_nf; omega
        exact (Nat.mul_lt_mul_right hs).mpr this |>.trans_eq' (by ring)
      omega
    · exact lt_of_le_of_ne hup (fun e => hnt _ (odd_two_mul_add_one m) e.symm)
  · rcases hlo with h | hlo
    · exact Or.inl h
    · rcases Nat.eq_zero_or_pos m with h | h
      · exact Or.inl h
      · exact Or.inr (lt_of_le_of_ne hlo (hnt _ (by
          rw [Nat.odd_iff]; omega)))

/-- The body of the loop of `scale_narrow` at `i < 3`: the component `x = v[i]`,
`p = |x| · k`, stops at the magnitude of `ScaleRound p s` from any estimate,
and is stored with the sign of `x`. -/
theorem narrow_body_spec (v out : Std.Array Std.I64 3#usize) (k s inv : Std.U64)
    (shift : Std.U32) (i : Std.Usize) (hi : i.val < 3) (hk : k.val < 2 ^ 31) (hs0 : 0 < s.val)
    (hs : s.val ≤ 3 * 2 ^ 62) (hsh1 : 1 ≤ shift.val) (hsh : shift.val ≤ 94)
    (hx : (v.val[i.val]!).val.natAbs ≤ 2 ^ 31)
    (hxs : (v.val[i.val]!).val.natAbs * (v.val[i.val]!).val.natAbs ≤ s.val)
    (hnt : ∀ o, Odd o → o * o * s.val ≠
      4 * ((v.val[i.val]!).val.natAbs * k.val) * ((v.val[i.val]!).val.natAbs * k.val)) :
    fulcrum.kernel.scale_narrow_loop0.body v k s inv shift out i ⦃ r =>
      ∃ w : Std.I64, ScaleOut (v.val[i.val]!).val k.val s.val w.val ∧
        ∃ i' : Std.Usize, i'.val = i.val + 1 ∧ r = ControlFlow.cont (out.set i w, i') ⦄ := by
  unfold fulcrum.kernel.scale_narrow_loop0.body
  rw [ite_eq_left (show i < 3#usize from hi)]
  have hl : i.val < v.length := by rw [Array.length, v.property]; exact hi
  refine WP.spec_bind (Array.index_usize_spec v i hl) fun x hx' => ?_
  have xe : x = v.val[i.val]! := by
    rw [hx', getElem!_pos v.val i.val (show i.val < v.val.length by rw [v.property]; exact hi)]
  subst xe
  set X := v.val[i.val]!
  set P := X.val.natAbs * k.val with hP
  refine WP.spec_bind (I64_unsigned_abs_spec X) fun ax habsx => ?_
  have hp : P < 2 ^ 62 := by
    have := Nat.mul_lt_mul_of_le_of_lt hx hk (by positivity); rw [hP]; omega
  refine WP.spec_bind (UScalar.mul_spec (by rw [habsx, U64_max_val]; omega)) fun p hp' => ?_
  rw [habsx, ← hP] at hp'
  rw [lift, bind_ok, lift, bind_ok]
  have cp := UScalar.cast_val_mod_pow_greater_numBits_eq .U128 p (by decide)
  have ci := UScalar.cast_val_mod_pow_greater_numBits_eq .U128 inv (by decide)
  have pp : P * P < 2 ^ 124 := by
    have := Nat.mul_lt_mul'' hp hp; rwa [← pow_add] at this
  refine WP.spec_bind (UScalar.mul_spec (by rw [cp, hp', U128_max_val]; (clear * - pp; omega))) fun i4 hi4 => ?_
  refine WP.spec_bind (UScalar.mul_spec (by rw [hi4, cp, hp', lit_val, U128_max_val]; (clear * - pp; omega)))
    fun four hfour => ?_
  rw [hi4, cp, hp', lit_val, ← mul_assoc] at hfour
  rw [bind_ok, bind_ok]
  have pinv : P * inv.val < 2 ^ 126 := by
    have := Nat.mul_lt_mul'' hp inv.hBounds; rwa [← pow_add] at this
  refine WP.spec_bind (UScalar.mul_spec (by rw [cp, ci, hp', U128_max_val]; (clear * - pinv; omega))) fun i7 hi7 => ?_
  rw [cp, ci, hp'] at hi7
  refine WP.spec_bind (UScalar.sub_spec (by rw [lit_val]; (clear * - hsh1; omega))) fun i8 ⟨hi8, _⟩ => ?_
  rw [lit_val] at hi8
  refine WP.spec_bind (UScalar.ShiftLeft_spec 1#u128 i8 _ (by rw [UScalarTy.U128_numBits_eq]; (clear * - hsh1 hsh hi8; omega)) rfl) fun i9 ⟨hi9, _⟩ => ?_
  have i9v : i9.val = 2 ^ i8.val := by
    rw [hi9, lit_val, Nat.shiftLeft_eq, one_mul, UScalar.size_def]
    exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num) (by rw [UScalarTy.U128_numBits_eq]; (clear * - hsh1 hsh hi8; omega)))
  have i9b : i9.val ≤ 2 ^ 93 := i9v ▸ Nat.pow_le_pow_right two_pos (by (clear * - hsh1 hsh hi8; omega))
  refine WP.spec_bind (UScalar.add_spec (by rw [hi7, U128_max_val]; (clear * - pinv hi7 i9v i9b; omega))) fun i10 _ => ?_
  refine WP.spec_bind (UScalar.ShiftRight_spec i10 shift (by rw [UScalarTy.U128_numBits_eq]; (clear * - hsh1 hsh; omega))) fun i11 _ => ?_
  rw [lift, bind_ok]
  set m := UScalar.cast .U64 i11
  refine WP.spec_bind (Pₘ := fun m1 : Std.U64 => m1.val ≤ k.val) ?_ fun m1 hm1 => ?_
  · by_cases g : m > k
    · rw [ite_eq_left g, WP.spec_ok]
    · rw [ite_eq_right g, WP.spec_ok]; exact not_lt.mp g
  have F : 4 * P * P = four.val := by rw [hfour]
  have hpk : P * P ≤ k.val * k.val * s.val := by
    have := Nat.mul_le_mul_right (k.val * k.val) hxs
    rw [hP]; nlinarith only [this]
  have hnt' : ∀ o, Odd o → o * o * s.val ≠ 4 * P * P := hnt
  have fin : ∀ m3 : Std.U64, m3.val ≤ k.val → ScaleRound P s.val m3.val →
      (do
        let w ← if X < 0#i64 then do
            let i20 ← lift (UScalar.hcast .I64 m3)
            -. i20
          else ok (UScalar.hcast .I64 m3)
        let a ← Array.update out i w
        let i' ← i + 1#usize
        ok (ControlFlow.cont (β := Std.Array Std.I64 3#usize) (a, i'))) ⦃ r =>
        ∃ w : Std.I64, ScaleOut X.val k.val s.val w.val ∧
          ∃ i' : Std.Usize, i'.val = i.val + 1 ∧ r = ControlFlow.cont (out.set i w, i') ⦄ :=
    fun m3 hm3 sr => WP.spec_mono (sign_update_spec X m3 out i hi (by (clear * - hk hm3; omega)))
      fun r ⟨w, hw, rest⟩ => ⟨w, ⟨m3.val, sr, hm3, hw⟩, rest⟩
  have walk := scaleRound_of_walk P s.val k.val
  by_cases lt : m1 < k
  · have lt' : m1.val < k.val := lt
    rw [ite_eq_left lt]
    refine WP.spec_bind (UScalar.mul_spec (by rw [lit_val, U64_max_val]; (clear * - hk lt'; omega))) fun j hj => ?_
    rw [lit_val] at hj
    refine WP.spec_bind (UScalar.add_spec (by rw [hj, lit_val, U64_max_val]; (clear * - hk lt'; omega))) fun j1 hj1 => ?_
    refine WP.spec_bind (UScalar.add_spec (by rw [hj, lit_val, U64_max_val]; (clear * - hk lt'; omega))) fun j2 hj2 => ?_
    rw [lit_val, hj] at hj1 hj2
    refine sq_s_bind j1 j2 s (2 * m1.val + 1) hj1 hj2 (by (clear * - hk lt'; omega)) hs _ _ fun t ht => ?_
    by_cases c : t < four
    · have c' : (2 * m1.val + 1) * (2 * m1.val + 1) * s.val < 4 * P * P := by
        have : t.val < four.val := c; rw [ht, ← F] at this; exact this
      rw [ite_eq_left c]
      refine WP.spec_bind (UScalar.add_spec (by rw [lit_val, U64_max_val]; (clear * - hk lt'; omega))) fun m2 hm2 => ?_
      rw [lit_val] at hm2
      refine WP.spec_bind (up_loop_spec k s m2 four (4 * P * P) F.symm hk hs (by (clear * - lt' hm2; omega)) (by (clear * - hj hm2; omega))
        (by rw [hm2, show 2 * (m1.val + 1) - 1 = 2 * m1.val + 1 by (clear * - hj hm2; omega)]; exact c'))
        fun m3 ⟨m3k, m31, m3lo, m3up⟩ => ?_
      exact fin m3 m3k (walk m3.val hs0 hpk m3k hnt' m3up (Or.inr m3lo.le))
    · have c' : 4 * P * P ≤ (2 * m1.val + 1) * (2 * m1.val + 1) * s.val := by
        have : ¬ t.val < four.val := c; rw [ht, ← F] at this; (clear * - this; omega)
      rw [ite_eq_right c]
      by_cases z : m1 > 0#u64
      · have z' : 0 < m1.val := z
        rw [ite_eq_left z]
        refine WP.spec_bind (UScalar.sub_spec (by rw [hj, lit_val]; (clear * - z'; omega))) fun j3 ⟨hj3, _⟩ => ?_
        refine WP.spec_bind (UScalar.sub_spec (by rw [hj, lit_val]; (clear * - z'; omega))) fun j4 ⟨hj4, _⟩ => ?_
        rw [lit_val, hj] at hj3 hj4
        refine sq_s_bind j3 j4 s (2 * m1.val - 1) hj3 hj4 (by (clear * - hk lt' z' hj3; omega)) hs _ _ fun t2 ht2 => ?_
        by_cases c2 : t2 > four
        · have c2' : 4 * P * P < (2 * m1.val - 1) * (2 * m1.val - 1) * s.val := by
            have : four.val < t2.val := c2; rw [ht2, ← F] at this; exact this
          rw [ite_eq_left c2]
          refine WP.spec_bind (UScalar.sub_spec (by rw [lit_val]; (clear * - z'; omega))) fun m2 ⟨hm2, _⟩ => ?_
          rw [lit_val] at hm2
          refine WP.spec_bind (down_loop_spec _ k s m2 four (4 * P * P) (fun _ => rfl) F.symm hk hs
            (by (clear * - lt' z' hm2; omega)) (by rw [hm2, show 2 * (m1.val - 1) + 1 = 2 * m1.val - 1 by (clear * - z' hj3 hm2; omega)]; exact c2'))
            fun m3 ⟨m3k, m3up, m3lo⟩ => ?_
          exact fin m3 m3k (walk m3.val hs0 hpk m3k hnt' (Or.inr m3up.le) m3lo)
        · have c2' : (2 * m1.val - 1) * (2 * m1.val - 1) * s.val ≤ 4 * P * P := by
            have : ¬ four.val < t2.val := c2; rw [ht2, ← F] at this; (clear * - this; omega)
          rw [ite_eq_right c2]
          exact fin m1 hm1 (walk m1.val hs0 hpk hm1 hnt' (Or.inr c') (Or.inr c2'))
      · have z' : m1.val = 0 := by have : ¬ 0 < m1.val := z; (clear * - this; omega)
        rw [ite_eq_right z]
        exact fin m1 hm1 (walk m1.val hs0 hpk hm1 hnt' (Or.inr c') (Or.inl z'))
  · have e : m1.val = k.val := by have : ¬ m1.val < k.val := lt; (clear * - hm1 this; omega)
    rw [ite_eq_right lt]
    by_cases z : m1 > 0#u64
    · have z' : 0 < m1.val := z
      rw [ite_eq_left z]
      refine WP.spec_bind (UScalar.mul_spec (by rw [lit_val, U64_max_val]; (clear * - hk e z'; omega))) fun j hj => ?_
      rw [lit_val] at hj
      refine WP.spec_bind (UScalar.sub_spec (by rw [hj, lit_val]; (clear * - hk e z'; omega))) fun j3 ⟨hj3, _⟩ => ?_
      refine WP.spec_bind (UScalar.sub_spec (by rw [hj, lit_val]; (clear * - hk e z'; omega))) fun j4 ⟨hj4, _⟩ => ?_
      rw [lit_val, hj] at hj3 hj4
      refine sq_s_bind j3 j4 s (2 * m1.val - 1) hj3 hj4 (by (clear * - hk e z' hj3; omega)) hs _ _ fun t2 ht2 => ?_
      by_cases c2 : t2 > four
      · have c2' : 4 * P * P < (2 * m1.val - 1) * (2 * m1.val - 1) * s.val := by
          have : four.val < t2.val := c2; rw [ht2, ← F] at this; exact this
        rw [ite_eq_left c2]
        refine WP.spec_bind (UScalar.sub_spec (by rw [lit_val]; (clear * - hk e z'; omega))) fun m2 ⟨hm2, _⟩ => ?_
        rw [lit_val] at hm2
        refine WP.spec_bind (down_loop_spec _ k s m2 four (4 * P * P) (fun _ => rfl) F.symm hk hs
          (by (clear * - hk e z' hm2; omega)) (by rw [hm2, show 2 * (m1.val - 1) + 1 = 2 * m1.val - 1 by (clear * - hk e z' hj3; omega)]; exact c2'))
          fun m3 ⟨m3k, m3up, m3lo⟩ => ?_
        exact fin m3 m3k (walk m3.val hs0 hpk m3k hnt' (Or.inr m3up.le) m3lo)
      · have c2' : (2 * m1.val - 1) * (2 * m1.val - 1) * s.val ≤ 4 * P * P := by
          have : ¬ four.val < t2.val := c2; rw [ht2, ← F] at this; (clear * - this; omega)
        rw [ite_eq_right c2]
        exact fin m1 hm1 (walk m1.val hs0 hpk hm1 hnt' (Or.inl e) (Or.inr c2'))
    · have z' : m1.val = 0 := by have : ¬ 0 < m1.val := z; (clear * - hk e this; omega)
      rw [ite_eq_right z]
      exact fin m1 hm1 (walk m1.val hs0 hpk hm1 hnt' (Or.inl e) (Or.inl z'))

/-- The hypotheses of `scale_narrow` on one component `x` of the vector with
squared length `s`: `|x| ≤ 2^31`, `x² ≤ s` and no tie for `p = |x| · k`. -/
def NarrowOk (x : ℤ) (k s : ℕ) : Prop :=
  x.natAbs ≤ 2 ^ 31 ∧ x.natAbs * x.natAbs ≤ s ∧
    ∀ o, Odd o → o * o * s ≠ 4 * (x.natAbs * k) * (x.natAbs * k)

/-- The loop of `scale_narrow` over the three components. -/
theorem narrow_loop_spec (v : Std.Array Std.I64 3#usize) (k s inv : Std.U64) (shift : Std.U32)
    (hk : k.val < 2 ^ 31) (hs0 : 0 < s.val) (hs : s.val ≤ 3 * 2 ^ 62) (hsh1 : 1 ≤ shift.val)
    (hsh : shift.val ≤ 94) (hv : ∀ j < 3, NarrowOk (v.val[j]!).val k.val s.val) :
    fulcrum.kernel.scale_narrow_loop0 v k s inv shift (Array.repeat 3#usize 0#i64) 0#usize ⦃ r =>
      ∀ j < 3, ScaleOut (v.val[j]!).val k.val s.val (r.val[j]!).val ⦄ := by
  unfold fulcrum.kernel.scale_narrow_loop0
  refine loop.spec_decr_nat (fun y => 3 - y.2.val)
    (fun y => y.2.val ≤ 3 ∧ ∀ j < y.2.val, ScaleOut (v.val[j]!).val k.val s.val (y.1.val[j]!).val)
    _ _ _ ?_ ⟨by simp, fun j hj => by simp at hj⟩
  rintro ⟨out, i⟩ ⟨hi, hout⟩
  dsimp only at hi hout ⊢
  by_cases h3 : i.val < 3
  · have ⟨hx, hxs, hnt⟩ := hv i.val h3
    refine WP.spec_mono (narrow_body_spec v out k s inv shift i h3 hk hs0 hs hsh1 hsh hx hxs hnt)
      fun r ⟨w, hw, i', hi', hr⟩ => ?_
    rw [hr]
    dsimp only
    refine ⟨⟨by omega, fun j hj => ?_⟩, by omega⟩
    rw [Array.set_val_eq, getElem!_set_of_lt _ _ _ _ (by rw [out.property]; exact h3)]
    by_cases e : i.val = j
    · rw [ite_eq_left e]; subst e; exact hw
    · rw [ite_eq_right e]; exact hout j (by omega)
  · unfold fulcrum.kernel.scale_narrow_loop0.body
    rw [ite_eq_right (show ¬ i < 3#usize from h3), WP.spec_ok]
    exact fun j hj => hout j (by omega)

/-- L5 on the code: `kernel::scale_narrow` scales the raw vector `v` with squared
length `0 < s ≤ 3 · 2^62` to the raw length `k < 2^31`: every component is the
magnitude of `ScaleRound` with the sign of the input. -/
theorem scale_narrow_spec (v : Std.Array Std.I64 3#usize) (k s : Std.U64) (hk : k.val < 2 ^ 31)
    (hs0 : 0 < s.val) (hs : s.val ≤ 3 * 2 ^ 62) (hv : ∀ j < 3, NarrowOk (v.val[j]!).val k.val s.val) :
    fulcrum.kernel.scale_narrow v k s ⦃ r =>
      ∀ j < 3, ScaleOut (v.val[j]!).val k.val s.val (r.val[j]!).val ⦄ := by
  unfold fulcrum.kernel.scale_narrow
  obtain ⟨L, hL⟩ : ∃ L, L = Nat.log 2 s.val := ⟨_, rfl⟩
  have hlo : 2 ^ L ≤ s.val := hL ▸ Nat.pow_log_le_self 2 (Nat.ne_zero_of_lt hs0)
  have hhi : s.val < 2 ^ (L + 1) := hL ▸ Nat.lt_pow_succ_log_self Nat.one_lt_two _
  have L63 : L ≤ 63 := by
    have : 2 ^ L < 2 ^ 64 := hlo.trans_lt (hs.trans_lt (by norm_num))
    exact Nat.le_of_lt_succ ((Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp this)
  have hlz : (core.num.U64.leading_zeros s).val = 64 - L - 1 := by
    rw [hL]; exact leading_zeros_val s (Nat.ne_zero_of_lt hs0) (Nat.le_of_ble_eq_true rfl)
  rw [lift, bind_ok]
  set! zv := 2 * ((63 - L - 1) / 2) with hzv
  refine WP.spec_bind (Pₘ := fun z : Std.U32 => z.val = zv) ?_ fun z hz => ?_
  · by_cases h0 : core.num.U64.leading_zeros s = 0#u32
    · have : (core.num.U64.leading_zeros s).val = 0 := congrArg UScalar.val h0
      rw [ite_eq_left h0, WP.spec_ok, lit_val]; omega
    · have : (core.num.U64.leading_zeros s).val ≠ 0 := fun e => h0 (UScalar.eq_of_val_eq e)
      rw [ite_eq_right h0]
      refine WP.spec_bind (UScalar.sub_spec (by rw [lit_val]; omega)) fun j ⟨hj, _⟩ => ?_
      rw [lift, bind_ok, WP.spec_ok, UScalar.val_and, hj, lit_val, hlz]
      have : (~~~1#u32 : Std.U32).val = 2 ^ 32 - 2 := rfl
      rw [this, show 64 - L - 1 - 1 = 63 - L - 1 by omega]
      exact clear_low_bit _ (by omega)
  refine WP.spec_bind (shl_i32_spec 1#u128 94#i32 94 rfl (by decide) (by rw [lit_val]; norm_num))
    fun i3 hi3 => ?_
  rw [lit_val, one_mul] at hi3
  have sz : s.val * 2 ^ zv ≤ 3 * 2 ^ 62 := by
    rcases Nat.lt_or_ge L 62 with h | h
    · have : s.val * 2 ^ zv < 2 ^ (L + 1) * 2 ^ zv := Nat.mul_lt_mul_of_pos_right hhi (Nat.two_pow_pos _)
      have z1 : zv ≤ 63 - L - 1 := Nat.mul_div_le _ 2
      have : 2 ^ (L + 1) * 2 ^ zv ≤ 2 ^ 63 := by
        rw [← pow_add]; exact Nat.pow_le_pow_right two_pos (by omega)
      omega
    · have : zv = 0 := by omega
      rw [this, pow_zero, mul_one]; exact hs
  refine WP.spec_bind (UScalar.ShiftLeft_spec s z _ (by rw [hz, UScalarTy.U64_numBits_eq]; omega) rfl)
    fun i4 ⟨hi4, _⟩ => ?_
  have i4v : i4.val = s.val * 2 ^ zv := by
    rw [hi4, hz, Nat.shiftLeft_eq, UScalar.size_def, UScalarTy.U64_numBits_eq]
    exact Nat.mod_eq_of_lt (by omega)
  have i4p : 1 ≤ i4.val := by
    rw [i4v]; exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by positivity))
  refine WP.spec_bind (k32_isqrt_spec i4 (by rw [i4v]; exact sz)) fun i5 hi5 => ?_
  rw [lift, bind_ok]
  have c5 := UScalar.cast_val_mod_pow_greater_numBits_eq .U128 i5 (by decide)
  have r1 : 1 ≤ i5.val := by rw [hi5]; exact Nat.le_sqrt.mpr (by omega)
  obtain ⟨i7, hi7, _⟩ := UScalar.div_spec i3 (y := UScalar.cast .U128 i5) (by rw [c5]; omega)
  rw [hi7, bind_ok, lift, bind_ok]
  obtain ⟨i8, hi8, hi8v⟩ := UScalar.div_spec z (y := 2#u32) (by rw [lit_val]; omega)
  rw [hi8, bind_ok]
  rw [hz, lit_val] at hi8v
  refine WP.spec_bind (UScalar.sub_spec (by rw [hi8v, lit_val]; omega)) fun sh ⟨hsh, _⟩ => ?_
  rw [hi8v, lit_val] at hsh
  exact narrow_loop_spec v k s _ sh hk hs0 hs (by omega) (by omega) hv

/-- A component of `scale_narrow` is `scaled`. -/
theorem scaleOut_scaled (x : ℤ) (k s : ℕ) (w : ℤ) (hs : 0 < s) (h : ScaleOut x k s w) :
    w = scaled x k s := by
  obtain ⟨m, sr, _, rfl⟩ := h
  rw [scaled, scaleRound_eq _ _ _ hs sr]

/-- The three components `a`, `b`, `c` of a vector with squared length
`s = a² + b² + c² > 0` satisfy the hypotheses of `scale_narrow` for `k`. -/
theorem narrowOk_of (a b c : ℤ) (k : ℕ) (ha : a.natAbs ≤ 2 ^ 31) (hb : b.natAbs ≤ 2 ^ 31)
    (hc : c.natAbs ≤ 2 ^ 31) (hs : 0 < a.natAbs * a.natAbs + b.natAbs * b.natAbs + c.natAbs * c.natAbs) :
    ∀ j < 3, NarrowOk ([a, b, c][j]!) k
      (a.natAbs * a.natAbs + b.natAbs * b.natAbs + c.natAbs * c.natAbs) := by
  intro j hj
  have : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases this with rfl | rfl | rfl
  · exact ⟨ha, by simp only [List.getElem!_cons_zero]; omega, fun o ho => no_tie o k ho _ _ _ hs⟩
  · refine ⟨hb, by simp only [List.getElem!_cons_succ, List.getElem!_cons_zero]; omega, fun o ho => ?_⟩
    have := no_tie o k ho b.natAbs a.natAbs c.natAbs (by omega)
    simp only [List.getElem!_cons_succ, List.getElem!_cons_zero]
    rwa [show a.natAbs * a.natAbs + b.natAbs * b.natAbs + c.natAbs * c.natAbs =
      b.natAbs * b.natAbs + a.natAbs * a.natAbs + c.natAbs * c.natAbs by ring]
  · refine ⟨hc, by simp only [List.getElem!_cons_succ, List.getElem!_cons_zero]; omega, fun o ho => ?_⟩
    have := no_tie o k ho c.natAbs a.natAbs b.natAbs (by omega)
    simp only [List.getElem!_cons_succ, List.getElem!_cons_zero]
    rwa [show a.natAbs * a.natAbs + b.natAbs * b.natAbs + c.natAbs * c.natAbs =
      c.natAbs * c.natAbs + a.natAbs * a.natAbs + b.natAbs * b.natAbs by ring]

/-- The body of `kernel::kN::scale_vec` for `k8`..`k32`: the zero vector stays,
any other goes through `scale_narrow` on `i64` and back; every component is
`scaled`. -/
theorem scale_vec_narrow_shape {B} (ns : Result Std.U128) (a b c k : IScalar B) (bb : ℕ)
    (hB : B.numBits = bb + 1) (hb : bb ≤ 31)
    (hns : ns ⦃ r => (r.val : ℤ) = a.val ^ 2 + b.val ^ 2 + c.val ^ 2 ⦄) (hk : 0 ≤ k.val) :
    (do
        let s ← ns
        if s = 0#u128 then ok (Array.make 3#usize [a, b, c])
        else do
          let i ← lift (IScalar.cast .I64 a)
          let i1 ← lift (IScalar.cast .I64 b)
          let i2 ← lift (IScalar.cast .I64 c)
          let i3 ← lift (IScalar.hcast .U64 k)
          let i4 ← lift (UScalar.cast .U64 s)
          let r ← fulcrum.kernel.scale_narrow (Array.make 3#usize [i, i1, i2]) i3 i4
          let i5 ← Array.index_usize r 0#usize
          let i6 ← lift (IScalar.cast B i5)
          let i7 ← Array.index_usize r 1#usize
          let i8 ← lift (IScalar.cast B i7)
          let i9 ← Array.index_usize r 2#usize
          let i10 ← lift (IScalar.cast B i9)
          ok (Array.make 3#usize [i6, i8, i10]))
      ⦃ r => ∀ j < 3, (r.val[j]!).val = scaled ([a.val, b.val, c.val][j]!) k.val.toNat
        (a.val.natAbs * a.val.natAbs + b.val.natAbs * b.val.natAbs + c.val.natAbs * c.val.natAbs) ⦄ := by
  set S := a.val.natAbs * a.val.natAbs + b.val.natAbs * b.val.natAbs + c.val.natAbs * c.val.natAbs
    with hS
  have Sz : (S : ℤ) = a.val ^ 2 + b.val ^ 2 + c.val ^ 2 := by
    rw [hS]; push_cast
    rw [abs_mul_abs_self, abs_mul_abs_self, abs_mul_abs_self]; ring
  have na := natAbs_le_pow a bb hB
  have nb := natAbs_le_pow b bb hB
  have nc := natAbs_le_pow c bb hB
  have p31 : 2 ^ bb ≤ 2 ^ 31 := Nat.pow_le_pow_right two_pos hb
  refine WP.spec_bind hns fun s hs => ?_
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
  have h64 : B.numBits ≤ IScalarTy.I64.numBits := by rw [hB]; simp; omega
  have ca := IScalar.val_mod_pow_greater_numBits .I64 a h64
  have cb := IScalar.val_mod_pow_greater_numBits .I64 b h64
  have cc := IScalar.val_mod_pow_greater_numBits .I64 c h64
  simp only [lift, bind_ok]
  have kv : (IScalar.hcast .U64 k).val = k.val.toNat := by
    rw [IScalar.hcast_val_eq, Int.emod_eq_of_lt hk]
    have := (val_bounds k hB).2
    have : (2 : ℤ) ^ bb ≤ 2 ^ UScalarTy.U64.numBits := by
      rw [UScalarTy.U64_numBits_eq]; exact pow_le_pow_right₀ one_le_two (by omega)
    omega
  have kb : k.val.toNat < 2 ^ 31 := by
    have := (val_bounds k hB).2
    have : k.val < ((2 ^ bb : ℕ) : ℤ) := by exact_mod_cast this
    omega
  have Sb : S ≤ 3 * 2 ^ 62 := by
    have := Nat.mul_le_mul na na
    have := Nat.mul_le_mul nb nb
    have := Nat.mul_le_mul nc nc
    have : 2 ^ bb * 2 ^ bb ≤ 2 ^ 62 := by rw [← pow_add]; exact Nat.pow_le_pow_right two_pos (by omega)
    omega
  have sc : (UScalar.cast .U64 s).val = S := by
    rw [UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by rw [sv, UScalarTy.U64_numBits_eq]; omega), sv]
  set v := Array.make 3#usize [IScalar.cast .I64 a, IScalar.cast .I64 b, IScalar.cast .I64 c]
  have vj : ∀ j < 3, (v.val[j]!).val = [a.val, b.val, c.val][j]! := by
    intro j hj
    have : j = 0 ∨ j = 1 ∨ j = 2 := by omega
    rcases this with rfl | rfl | rfl <;> simp [v, Array.make, ca, cb, cc]
  have hv : ∀ j < 3, NarrowOk (v.val[j]!).val (IScalar.hcast .U64 k).val (UScalar.cast .U64 s).val := by
    intro j hj
    rw [vj j hj, kv, sc]
    exact narrowOk_of a.val b.val c.val k.val.toNat (na.trans p31) (nb.trans p31) (nc.trans p31) S0 j hj
  refine WP.spec_bind (scale_narrow_spec v _ _ (by rw [kv]; exact kb) (by rw [sc]; exact S0)
    (by rw [sc]; exact Sb) hv) fun r hr => ?_
  have out : ∀ j < 3, ∃ m ≤ k.val.toNat, (r.val[j]!).val = scaled ([a.val, b.val, c.val][j]!)
      k.val.toNat S ∧ (r.val[j]!).val.natAbs ≤ m := by
    intro j hj
    have h := hr j hj
    rw [vj j hj, kv, sc] at h
    obtain ⟨m, sr, mk, hw⟩ := h
    refine ⟨m, mk, scaleOut_scaled _ _ _ _ S0 ⟨m, sr, mk, hw⟩, ?_⟩
    rw [hw]; split <;> simp
  have back : ∀ w : Std.I64, w.val.natAbs ≤ k.val.toNat → (IScalar.cast B w).val = w.val := by
    intro w hw
    rw [IScalar.cast_val_eq, show min B.numBits IScalarTy.I64.numBits = bb + 1 by
      rw [hB]; simp; omega]
    have : (w.val.natAbs : ℤ) < 2 ^ bb := by
      have : k.val.toNat < 2 ^ bb := by
        have := (val_bounds k hB).2
        have : k.val < ((2 ^ bb : ℕ) : ℤ) := by exact_mod_cast this
        omega
      exact_mod_cast (lt_of_le_of_lt hw this)
    have := Int.natCast_natAbs w.val
    rw [Int.natCast_natAbs] at this
    have ⟨l, u⟩ := abs_lt.mp (show |w.val| < 2 ^ bb by rwa [← Int.natCast_natAbs])
    exact Int.bmod_eq_of_le (by push_cast; rw [pow_succ]; omega) (by push_cast; rw [pow_succ]; omega)
  refine WP.spec_bind (arr3_read r 0#usize 0 rfl (by omega)) fun x0 hx0 => ?_
  refine WP.spec_bind (arr3_read r 1#usize 1 rfl (by omega)) fun x1 hx1 => ?_
  refine WP.spec_bind (arr3_read r 2#usize 2 rfl (by omega)) fun x2 hx2 => ?_
  rw [WP.spec_ok]
  intro j hj
  have : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  rcases this with rfl | rfl | rfl
  · obtain ⟨m, mk, e, le⟩ := out 0 (by omega)
    rw [Array.make_val]; simp only [List.getElem!_cons_zero]
    rw [back _ (hx0 ▸ le.trans mk), hx0, e]
    rfl
  · obtain ⟨m, mk, e, le⟩ := out 1 (by omega)
    rw [Array.make_val]; simp only [List.getElem!_cons_succ, List.getElem!_cons_zero]
    rw [back _ (hx1 ▸ le.trans mk), hx1, e]
    rfl
  · obtain ⟨m, mk, e, le⟩ := out 2 (by omega)
    rw [Array.make_val]; simp only [List.getElem!_cons_succ, List.getElem!_cons_zero]
    rw [back _ (hx2 ▸ le.trans mk), hx2, e]
    rfl

/-- L5 on the code: `kernel::k8::scale_vec` scales `(a, b, c)` to the raw length
`k ≥ 0`: every component is `round(|x| · k / √(a² + b² + c²))` with the sign of `x`. -/
theorem k8_scale_vec_spec (a b c k : Std.I8) (hk : 0 ≤ k.val) :
    fulcrum.kernel.k8.scale_vec a b c k ⦃ r => ∀ j < 3, (r.val[j]!).val =
      scaled ([a.val, b.val, c.val][j]!) k.val.toNat
        (a.val.natAbs * a.val.natAbs + b.val.natAbs * b.val.natAbs + c.val.natAbs * c.val.natAbs) ⦄ := by
  unfold fulcrum.kernel.k8.scale_vec
  exact scale_vec_narrow_shape _ a b c k 7 rfl (by norm_num) (k8_norm_sq_spec a b c) hk

/-- L5 on the code: `kernel::k16::scale_vec` scales `(a, b, c)` to the raw length
`k ≥ 0`: every component is `round(|x| · k / √(a² + b² + c²))` with the sign of `x`. -/
theorem k16_scale_vec_spec (a b c k : Std.I16) (hk : 0 ≤ k.val) :
    fulcrum.kernel.k16.scale_vec a b c k ⦃ r => ∀ j < 3, (r.val[j]!).val =
      scaled ([a.val, b.val, c.val][j]!) k.val.toNat
        (a.val.natAbs * a.val.natAbs + b.val.natAbs * b.val.natAbs + c.val.natAbs * c.val.natAbs) ⦄ := by
  unfold fulcrum.kernel.k16.scale_vec
  exact scale_vec_narrow_shape _ a b c k 15 rfl (by norm_num) (k16_norm_sq_spec a b c) hk

/-- L5 on the code: `kernel::k32::scale_vec` scales `(a, b, c)` to the raw length
`k ≥ 0`: every component is `round(|x| · k / √(a² + b² + c²))` with the sign of `x`. -/
theorem k32_scale_vec_spec (a b c k : Std.I32) (hk : 0 ≤ k.val) :
    fulcrum.kernel.k32.scale_vec a b c k ⦃ r => ∀ j < 3, (r.val[j]!).val =
      scaled ([a.val, b.val, c.val][j]!) k.val.toNat
        (a.val.natAbs * a.val.natAbs + b.val.natAbs * b.val.natAbs + c.val.natAbs * c.val.natAbs) ⦄ := by
  unfold fulcrum.kernel.k32.scale_vec
  exact scale_vec_narrow_shape _ a b c k 31 rfl (by norm_num) (k32_norm_sq_spec a b c) hk

end Fulcrum

end
