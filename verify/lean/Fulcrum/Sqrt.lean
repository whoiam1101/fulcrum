module

public import Fulcrum.Div
public import Mathlib.Data.Nat.Sqrt

/-!
# L3: `kernel::kN::isqrt`

`isqrt(n)` of `k8` and `k16`, as Aeneas extracts it, never fails and is `⌊√n⌋`
on its domain `n ≤ 3 · 2^(BITS - 2)`. The start is `SQRT_START` at the leading
bits of `n` taken in pairs; the table, built by the compiler, is
`⌊√((2t + 1) · 2^15)⌋` (`sqrt_start_spec`). One Newton step from any `x > 0` is at
least `⌊√n⌋` (`sqrt_le_newton`); from a start whose square is close to `n`
(`start_good8`, `start_good16`) its square fits the type (`newton_bound`), and
the final loop steps down to `⌊√n⌋` exactly (`descend_spec`).
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace Fulcrum


/-- `2·⌊√n⌋ ≤ x + ⌊n / x⌋` for `x > 0`: the arithmetic mean bound. -/
theorem two_sqrt_le (n x : ℕ) (hx : 0 < x) : 2 * Nat.sqrt n ≤ x + n / x := by
  set s := Nat.sqrt n
  by_cases h : 2 * s ≤ x
  · exact h.trans (Nat.le_add_right _ _)
  have amgm : ((2 * s - x : ℕ) : ℤ) * x ≤ (s : ℤ) * s := by
    rw [Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat]
    have e : (s : ℤ) * s - (2 * s - x) * x = (s - x) * (s - x) := by ring
    exact sub_nonneg.mp (e ▸ mul_self_nonneg _)
  have : (2 * s - x) * x ≤ n := (Int.ofNat_le.mp (by exact_mod_cast amgm)).trans (Nat.sqrt_le n)
  have := (Nat.le_div_iff_mul_le hx).mpr this
  omega

/-- One Newton step from any `x > 0` stays at or above `⌊√n⌋`. -/
theorem sqrt_le_newton (n x : ℕ) (hx : 0 < x) : Nat.sqrt n ≤ (x + n / x) / 2 :=
  (Nat.le_div_iff_mul_le two_pos).mpr (by rw [mul_comm]; exact two_sqrt_le n x hx)

/-- The final loop of `isqrt`: from `x ≥ ⌊√n⌋` with `x²` inside the type, step
down while `x² > n`; it stops at `⌊√n⌋`. -/
theorem descend_spec {U} (n x one : UScalar U) (h1 : one.val = 1)
    (hs : Nat.sqrt n.val ≤ x.val) (hf : x.val * x.val ≤ UScalar.max U) :
    loop (fun (x1 : UScalar U) => do
        let i ← x1 * x1
        if i > n then do let x2 ← x1 - one; ok (ControlFlow.cont x2) else ok (ControlFlow.done x1))
      x ⦃ r => r.val = Nat.sqrt n.val ⦄ := by
  refine loop.spec_decr_nat (fun y => y.val)
    (fun y => Nat.sqrt n.val ≤ y.val ∧ y.val * y.val ≤ UScalar.max U) _ _ x ?_ ⟨hs, hf⟩
  intro y ⟨ys, yf⟩
  refine WP.spec_bind (UScalar.mul_spec yf) fun i hi => ?_
  by_cases hgt : i > n
  · have gt : n.val < y.val * y.val := hi ▸ hgt
    have lt : Nat.sqrt n.val < y.val := Nat.sqrt_lt.mpr gt
    rw [ite_eq_left hgt]
    refine WP.spec_bind (UScalar.sub_spec (x := y) (y := one) (by rw [h1]; omega))
      fun y2 ⟨hy2, _⟩ => ?_
    rw [WP.spec_ok]
    rw [h1] at hy2
    refine ⟨⟨by omega, (Nat.mul_le_mul (by omega) (by omega)).trans yf⟩, by omega⟩
  · have le : y.val * y.val ≤ n.val := hi ▸ not_lt.mp hgt
    rw [ite_eq_right hgt, WP.spec_ok]
    exact Nat.eq_sqrt.mpr ⟨le, (Nat.lt_succ_sqrt n.val).trans_le
      (Nat.mul_le_mul (Nat.succ_le_succ ys) (Nat.succ_le_succ ys))⟩

/-- `usize` holds every `u32`. -/
theorem usize_max_ge : 2 ^ 32 - 1 ≤ UScalar.max .Usize := by
  rw [UScalar.max_def, UScalarTy.Usize_numBits_eq]
  rcases System.Platform.numBits_eq with h | h
  · rw [h]
  · rw [h]; decide

/-- The inner loop of `sqrt_start`: from `s ≤ ⌊√v⌋`, step up while `(s+1)² ≤ v`. -/
theorem ascend_spec (s v : Std.U32) (hs : Nat.sqrt v.val ≤ 2 ^ 15) (h : s.val ≤ Nat.sqrt v.val) :
    fulcrum.kernel.sqrt_start_loop0_loop0 s v ⦃ r => r.val = Nat.sqrt v.val ⦄ := by
  unfold fulcrum.kernel.sqrt_start_loop0_loop0
  refine loop.spec_decr_nat (fun y => Nat.sqrt v.val + 1 - y.val)
    (fun y => y.val ≤ Nat.sqrt v.val) _ _ s ?_ h
  intro y hy
  unfold fulcrum.kernel.sqrt_start_loop0_loop0.body
  have one : (1#u32 : Std.U32).val = 1 := rfl
  refine WP.spec_bind (UScalar.add_spec (x := y) (y := 1#u32)
    (by rw [one, UScalar.max_def, UScalarTy.U32_numBits_eq]; omega)) fun i hi => ?_
  rw [one] at hi
  have sq : i.val * i.val ≤ (2 ^ 15 + 1) * (2 ^ 15 + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  refine WP.spec_bind (UScalar.mul_spec (x := i) (y := i)
    (by rw [UScalar.max_def, UScalarTy.U32_numBits_eq]; omega)) fun i1 hi1 => ?_
  by_cases hle : i1 ≤ v
  · rw [ite_eq_left hle, WP.spec_ok]
    have : i.val ≤ Nat.sqrt v.val := Nat.le_sqrt.mpr (hi1 ▸ hle)
    exact ⟨this, by omega⟩
  · rw [ite_eq_right hle, WP.spec_ok]
    have lt : v.val < i.val * i.val := hi1 ▸ not_le.mp hle
    exact Nat.eq_sqrt.mpr ⟨(Nat.le_sqrt.mp hy), hi ▸ lt⟩

/-- Reading a list after a write inside it. -/
theorem getElem!_set_of_lt {α} [Inhabited α] (l : List α) (i j : ℕ) (a : α) (h : i < l.length) :
    (l.set i a)[j]! = if i = j then a else l[j]! := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_set, List.getElem!_eq_getElem?_getD]
  split <;> rfl

/-- The table `SQRT_START`: `⌊√((2t + 1) · 2^15)⌋` at every `t < 256`. -/
theorem sqrt_start_spec :
    fulcrum.kernel.SQRT_START
      ⦃ a => ∀ t < 256, (a.val[t]!).val = Nat.sqrt ((2 * t + 1) * 2 ^ 15) ⦄ := by
  unfold fulcrum.kernel.SQRT_START fulcrum.kernel.sqrt_start fulcrum.kernel.sqrt_start_loop0
  refine loop.spec_decr_nat (fun y => 256 - y.2.1.val)
    (fun y => y.2.1.val ≤ 256 ∧
      y.2.2.val = (if y.2.1.val = 0 then 0 else Nat.sqrt ((2 * y.2.1.val - 1) * 2 ^ 15)) ∧
      (∀ t < y.2.1.val, (y.1.val[t]!).val = Nat.sqrt ((2 * t + 1) * 2 ^ 15))) _ _ _ ?_
    ⟨Nat.zero_le _, rfl, fun t ht => absurd ht (Nat.not_lt_zero t)⟩
  rintro ⟨table, t, s⟩ ⟨ht, hs, htab⟩
  unfold fulcrum.kernel.sqrt_start_loop0.body
  dsimp only at ht hs htab ⊢
  by_cases hlt : t < 256#usize
  · have hlt' : t.val < 256 := hlt
    rw [ite_eq_left hlt]
    have um := usize_max_ge
    have two : (2#usize : Std.Usize).val = 2 := rfl
    have one : (1#usize : Std.Usize).val = 1 := rfl
    refine WP.spec_bind (UScalar.mul_spec (x := 2#usize) (y := t) (by rw [two]; omega))
      fun i hi => ?_
    refine WP.spec_bind (UScalar.add_spec (x := i) (y := 1#usize) (by rw [hi, two, one]; omega))
      fun i1 hi1 => ?_
    rw [lift, bind_ok]
    have c1 : (UScalar.cast .U32 i1).val = 2 * t.val + 1 := by
      rw [UScalar.cast_val_eq, hi1, hi, two, one, UScalarTy.U32_numBits_eq]
      exact Nat.mod_eq_of_lt (by omega)
    refine WP.spec_bind (UScalar.ShiftLeft_IScalar_spec (UScalar.cast .U32 i1) 15#i32 _
      (by decide) (by decide) rfl) fun v ⟨hv, _⟩ => ?_
    have hv' : v.val = (2 * t.val + 1) * 2 ^ 15 := by
      rw [hv, show (15#i32 : Std.I32).toNat = 15 from rfl, c1, Nat.shiftLeft_eq,
        UScalar.size_def, UScalarTy.U32_numBits_eq]
      exact Nat.mod_eq_of_lt (by omega)
    have sq : Nat.sqrt v.val ≤ 2 ^ 15 :=
      (Nat.sqrt_lt'.mpr (by rw [hv']; omega)).le
    have mono : s.val ≤ Nat.sqrt v.val := by
      rw [hs, hv']
      split
      · exact Nat.zero_le _
      · exact Nat.sqrt_le_sqrt (Nat.mul_le_mul_right _ (by omega))
    refine WP.spec_bind (ascend_spec s v sq mono) fun s1 hs1 => ?_
    rw [lift, bind_ok]
    have c2 : (UScalar.cast .U16 s1).val = s1.val := by
      rw [UScalar.cast_val_eq, UScalarTy.U16_numBits_eq]
      exact Nat.mod_eq_of_lt (by omega)
    refine WP.spec_bind (Array.update_spec table t _ (by rw [Array.length, table.property]; exact hlt'))
      fun a ha => ?_
    refine WP.spec_bind (UScalar.add_spec (x := t) (y := 1#usize) (by rw [one]; omega))
      fun t1 ht1 => ?_
    rw [WP.spec_ok]
    dsimp only
    rw [one] at ht1
    refine ⟨⟨by omega, ?_, fun k hk => ?_⟩, by omega⟩
    · rw [ite_eq_right (by omega), hs1, hv', ht1]
      congr 2
    · rw [ha, Array.set_val_eq, getElem!_set_of_lt _ _ _ _ (by rw [table.property]; exact hlt')]
      split
      · next e => rw [c2, hs1, hv', e]
      · exact htab k (by omega)
  · rw [ite_eq_right hlt, WP.spec_ok]
    have : t.val = 256 := by have : ¬ t.val < 256 := hlt; omega
    exact fun k hk => htab k (this ▸ hk)

/-- `u32::leading_zeros` of a non-zero `n` is `31 - ⌊log₂ n⌋`. -/
theorem U32_leading_zeros_val (n : Std.U32) (hn : n.val ≠ 0) :
    (core.num.U32.leading_zeros n).val = 32 - Nat.log 2 n.val - 1 := by
  have hl : Nat.log 2 n.val < 32 := Nat.log_lt_of_lt_pow hn (by have := n.hmax; exact this)
  have hb : n.bv ≠ 0 := fun h => hn ((congrArg BitVec.toNat h).trans rfl)
  rw [core.num.U32.leading_zeros, UScalar.val, BitVec.leadingZeros, ite_eq_right hb, show n.bv.toNat = n.val from rfl]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _)
    (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (by rw [UScalarTy.U32_numBits_eq]; decide)))

/-- The Newton loop of `k16::isqrt`: `NEWTON_STEPS = 1`, one step from `x > 0`. -/
theorem k16_newton_spec (n x : Std.U32) (hx : 0 < x.val)
    (hf : x.val + n.val / x.val ≤ UScalar.max .U32) :
    fulcrum.kernel.k16.isqrt_loop0 n x 0#u32 ⦃ r => r.val = (x.val + n.val / x.val) / 2 ⦄ := by
  have steps : fulcrum.kernel.k16.NEWTON_STEPS = 1#u32 := by
    unfold fulcrum.kernel.k16.NEWTON_STEPS; rfl
  unfold fulcrum.kernel.k16.isqrt_loop0
  refine loop.spec_decr_nat (fun y => 1 - y.2.val)
    (fun y => (y.2.val = 0 ∧ y.1 = x) ∨ (y.2.val = 1 ∧ y.1.val = (x.val + n.val / x.val) / 2))
    _ _ _ ?_ (Or.inl ⟨rfl, rfl⟩)
  rintro ⟨y, i⟩ hinv
  unfold fulcrum.kernel.k16.isqrt_loop0.body
  dsimp only at hinv ⊢
  rw [steps]
  rcases hinv with ⟨hi, rfl⟩ | ⟨hi, hy⟩
  · rw [ite_eq_left (show i < 1#u32 from by show i.val < 1; omega)]
    obtain ⟨q, hq, hqv⟩ := UScalar.div_spec n (y := y) (by omega)
    rw [hq, bind_ok]
    refine WP.spec_bind (UScalar.add_spec (x := y) (y := q) (by rw [hqv]; exact hf)) fun s hs => ?_
    have one : (1#i32 : Std.I32).toNat = 1 := rfl
    refine WP.spec_bind (UScalar.ShiftRight_IScalar_spec s 1#i32 (by decide) (by decide))
      fun x1 ⟨hx1, _⟩ => ?_
    refine WP.spec_bind (UScalar.add_spec (x := i) (y := 1#u32)
      (by rw [hi, show (1#u32 : Std.U32).val = 1 from rfl, UScalar.max_def, UScalarTy.U32_numBits_eq]; decide)) fun i1 hi1 => ?_
    rw [WP.spec_ok]
    refine ⟨Or.inr ⟨by rw [hi1, hi]; rfl, ?_⟩, by rw [hi1, hi]; decide⟩
    rw [hx1, one, Nat.shiftRight_eq_div_pow, hs, hqv, pow_one]
  · rw [ite_eq_right (show ¬ i < 1#u32 from by show ¬ i.val < 1; omega), WP.spec_ok]
    exact hy

/-- `⌊√m⌋ / k = ⌊√(m / k²)⌋`. -/
theorem sqrt_div_eq (m k : ℕ) (hk : 0 < k) : Nat.sqrt m / k = Nat.sqrt (m / (k * k)) := by
  refine Nat.eq_sqrt.mpr ⟨?_, ?_⟩
  · refine (Nat.le_div_iff_mul_le (Nat.mul_pos hk hk)).mpr ?_
    have h := Nat.div_mul_le_self (Nat.sqrt m) k
    calc Nat.sqrt m / k * (Nat.sqrt m / k) * (k * k)
        = (Nat.sqrt m / k * k) * (Nat.sqrt m / k * k) := by ring
      _ ≤ Nat.sqrt m * Nat.sqrt m := Nat.mul_le_mul h h
      _ ≤ m := Nat.sqrt_le m
  · refine (Nat.div_lt_iff_lt_mul (Nat.mul_pos hk hk)).mpr ?_
    have h : Nat.sqrt m + 1 ≤ (Nat.sqrt m / k + 1) * k := by
      have := Nat.lt_div_mul_add (a := Nat.sqrt m) hk
      rw [Nat.add_mul, one_mul]; omega
    calc m < (Nat.sqrt m + 1) * (Nat.sqrt m + 1) := Nat.lt_succ_sqrt m
      _ ≤ ((Nat.sqrt m / k + 1) * k) * ((Nat.sqrt m / k + 1) * k) := Nat.mul_le_mul h h
      _ = (Nat.sqrt m / k + 1) * (Nat.sqrt m / k + 1) * (k * k) := by ring

/-- From the table entry `T ≤ √((2t + 1) · 2^15)` and `x₀ · 2^8 ≤ T · Q`,
`t · Q² ≤ n`: `2 · x₀² ≤ 2 · n + Q²`. -/
theorem start_upper (n t T x0 Q : ℕ) (hx : x0 * 256 ≤ T * Q) (hT : T * T ≤ (2 * t + 1) * 2 ^ 15)
    (ht : t * (Q * Q) ≤ n) : 2 * (x0 * x0) ≤ 2 * n + Q * Q := by
  have h1 : x0 * x0 * 65536 ≤ (2 * t + 1) * (Q * Q) * 32768 :=
    calc x0 * x0 * 65536 = (x0 * 256) * (x0 * 256) := by ring
      _ ≤ (T * Q) * (T * Q) := Nat.mul_le_mul hx hx
      _ = (T * T) * (Q * Q) := by ring
      _ ≤ ((2 * t + 1) * 2 ^ 15) * (Q * Q) := Nat.mul_le_mul_right _ hT
      _ = (2 * t + 1) * (Q * Q) * 32768 := by ring
  have h2 : 2 * (x0 * x0) ≤ (2 * t + 1) * (Q * Q) := by omega
  have e : (2 * t + 1) * (Q * Q) = 2 * (t * (Q * Q)) + Q * Q := by ring
  omega

/-- From `(2t + 1) · 2^15 < (T + 1)²`, `T · Q < (x₀ + 1) · 2^8` and
`n < (t + 1) · Q²`: `2^16 · n < ((x₀ + 1) · 2^8 + Q)² + 2^16 · Q²`. -/
theorem start_lower (n t T x0 Q : ℕ) (hQ : 0 < Q) (hx : T * Q < (x0 + 1) * 256)
    (hT : (2 * t + 1) * 2 ^ 15 < (T + 1) * (T + 1)) (ht : n < (t + 1) * (Q * Q)) :
    65536 * n < ((x0 + 1) * 256 + Q) * ((x0 + 1) * 256 + Q) + 65536 * (Q * Q) := by
  have hq : (T + 1) * Q ≤ (x0 + 1) * 256 + Q := by rw [Nat.add_mul, one_mul]; omega
  have h1 : 65536 * (t * (Q * Q)) < ((x0 + 1) * 256 + Q) * ((x0 + 1) * 256 + Q) := by
    have hT' : 65536 * t < (T + 1) * (T + 1) := by omega
    calc 65536 * (t * (Q * Q)) = (65536 * t) * (Q * Q) := by ring
      _ < ((T + 1) * (T + 1)) * (Q * Q) := Nat.mul_lt_mul_of_pos_right hT' (Nat.mul_pos hQ hQ)
      _ = ((T + 1) * Q) * ((T + 1) * Q) := by ring
      _ ≤ ((x0 + 1) * 256 + Q) * ((x0 + 1) * 256 + Q) := Nat.mul_le_mul hq hq
  have e : (t + 1) * (Q * Q) = t * (Q * Q) + Q * Q := by ring
  omega

/-- The start of `k16::isqrt` above eight bits: `x₀` is within `(2^16 - 2) · x₀`
of `n` in square. -/
theorem start_good16 (n t T x0 Q : ℕ) (hQ : 0 < Q) (hn : n ≤ 3 * 2 ^ 30)
    (hlo : x0 * 256 ≤ T * Q) (hhi : T * Q < (x0 + 1) * 256)
    (hT1 : T * T ≤ (2 * t + 1) * 2 ^ 15) (hT2 : (2 * t + 1) * 2 ^ 15 < (T + 1) * (T + 1))
    (ht1 : t * (Q * Q) ≤ n) (ht2 : n < (t + 1) * (Q * Q)) (h64 : 64 ≤ t) :
    1 ≤ x0 ∧ x0 < 2 ^ 16 ∧ x0 * x0 ≤ n + 65534 * x0 ∧ n ≤ x0 * x0 + 65534 * x0 := by
  have U := start_upper n t T x0 Q hlo hT1 ht1
  have L := start_lower n t T x0 Q hQ hhi hT2 ht2
  have T11 : 2 ^ 11 ≤ T := by
    by_contra hc
    have : T + 1 ≤ 2 ^ 11 := by omega
    have := Nat.mul_le_mul this this
    omega
  have q4 : Q * 4 ≤ x0 := by
    have : 2 ^ 11 * Q ≤ T * Q := Nat.mul_le_mul_right _ T11
    omega
  have qq : Q * Q * 16 ≤ x0 * x0 := by
    have := Nat.mul_le_mul q4 q4
    calc Q * Q * 16 = (Q * 4) * (Q * 4) := by ring
      _ ≤ x0 * x0 := this
  have pq : x0 * Q * 4 ≤ x0 * x0 := by
    calc x0 * Q * 4 = x0 * (Q * 4) := by ring
      _ ≤ x0 * x0 := Nat.mul_le_mul_left _ q4
  have xb : x0 < 2 ^ 16 := by
    have : x0 * x0 < 2 ^ 16 * 2 ^ 16 := by omega
    exact Nat.mul_self_lt_mul_self_iff.mp this
  have xx : x0 * x0 ≤ 2 ^ 16 * x0 := Nat.mul_le_mul_right _ xb.le
  have e : ((x0 + 1) * 256 + Q) * ((x0 + 1) * 256 + Q) =
      65536 * (x0 * x0) + 131072 * x0 + 65536 + 512 * (x0 * Q) + 512 * Q + Q * Q := by ring
  refine ⟨by omega, by omega, by omega⟩

/-- One Newton step from `x₀` with `x₀² ≈ n` within `D · x₀`: the sum and the
square of the step are bounded by `n` and `D`. -/
theorem newton_bound (n x0 D : ℕ) (h1 : 1 ≤ x0) (hu : x0 * x0 ≤ n + D * x0)
    (hl : n ≤ x0 * x0 + D * x0) :
    x0 + n / x0 ≤ 2 * x0 + D ∧
      4 * ((x0 + n / x0) / 2 * ((x0 + n / x0) / 2)) ≤ D * D + 4 * n := by
  set q := n / x0
  have hq1 : q * x0 ≤ n := Nat.div_mul_le_self n x0
  have hq2 : n < q * x0 + x0 := Nat.lt_div_mul_add h1
  have hxq : x0 ≤ q + D := by
    by_contra hc
    have : (q + D + 1) * x0 ≤ x0 * x0 := Nat.mul_le_mul_right _ (by omega)
    have e : (q + D + 1) * x0 = q * x0 + D * x0 + x0 := by ring
    omega
  have hqx : q ≤ x0 + D := by
    by_contra hc
    have : (x0 + D + 1) * x0 ≤ q * x0 := Nat.mul_le_mul_right _ (by omega)
    have e : (x0 + D + 1) * x0 = x0 * x0 + D * x0 + x0 := by ring
    omega
  refine ⟨by omega, ?_⟩
  have h2 : 2 * ((x0 + q) / 2) ≤ x0 + q := Nat.mul_div_le _ _
  have sq : 4 * ((x0 + q) / 2 * ((x0 + q) / 2)) ≤ (x0 + q) * (x0 + q) := by
    calc 4 * ((x0 + q) / 2 * ((x0 + q) / 2))
        = (2 * ((x0 + q) / 2)) * (2 * ((x0 + q) / 2)) := by ring
      _ ≤ (x0 + q) * (x0 + q) := Nat.mul_le_mul h2 h2
  rcases le_total x0 q with hle | hle
  · obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hle
    rw [he] at sq hq1 hqx ⊢
    have ee : e * e ≤ D * D := Nat.mul_le_mul (by omega) (by omega)
    have id : (x0 + (x0 + e)) * (x0 + (x0 + e)) = e * e + 4 * ((x0 + e) * x0) := by ring
    omega
  · obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le hle
    rw [he] at sq hq1 ⊢
    have ee : e * e ≤ D * D := Nat.mul_le_mul (by omega) (by omega)
    have id : (q + e + q) * (q + e + q) = e * e + 4 * (q * (q + e)) := by ring
    omega

/-- L3 on the code: `kernel::k16::isqrt` is `⌊√n⌋` for `n ≤ 3 · 2^30`. -/
theorem k16_isqrt_spec (n : Std.U32) (hn : n.val ≤ 3 * 2 ^ 30) :
    fulcrum.kernel.k16.isqrt n ⦃ r => r.val = Nat.sqrt n.val ⦄ := by
  unfold fulcrum.kernel.k16.isqrt
  by_cases h2 : n < 2#u32
  · rw [ite_eq_left h2, WP.spec_ok]
    have : n.val < 2 := h2
    rcases (show n.val = 0 ∨ n.val = 1 by omega) with h | h <;> rw [h] <;> rfl
  rw [ite_eq_right h2]
  have hn2 : 2 ≤ n.val := Nat.le_of_not_lt h2
  set L := Nat.log 2 n.val with hL
  have hlo : 2 ^ L ≤ n.val := Nat.pow_log_le_self 2 (by omega)
  have hhi : n.val < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by decide) _
  have L31 : L ≤ 31 := by
    by_contra hc
    have : 2 ^ 32 ≤ 2 ^ L := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have L1 : 1 ≤ L := by
    by_contra hc
    have : L = 0 := by omega
    rw [this] at hhi
    omega
  rw [lift, bind_ok]
  have hlz := U32_leading_zeros_val n (by omega)
  refine WP.spec_bind (UScalar.sub_spec (x := core.num.U32.BITS) (y := core.num.U32.leading_zeros n)
    (by rw [hlz, show core.num.U32.BITS.val = 32 from rfl]; omega)) fun bits ⟨hbits, _⟩ => ?_
  rw [hlz, show core.num.U32.BITS.val = 32 from rfl] at hbits
  have hb : bits.val = L + 1 := by omega
  have hj : (if bits ≤ 8#u32 then ok 0#u32 else do
        let i1 ← bits - 7#u32
        i1 / 2#u32) ⦃ j => j.val = if L + 1 ≤ 8 then 0 else (L - 6) / 2 ⦄ := by
    by_cases h8 : bits ≤ 8#u32
    · have h8' : L + 1 ≤ 8 := by have : bits.val ≤ 8 := h8; omega
      rw [ite_eq_left h8, WP.spec_ok, ite_eq_left h8']
      rfl
    · have h8' : ¬ L + 1 ≤ 8 := by have : ¬ bits.val ≤ 8 := h8; omega
      rw [ite_eq_right h8, ite_eq_right h8']
      refine WP.spec_bind (UScalar.sub_spec (x := bits) (y := 7#u32)
        (by rw [show (7#u32 : Std.U32).val = 7 from rfl]; omega)) fun i1 ⟨hi1, _⟩ => ?_
      obtain ⟨q, hq, hqv⟩ := UScalar.div_spec i1 (y := 2#u32) (by decide)
      rw [hq, WP.spec_ok, hqv, hi1, show (7#u32 : Std.U32).val = 7 from rfl,
        show (2#u32 : Std.U32).val = 2 from rfl]
      omega
  refine WP.spec_bind hj fun j hjv => ?_
  refine WP.spec_bind sqrt_start_spec fun a ha => ?_
  have j12 : j.val ≤ 12 := by rw [hjv]; split <;> omega
  refine WP.spec_bind (UScalar.mul_spec (x := 2#u32) (y := j)
    (by rw [show (2#u32 : Std.U32).val = 2 from rfl, UScalar.max_def, UScalarTy.U32_numBits_eq];
        omega)) fun i1 hi1 => ?_
  rw [show (2#u32 : Std.U32).val = 2 from rfl] at hi1
  refine WP.spec_bind (UScalar.ShiftRight_spec n i1 (by rw [hi1, UScalarTy.U32_numBits_eq]; omega))
    fun i2 ⟨hi2, _⟩ => ?_
  rw [hi1, Nat.shiftRight_eq_div_pow] at hi2
  set t := n.val / 2 ^ (2 * j.val) with ht
  have tQ : 2 ^ (2 * j.val) = 2 ^ j.val * 2 ^ j.val := by rw [two_mul, pow_add]
  have tlt : t < 256 := by
    rw [ht, Nat.div_lt_iff_lt_mul (by positivity)]
    calc n.val < 2 ^ (L + 1) := hhi
      _ ≤ 2 ^ (8 + 2 * j.val) := Nat.pow_le_pow_right (by decide) (by rw [hjv]; split <;> omega)
      _ = 256 * 2 ^ (2 * j.val) := by rw [pow_add]; rfl
  rw [lift, bind_ok]
  have um := usize_max_ge
  have c3 : (UScalar.cast .Usize i2).val = t := by
    rw [UScalar.cast_val_eq, hi2]
    exact Nat.mod_eq_of_lt (by rw [UScalarTy.Usize_numBits_eq]; rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> omega)
  refine WP.spec_bind (Array.index_usize_spec a _ (by rw [c3, Array.length, a.property]; exact tlt))
    fun i4 hi4 => ?_
  rw [lift, bind_ok]
  have hidx : (UScalar.cast .Usize i2).val < a.val.length := by rw [c3, a.property]; exact tlt
  have e1 : i4 = a.val[(UScalar.cast .Usize i2).val]! := by
    rw [hi4]; exact (getElem!_pos a.val _ hidx).symm
  obtain ⟨T, hTdef⟩ : ∃ T, T = Nat.sqrt ((2 * t + 1) * 2 ^ 15) := ⟨_, rfl⟩
  have e2 : (a.val[(UScalar.cast .Usize i2).val]!).val = T := by
    rw [c3]; exact (ha t tlt).trans hTdef.symm
  have T12 : T < 2 ^ 12 := hTdef ▸ Nat.sqrt_lt'.mpr (by omega)
  have hT : (UScalar.cast .U32 i4).val = T := by
    rw [UScalar.cast_val_eq, e1, e2, UScalarTy.U32_numBits_eq]
    exact Nat.mod_eq_of_lt (by omega)
  have hx : (if j ≥ 8#u32 then do
        let i5 ← j - 8#u32
        UScalar.cast .U32 i4 <<< i5
      else do
        let i5 ← 8#u32 - j
        UScalar.cast .U32 i4 >>> i5)
      ⦃ x => x.val = if 8 ≤ j.val then T * 2 ^ (j.val - 8) else T / 2 ^ (8 - j.val) ⦄ := by
    by_cases h8 : j ≥ 8#u32
    · have h8' : 8 ≤ j.val := h8
      rw [ite_eq_left h8, ite_eq_left h8']
      refine WP.spec_bind (UScalar.sub_spec (x := j) (y := 8#u32) h8') fun i5 ⟨hi5, _⟩ => ?_
      rw [show (8#u32 : Std.U32).val = 8 from rfl] at hi5
      refine WP.spec_mono (UScalar.ShiftLeft_spec (UScalar.cast .U32 i4) i5 _
        (by rw [hi5, UScalarTy.U32_numBits_eq]; omega) rfl) fun x ⟨hxv, _⟩ => ?_
      rw [hxv, hT, hi5, Nat.shiftLeft_eq, UScalar.size_def, UScalarTy.U32_numBits_eq]
      have : 2 ^ (j.val - 8) ≤ 2 ^ 4 := Nat.pow_le_pow_right (by decide) (by omega)
      exact Nat.mod_eq_of_lt (by
        calc T * 2 ^ (j.val - 8) ≤ T * 2 ^ 4 := Nat.mul_le_mul_left _ this
          _ < 2 ^ 32 := by omega)
    · have h8' : ¬ 8 ≤ j.val := h8
      rw [ite_eq_right h8, ite_eq_right h8']
      refine WP.spec_bind (UScalar.sub_spec (x := 8#u32) (y := j)
        (by rw [show (8#u32 : Std.U32).val = 8 from rfl]; omega)) fun i5 ⟨hi5, _⟩ => ?_
      rw [show (8#u32 : Std.U32).val = 8 from rfl] at hi5
      refine WP.spec_mono (UScalar.ShiftRight_spec (UScalar.cast .U32 i4) i5
        (by rw [hi5, UScalarTy.U32_numBits_eq]; omega)) fun x ⟨hxv, _⟩ => ?_
      rw [hxv, hT, hi5, Nat.shiftRight_eq_div_pow]
  refine WP.spec_bind hx fun x hxv => ?_
  have hT1 : T * T ≤ (2 * t + 1) * 2 ^ 15 := hTdef ▸ Nat.sqrt_le _
  have hT2 : (2 * t + 1) * 2 ^ 15 < (T + 1) * (T + 1) := hTdef ▸ Nat.lt_succ_sqrt _
  have Q0 : 0 < 2 ^ j.val := by positivity
  have good : 1 ≤ x.val ∧ x.val < 2 ^ 16 ∧ x.val * x.val ≤ n.val + 65534 * x.val ∧
      n.val ≤ x.val * x.val + 65534 * x.val := by
    by_cases hs : L + 1 ≤ 8
    · have j0 : j.val = 0 := by rw [hjv, ite_eq_left hs]
      have t0 : t = n.val := by rw [ht, j0, Nat.mul_zero, pow_zero, Nat.div_one]
      have x0 : x.val = Nat.sqrt n.val := by
        rw [hxv, ite_eq_right (by omega), j0, hTdef, t0, show 8 - 0 = 8 from rfl,
          sqrt_div_eq _ _ (by decide)]
        congr 1
        omega
      rw [x0]
      have s1 := Nat.sqrt_le n.val
      have s2 := Nat.lt_succ_sqrt n.val
      have p := Nat.sqrt_pos.mpr (show 0 < n.val by omega)
      have s16 : Nat.sqrt n.val < 2 ^ 16 := Nat.sqrt_lt'.mpr (by omega)
      refine ⟨p, s16, by omega, ?_⟩
      have e : (Nat.sqrt n.val + 1) * (Nat.sqrt n.val + 1) =
          Nat.sqrt n.val * Nat.sqrt n.val + 2 * Nat.sqrt n.val + 1 := by ring
      have s3 : n.val < Nat.sqrt n.val * Nat.sqrt n.val + 2 * Nat.sqrt n.val + 1 := e ▸ s2
      omega
    · have jv : j.val = (L - 6) / 2 := by rw [hjv, ite_eq_right hs]
      have hb1 : x.val * 256 ≤ T * 2 ^ j.val ∧ T * 2 ^ j.val < (x.val + 1) * 256 := by
        rw [hxv]
        split
        · next h8 =>
          have e : T * 2 ^ j.val = T * 2 ^ (j.val - 8) * 256 := by
            rw [mul_assoc, show (256 : ℕ) = 2 ^ 8 from rfl, ← pow_add, Nat.sub_add_cancel h8]
          omega
        · next h8 =>
          have e : (256 : ℕ) = 2 ^ (8 - j.val) * 2 ^ j.val := by
            rw [← pow_add, Nat.sub_add_cancel (by omega)]; rfl
          have d1 := Nat.div_mul_le_self T (2 ^ (8 - j.val))
          have d2 := Nat.lt_div_mul_add (a := T) (show 0 < 2 ^ (8 - j.val) by positivity)
          constructor
          · rw [e, ← mul_assoc]; exact Nat.mul_le_mul_right _ d1
          · rw [e, ← mul_assoc]
            exact Nat.mul_lt_mul_of_pos_right (by rw [Nat.add_mul, one_mul]; omega) Q0
      have ht1 : t * (2 ^ j.val * 2 ^ j.val) ≤ n.val := by
        rw [← tQ]; exact Nat.div_mul_le_self _ _
      have ht2 : n.val < (t + 1) * (2 ^ j.val * 2 ^ j.val) := by
        rw [← tQ, Nat.add_mul, one_mul]; exact Nat.lt_div_mul_add (by positivity)
      have h64 : 64 ≤ t := by
        rw [ht, Nat.le_div_iff_mul_le (by positivity)]
        calc 64 * 2 ^ (2 * j.val) = 2 ^ (6 + 2 * j.val) := by rw [pow_add]; rfl
          _ ≤ 2 ^ L := Nat.pow_le_pow_right (by decide) (by omega)
          _ ≤ n.val := hlo
      exact start_good16 n.val t T x.val (2 ^ j.val) Q0 hn hb1.1 hb1.2 hT1 hT2 ht1 ht2 h64
  obtain ⟨g1, g16, gu, gl⟩ := good
  have nb := newton_bound n.val x.val 65534 g1 gu gl
  refine WP.spec_bind (k16_newton_spec n x (by omega)
    (by rw [UScalar.max_def, UScalarTy.U32_numBits_eq]; omega)) fun x1 hx1 => ?_
  have ge := sqrt_le_newton n.val x.val (by omega)
  rw [← hx1] at ge nb
  have sq : x1.val * x1.val ≤ UScalar.max .U32 := by
    rw [UScalar.max_def, UScalarTy.U32_numBits_eq]; omega
  refine WP.spec_bind (UScalar.mul_spec sq) fun i5 hi5 => ?_
  by_cases hgt : i5 > n
  · have gt : n.val < x1.val * x1.val := hi5 ▸ hgt
    have lt : Nat.sqrt n.val < x1.val := Nat.sqrt_lt.mpr gt
    rw [ite_eq_left hgt]
    refine WP.spec_bind (UScalar.sub_spec (x := x1) (y := 1#u32)
      (by rw [show (1#u32 : Std.U32).val = 1 from rfl]; omega)) fun x2 ⟨hx2, _⟩ => ?_
    rw [show (1#u32 : Std.U32).val = 1 from rfl] at hx2
    unfold fulcrum.kernel.k16.isqrt_loop1
    exact descend_spec n x2 1#u32 rfl (by omega)
      ((Nat.mul_le_mul (by omega) (by omega)).trans sq)
  · have le : x1.val * x1.val ≤ n.val := hi5 ▸ not_lt.mp hgt
    rw [ite_eq_right hgt, WP.spec_ok]
    exact Nat.eq_sqrt.mpr ⟨le, (Nat.lt_succ_sqrt n.val).trans_le
      (Nat.mul_le_mul (Nat.succ_le_succ ge) (Nat.succ_le_succ ge))⟩

/-- `u16::leading_zeros` of a non-zero `n` is `15 - ⌊log₂ n⌋`. -/
theorem U16_leading_zeros_val (n : Std.U16) (hn : n.val ≠ 0) :
    (core.num.U16.leading_zeros n).val = 16 - Nat.log 2 n.val - 1 := by
  have hl : Nat.log 2 n.val < 16 := Nat.log_lt_of_lt_pow hn (by have := n.hmax; exact this)
  have hb : n.bv ≠ 0 := fun h => hn ((congrArg BitVec.toNat h).trans rfl)
  rw [core.num.U16.leading_zeros, UScalar.val, BitVec.leadingZeros, ite_eq_right hb, show n.bv.toNat = n.val from rfl]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _)
    (Nat.lt_of_le_of_lt (Nat.sub_le _ _) (by rw [UScalarTy.U32_numBits_eq]; decide)))

/-- The Newton loop of `k16::isqrt`: `NEWTON_STEPS = 1`, one step from `x > 0`. -/theorem k8_newton_spec (n x : Std.U16) (hx : 0 < x.val)
    (hf : x.val + n.val / x.val ≤ UScalar.max .U16) :
    fulcrum.kernel.k8.isqrt_loop0 n x 0#u32 ⦃ r => r.val = (x.val + n.val / x.val) / 2 ⦄ := by
  have steps : fulcrum.kernel.k8.NEWTON_STEPS = 1#u32 := by
    unfold fulcrum.kernel.k8.NEWTON_STEPS; rfl
  unfold fulcrum.kernel.k8.isqrt_loop0
  refine loop.spec_decr_nat (fun y => 1 - y.2.val)
    (fun y => (y.2.val = 0 ∧ y.1 = x) ∨ (y.2.val = 1 ∧ y.1.val = (x.val + n.val / x.val) / 2))
    _ _ _ ?_ (Or.inl ⟨rfl, rfl⟩)
  rintro ⟨y, i⟩ hinv
  unfold fulcrum.kernel.k8.isqrt_loop0.body
  dsimp only at hinv ⊢
  rw [steps]
  rcases hinv with ⟨hi, rfl⟩ | ⟨hi, hy⟩
  · rw [ite_eq_left (show i < 1#u32 from by show i.val < 1; omega)]
    obtain ⟨q, hq, hqv⟩ := UScalar.div_spec n (y := y) (by omega)
    rw [hq, bind_ok]
    refine WP.spec_bind (UScalar.add_spec (x := y) (y := q) (by rw [hqv]; exact hf)) fun s hs => ?_
    have one : (1#i32 : Std.I32).toNat = 1 := rfl
    refine WP.spec_bind (UScalar.ShiftRight_IScalar_spec s 1#i32 (by decide) (by decide))
      fun x1 ⟨hx1, _⟩ => ?_
    refine WP.spec_bind (UScalar.add_spec (x := i) (y := 1#u32)
      (by rw [hi, show (1#u32 : Std.U32).val = 1 from rfl, UScalar.max_def, UScalarTy.U32_numBits_eq]; decide)) fun i1 hi1 => ?_
    rw [WP.spec_ok]
    refine ⟨Or.inr ⟨by rw [hi1, hi]; rfl, ?_⟩, by rw [hi1, hi]; decide⟩
    rw [hx1, one, Nat.shiftRight_eq_div_pow, hs, hqv, pow_one]
  · rw [ite_eq_right (show ¬ i < 1#u32 from by show ¬ i.val < 1; omega), WP.spec_ok]
    exact hy

/-- `⌊√m⌋ / k = ⌊√(m / k²)⌋`. -/theorem start_good8 (n t T x0 Q : ℕ) (hQ : 0 < Q) (hn : n ≤ 3 * 2 ^ 14)
    (hlo : x0 * 256 ≤ T * Q) (hhi : T * Q < (x0 + 1) * 256)
    (hT1 : T * T ≤ (2 * t + 1) * 2 ^ 15) (hT2 : (2 * t + 1) * 2 ^ 15 < (T + 1) * (T + 1))
    (ht1 : t * (Q * Q) ≤ n) (ht2 : n < (t + 1) * (Q * Q)) (h64 : 64 ≤ t) :
    1 ≤ x0 ∧ x0 < 2 ^ 8 ∧ x0 * x0 ≤ n + 254 * x0 ∧ n ≤ x0 * x0 + 254 * x0 := by
  have U := start_upper n t T x0 Q hlo hT1 ht1
  have L := start_lower n t T x0 Q hQ hhi hT2 ht2
  have T11 : 2 ^ 11 ≤ T := by
    by_contra hc
    have : T + 1 ≤ 2 ^ 11 := by omega
    have := Nat.mul_le_mul this this
    omega
  have q4 : Q * 4 ≤ x0 := by
    have : 2 ^ 11 * Q ≤ T * Q := Nat.mul_le_mul_right _ T11
    omega
  have qq : Q * Q * 16 ≤ x0 * x0 := by
    have := Nat.mul_le_mul q4 q4
    calc Q * Q * 16 = (Q * 4) * (Q * 4) := by ring
      _ ≤ x0 * x0 := this
  have pq : x0 * Q * 4 ≤ x0 * x0 := by
    calc x0 * Q * 4 = x0 * (Q * 4) := by ring
      _ ≤ x0 * x0 := Nat.mul_le_mul_left _ q4
  have xb : x0 < 2 ^ 8 := by
    have : x0 * x0 < 2 ^ 8 * 2 ^ 8 := by omega
    exact Nat.mul_self_lt_mul_self_iff.mp this
  have xx : x0 * x0 ≤ 2 ^ 8 * x0 := Nat.mul_le_mul_right _ xb.le
  have e : ((x0 + 1) * 256 + Q) * ((x0 + 1) * 256 + Q) =
      65536 * (x0 * x0) + 131072 * x0 + 65536 + 512 * (x0 * Q) + 512 * Q + Q * Q := by ring
  refine ⟨by omega, by omega, by omega⟩

/-- One Newton step from `x₀` with `x₀² ≈ n` within `D · x₀`: the sum and the
square of the step are bounded by `n` and `D`. -/theorem k8_isqrt_spec (n : Std.U16) (hn : n.val ≤ 3 * 2 ^ 14) :
    fulcrum.kernel.k8.isqrt n ⦃ r => r.val = Nat.sqrt n.val ⦄ := by
  unfold fulcrum.kernel.k8.isqrt
  by_cases h2 : n < 2#u16
  · rw [ite_eq_left h2, WP.spec_ok]
    have : n.val < 2 := h2
    rcases (show n.val = 0 ∨ n.val = 1 by omega) with h | h <;> rw [h] <;> rfl
  rw [ite_eq_right h2]
  have hn2 : 2 ≤ n.val := Nat.le_of_not_lt h2
  set L := Nat.log 2 n.val with hL
  have hlo : 2 ^ L ≤ n.val := Nat.pow_log_le_self 2 (by omega)
  have hhi : n.val < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by decide) _
  have L15 : L ≤ 15 := by
    by_contra hc
    have : 2 ^ 16 ≤ 2 ^ L := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have L1 : 1 ≤ L := by
    by_contra hc
    have : L = 0 := by omega
    rw [this] at hhi
    omega
  rw [lift, bind_ok]
  have hlz := U16_leading_zeros_val n (by omega)
  refine WP.spec_bind (UScalar.sub_spec (x := core.num.U16.BITS) (y := core.num.U16.leading_zeros n)
    (by rw [hlz, show core.num.U16.BITS.val = 16 from rfl]; omega)) fun bits ⟨hbits, _⟩ => ?_
  rw [hlz, show core.num.U16.BITS.val = 16 from rfl] at hbits
  have hb : bits.val = L + 1 := by omega
  have hj : (if bits ≤ 8#u32 then ok 0#u32 else do
        let i1 ← bits - 7#u32
        i1 / 2#u32) ⦃ j => j.val = if L + 1 ≤ 8 then 0 else (L - 6) / 2 ⦄ := by
    by_cases h8 : bits ≤ 8#u32
    · have h8' : L + 1 ≤ 8 := by have : bits.val ≤ 8 := h8; omega
      rw [ite_eq_left h8, WP.spec_ok, ite_eq_left h8']
      rfl
    · have h8' : ¬ L + 1 ≤ 8 := by have : ¬ bits.val ≤ 8 := h8; omega
      rw [ite_eq_right h8, ite_eq_right h8']
      refine WP.spec_bind (UScalar.sub_spec (x := bits) (y := 7#u32)
        (by rw [show (7#u32 : Std.U32).val = 7 from rfl]; omega)) fun i1 ⟨hi1, _⟩ => ?_
      obtain ⟨q, hq, hqv⟩ := UScalar.div_spec i1 (y := 2#u32) (by decide)
      rw [hq, WP.spec_ok, hqv, hi1, show (7#u32 : Std.U32).val = 7 from rfl,
        show (2#u32 : Std.U32).val = 2 from rfl]
      omega
  refine WP.spec_bind hj fun j hjv => ?_
  refine WP.spec_bind sqrt_start_spec fun a ha => ?_
  have j12 : j.val ≤ 4 := by rw [hjv]; split <;> omega
  refine WP.spec_bind (UScalar.mul_spec (x := 2#u32) (y := j)
    (by rw [show (2#u32 : Std.U32).val = 2 from rfl, UScalar.max_def, UScalarTy.U32_numBits_eq];
        omega)) fun i1 hi1 => ?_
  rw [show (2#u32 : Std.U32).val = 2 from rfl] at hi1
  refine WP.spec_bind (UScalar.ShiftRight_spec n i1 (by rw [hi1, UScalarTy.U16_numBits_eq]; omega))
    fun i2 ⟨hi2, _⟩ => ?_
  rw [hi1, Nat.shiftRight_eq_div_pow] at hi2
  set t := n.val / 2 ^ (2 * j.val) with ht
  have tQ : 2 ^ (2 * j.val) = 2 ^ j.val * 2 ^ j.val := by rw [two_mul, pow_add]
  have tlt : t < 256 := by
    rw [ht, Nat.div_lt_iff_lt_mul (by positivity)]
    calc n.val < 2 ^ (L + 1) := hhi
      _ ≤ 2 ^ (8 + 2 * j.val) := Nat.pow_le_pow_right (by decide) (by rw [hjv]; split <;> omega)
      _ = 256 * 2 ^ (2 * j.val) := by rw [pow_add]; rfl
  rw [lift, bind_ok]
  have um := usize_max_ge
  have c3 : (UScalar.cast .Usize i2).val = t := by
    rw [UScalar.cast_val_eq, hi2]
    exact Nat.mod_eq_of_lt (by rw [UScalarTy.Usize_numBits_eq]; rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> omega)
  refine WP.spec_bind (Array.index_usize_spec a _ (by rw [c3, Array.length, a.property]; exact tlt))
    fun i4 hi4 => ?_
  have hidx : (UScalar.cast .Usize i2).val < a.val.length := by rw [c3, a.property]; exact tlt
  have e1 : i4 = a.val[(UScalar.cast .Usize i2).val]! := by
    rw [hi4]; exact (getElem!_pos a.val _ hidx).symm
  obtain ⟨T, hTdef⟩ : ∃ T, T = Nat.sqrt ((2 * t + 1) * 2 ^ 15) := ⟨_, rfl⟩
  have e2 : (a.val[(UScalar.cast .Usize i2).val]!).val = T := by
    rw [c3]; exact (ha t tlt).trans hTdef.symm
  have T12 : T < 2 ^ 12 := hTdef ▸ Nat.sqrt_lt'.mpr (by omega)
  have hT : i4.val = T := by rw [e1, e2]
  have hx : (if j ≥ 8#u32 then do
        let i5 ← j - 8#u32
        i4 <<< i5
      else do
        let i5 ← 8#u32 - j
        i4 >>> i5)
      ⦃ x => x.val = if 8 ≤ j.val then T * 2 ^ (j.val - 8) else T / 2 ^ (8 - j.val) ⦄ := by
    by_cases h8 : j ≥ 8#u32
    · have h8' : 8 ≤ j.val := h8
      rw [ite_eq_left h8, ite_eq_left h8']
      refine WP.spec_bind (UScalar.sub_spec (x := j) (y := 8#u32) h8') fun i5 ⟨hi5, _⟩ => ?_
      rw [show (8#u32 : Std.U32).val = 8 from rfl] at hi5
      refine WP.spec_mono (UScalar.ShiftLeft_spec (i4) i5 _
        (by rw [hi5, UScalarTy.U16_numBits_eq]; omega) rfl) fun x ⟨hxv, _⟩ => ?_
      rw [hxv, hT, hi5, Nat.shiftLeft_eq, UScalar.size_def, UScalarTy.U16_numBits_eq]
      have : 2 ^ (j.val - 8) ≤ 2 ^ 4 := Nat.pow_le_pow_right (by decide) (by omega)
      exact Nat.mod_eq_of_lt (by
        calc T * 2 ^ (j.val - 8) ≤ T * 2 ^ 4 := Nat.mul_le_mul_left _ this
          _ < 2 ^ 16 := by omega)
    · have h8' : ¬ 8 ≤ j.val := h8
      rw [ite_eq_right h8, ite_eq_right h8']
      refine WP.spec_bind (UScalar.sub_spec (x := 8#u32) (y := j)
        (by rw [show (8#u32 : Std.U32).val = 8 from rfl]; omega)) fun i5 ⟨hi5, _⟩ => ?_
      rw [show (8#u32 : Std.U32).val = 8 from rfl] at hi5
      refine WP.spec_mono (UScalar.ShiftRight_spec (i4) i5
        (by rw [hi5, UScalarTy.U16_numBits_eq]; omega)) fun x ⟨hxv, _⟩ => ?_
      rw [hxv, hT, hi5, Nat.shiftRight_eq_div_pow]
  refine WP.spec_bind hx fun x hxv => ?_
  have hT1 : T * T ≤ (2 * t + 1) * 2 ^ 15 := hTdef ▸ Nat.sqrt_le _
  have hT2 : (2 * t + 1) * 2 ^ 15 < (T + 1) * (T + 1) := hTdef ▸ Nat.lt_succ_sqrt _
  have Q0 : 0 < 2 ^ j.val := by positivity
  have good : 1 ≤ x.val ∧ x.val < 2 ^ 8 ∧ x.val * x.val ≤ n.val + 254 * x.val ∧
      n.val ≤ x.val * x.val + 254 * x.val := by
    by_cases hs : L + 1 ≤ 8
    · have j0 : j.val = 0 := by rw [hjv, ite_eq_left hs]
      have t0 : t = n.val := by rw [ht, j0, Nat.mul_zero, pow_zero, Nat.div_one]
      have x0 : x.val = Nat.sqrt n.val := by
        rw [hxv, ite_eq_right (by omega), j0, hTdef, t0, show 8 - 0 = 8 from rfl,
          sqrt_div_eq _ _ (by decide)]
        congr 1
        omega
      rw [x0]
      have s1 := Nat.sqrt_le n.val
      have s2 := Nat.lt_succ_sqrt n.val
      have p := Nat.sqrt_pos.mpr (show 0 < n.val by omega)
      have s16 : Nat.sqrt n.val < 2 ^ 8 := Nat.sqrt_lt'.mpr (by omega)
      refine ⟨p, s16, by omega, ?_⟩
      have e : (Nat.sqrt n.val + 1) * (Nat.sqrt n.val + 1) =
          Nat.sqrt n.val * Nat.sqrt n.val + 2 * Nat.sqrt n.val + 1 := by ring
      have s3 : n.val < Nat.sqrt n.val * Nat.sqrt n.val + 2 * Nat.sqrt n.val + 1 := e ▸ s2
      omega
    · have jv : j.val = (L - 6) / 2 := by rw [hjv, ite_eq_right hs]
      have hb1 : x.val * 256 ≤ T * 2 ^ j.val ∧ T * 2 ^ j.val < (x.val + 1) * 256 := by
        rw [hxv]
        split
        · next h8 =>
          have e : T * 2 ^ j.val = T * 2 ^ (j.val - 8) * 256 := by
            rw [mul_assoc, show (256 : ℕ) = 2 ^ 8 from rfl, ← pow_add, Nat.sub_add_cancel h8]
          omega
        · next h8 =>
          have e : (256 : ℕ) = 2 ^ (8 - j.val) * 2 ^ j.val := by
            rw [← pow_add, Nat.sub_add_cancel (by omega)]; rfl
          have d1 := Nat.div_mul_le_self T (2 ^ (8 - j.val))
          have d2 := Nat.lt_div_mul_add (a := T) (show 0 < 2 ^ (8 - j.val) by positivity)
          constructor
          · rw [e, ← mul_assoc]; exact Nat.mul_le_mul_right _ d1
          · rw [e, ← mul_assoc]
            exact Nat.mul_lt_mul_of_pos_right (by rw [Nat.add_mul, one_mul]; omega) Q0
      have ht1 : t * (2 ^ j.val * 2 ^ j.val) ≤ n.val := by
        rw [← tQ]; exact Nat.div_mul_le_self _ _
      have ht2 : n.val < (t + 1) * (2 ^ j.val * 2 ^ j.val) := by
        rw [← tQ, Nat.add_mul, one_mul]; exact Nat.lt_div_mul_add (by positivity)
      have h64 : 64 ≤ t := by
        rw [ht, Nat.le_div_iff_mul_le (by positivity)]
        calc 64 * 2 ^ (2 * j.val) = 2 ^ (6 + 2 * j.val) := by rw [pow_add]; rfl
          _ ≤ 2 ^ L := Nat.pow_le_pow_right (by decide) (by omega)
          _ ≤ n.val := hlo
      exact start_good8 n.val t T x.val (2 ^ j.val) Q0 hn hb1.1 hb1.2 hT1 hT2 ht1 ht2 h64
  obtain ⟨g1, g16, gu, gl⟩ := good
  have nb := newton_bound n.val x.val 254 g1 gu gl
  refine WP.spec_bind (k8_newton_spec n x (by omega)
    (by rw [UScalar.max_def, UScalarTy.U16_numBits_eq]; omega)) fun x1 hx1 => ?_
  have ge := sqrt_le_newton n.val x.val (by omega)
  rw [← hx1] at ge nb
  have sq : x1.val * x1.val ≤ UScalar.max .U16 := by
    rw [UScalar.max_def, UScalarTy.U16_numBits_eq]; omega
  refine WP.spec_bind (UScalar.mul_spec sq) fun i5 hi5 => ?_
  by_cases hgt : i5 > n
  · have gt : n.val < x1.val * x1.val := hi5 ▸ hgt
    have lt : Nat.sqrt n.val < x1.val := Nat.sqrt_lt.mpr gt
    rw [ite_eq_left hgt]
    refine WP.spec_bind (UScalar.sub_spec (x := x1) (y := 1#u16)
      (by rw [show (1#u16 : Std.U16).val = 1 from rfl]; omega)) fun x2 ⟨hx2, _⟩ => ?_
    rw [show (1#u16 : Std.U16).val = 1 from rfl] at hx2
    unfold fulcrum.kernel.k8.isqrt_loop1
    exact descend_spec n x2 1#u16 rfl (by omega)
      ((Nat.mul_le_mul (by omega) (by omega)).trans sq)
  · have le : x1.val * x1.val ≤ n.val := hi5 ▸ not_lt.mp hgt
    rw [ite_eq_right hgt, WP.spec_ok]
    exact Nat.eq_sqrt.mpr ⟨le, (Nat.lt_succ_sqrt n.val).trans_le
      (Nat.mul_le_mul (Nat.succ_le_succ ge) (Nat.succ_le_succ ge))⟩

end Fulcrum

end
