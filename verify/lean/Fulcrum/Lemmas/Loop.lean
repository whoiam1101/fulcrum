module

public import Aeneas.Std.Scalar.Bitwise
public import Aeneas.Std.Scalar.Notations
public import Aeneas.Std.Scalar.Ops.Div
public import Aeneas.Std.Scalar.Ops.Mul
public import Aeneas.Std.Scalar.Ops.Sub
import Fulcrum.Lemmas.Nat
import Fulcrum.Lemmas.Scalar

/-!
# Loop specifications shared by every `isqrt`

A loop whose body is done at once returns its start (`loop_done_spec`), the
Newton loop with `NEWTON_STEPS = 1` is one step `(x + ⌊n / x⌋) / 2`
(`newton_once_spec`), and the ending of `isqrt`, the same in every width: from
`x ≥ ⌊√n⌋` whose square fits the type, the square check and the loop that
steps down while `x² > n` stop at `⌊√n⌋` (`descend_spec`, `check_descend_spec`).
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace Fulcrum

/-- A loop whose body is done at once returns its start. -/
theorem loop_done_spec {α β : Type} (f : α × β → Result (ControlFlow (α × β) α))
    (hf : ∀ y i, f (y, i) = ok (ControlFlow.done y)) (x : α) (i : β) :
    loop f (x, i) ⦃ r => r = x ⦄ := by
  refine loop.spec_decr_nat (fun _ => 0) (fun y => y = (x, i)) _ _ _ ?_ rfl
  rintro _ rfl
  rw [hf, WP.spec_ok]

/-- The Newton loop with `NEWTON_STEPS = 1`: one step `(x + ⌊n / x⌋) / 2` from
`x > 0`. -/
theorem newton_once_spec {U} (n x : UScalar U) (steps : Std.U32) (hs : steps = 1#u32)
    (hU : 8 ≤ U.numBits) (hx : 0 < x.val) (hf : x.val + n.val / x.val ≤ UScalar.max U) :
    loop (fun ((y, i) : UScalar U × Std.U32) =>
        if i < steps then do
          let i1 ← n / y
          let i2 ← y + i1
          let y1 ← i2 >>> 1#i32
          let i3 ← i + 1#u32
          ok (ControlFlow.cont (y1, i3))
        else ok (ControlFlow.done y))
      (x, 0#u32) ⦃ r => r.val = (x.val + n.val / x.val) / 2 ⦄ := by
  subst hs
  refine loop.spec_decr_nat (fun y => 1 - y.2.val)
    (fun y => (y.2.val = 0 ∧ y.1 = x) ∨ (y.2.val = 1 ∧ y.1.val = (x.val + n.val / x.val) / 2))
    _ _ _ ?_ (Or.inl ⟨rfl, rfl⟩)
  rintro ⟨y, i⟩ hinv
  dsimp only at hinv ⊢
  rcases hinv with ⟨hi, rfl⟩ | ⟨hi, hy⟩
  · rw [ite_eq_left (show i < 1#u32 from by show i.val < 1; rw [hi]; exact Nat.one_pos)]
    obtain ⟨q, hq, hqv⟩ := UScalar.div_spec n (y := y) (Nat.pos_iff_ne_zero.mp hx)
    rw [hq, bind_ok]
    refine WP.spec_bind (UScalar.add_spec (x := y) (y := q) (by rw [hqv]; exact hf)) fun s hs => ?_
    refine WP.spec_bind (shr_i32_spec s 1#i32 1 rfl (Nat.lt_of_lt_of_le (Nat.le_of_ble_eq_true rfl) hU))
      fun x1 hx1 => ?_
    refine WP.spec_bind (UScalar.add_spec (x := i) (y := 1#u32)
      (by rw [hi, lit_val, U32_max_val]; exact Nat.le_of_ble_eq_true rfl)) fun i1 hi1 => ?_
    rw [WP.spec_ok]
    refine ⟨Or.inr ⟨by rw [hi1, hi]; rfl, ?_⟩, by rw [hi1, hi]; exact Nat.one_pos⟩
    rw [hx1, hs, hqv, pow_one]
  · rw [ite_eq_right (show ¬ i < 1#u32 from by show ¬ i.val < 1; rw [hi]; exact Nat.lt_irrefl 1),
      WP.spec_ok]
    exact hy

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
    refine WP.spec_bind (UScalar.sub_spec (x := y) (y := one) (h1 ▸ Nat.one_le_of_lt lt))
      fun y2 ⟨hy2, _⟩ => ?_
    rw [WP.spec_ok]
    rw [h1] at hy2
    have le : y2.val ≤ y.val := hy2 ▸ Nat.sub_le _ _
    refine ⟨⟨hy2 ▸ Nat.le_sub_one_of_lt lt, (Nat.mul_le_mul le le).trans yf⟩,
      hy2 ▸ Nat.sub_lt (Nat.zero_lt_of_lt lt) Nat.one_pos⟩
  · have le : y.val * y.val ≤ n.val := hi ▸ not_lt.mp hgt
    rw [ite_eq_right hgt, WP.spec_ok]
    exact eq_sqrt_of_le n.val _ le ys

/-- The end of `isqrt` after the Newton steps: from `x ≥ ⌊√n⌋` with `x²` inside the
type, the square check and the final loop give `⌊√n⌋`. -/
theorem check_descend_spec {U} (n x one : UScalar U) (h1 : one.val = 1)
    (hs : Nat.sqrt n.val ≤ x.val) (hf : x.val * x.val ≤ UScalar.max U) :
    (do
      let i ← x * x
      if i > n then do
        let x1 ← x - one
        loop (fun (x1 : UScalar U) => do
            let i ← x1 * x1
            if i > n then do let x2 ← x1 - one; ok (ControlFlow.cont x2)
            else ok (ControlFlow.done x1))
          x1
      else ok x) ⦃ r => r.val = Nat.sqrt n.val ⦄ := by
  refine WP.spec_bind (UScalar.mul_spec hf) fun i hi => ?_
  by_cases hgt : i > n
  · have lt : Nat.sqrt n.val < x.val := Nat.sqrt_lt.mpr (hi ▸ hgt)
    rw [ite_eq_left hgt]
    refine WP.spec_bind (UScalar.sub_spec (x := x) (y := one) (h1 ▸ Nat.one_le_of_lt lt))
      fun x1 ⟨hx1, _⟩ => ?_
    rw [h1] at hx1
    have le : x1.val ≤ x.val := hx1 ▸ Nat.sub_le _ _
    exact descend_spec n x1 one h1 (hx1 ▸ Nat.le_sub_one_of_lt lt) ((Nat.mul_le_mul le le).trans hf)
  · rw [ite_eq_right hgt, WP.spec_ok]
    exact eq_sqrt_of_le n.val _ (hi ▸ not_lt.mp hgt) hs

end Fulcrum

end
