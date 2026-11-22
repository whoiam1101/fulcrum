module

public import Fulcrum.L3.Sqrt.Table
public import Fulcrum.Math.Newton
public import Fulcrum.Math.Sqrt
public import Fulcrum.Lemmas.Loop

/-!
# L3: the steps shared by every `isqrt`

The start of `isqrt` of `k8` and `k16` from `SQRT_START`: the shift `j` and
the lookup at the leading bits (`start_lookup_spec`), and the rest from the
table entry on (`start_tail_spec`): one Newton step from a start whose square
is within `(P - 2) · x₀` of `n` (`newton_bound`), then the square check and the
final loop down to `⌊√n⌋` (`check_descend_spec` of `Lemmas/Loop.lean`).
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace Fulcrum

/-- The start of `isqrt` of `k8` and `k16` up to the table entry: `bits` is
`⌊log₂ n⌋ + 1`, the shift `j` keeps the leading bits `t = ⌊n / 4^j⌋` below
`256`, and the entry of `SQRT_START` at `t` is `⌊√((2t + 1) · 2^15)⌋`. -/
theorem start_lookup_spec {U} {α} (n : UScalar U) (B i : Std.U32)
    (k : Std.U32 → Std.U16 → Result α) (post : α → Prop) (hU : U.numBits < 2 ^ 32)
    (hB : B.val = U.numBits) (h2 : 2 ≤ n.val) (hi : i.val = U.numBits - Nat.log 2 n.val - 1)
    (hk : ∀ (j : Std.U32) (t : Std.U16),
      j.val = (if Nat.log 2 n.val + 1 ≤ 8 then 0 else (Nat.log 2 n.val - 6) / 2) →
      t.val = Nat.sqrt ((2 * (n.val / 2 ^ (2 * j.val)) + 1) * 2 ^ 15) →
      k j t ⦃ r => post r ⦄) :
    (do
      let bits ← B - i
      let j ←
        if bits ≤ 8#u32 then ok 0#u32
        else do
          let i1 ← bits - 7#u32
          i1 / 2#u32
      let a ← fulcrum.kernel.SQRT_START
      let i1 ← 2#u32 * j
      let i2 ← n >>> i1
      let i3 ← lift (UScalar.cast .Usize i2)
      let t ← Array.index_usize a i3
      k j t) ⦃ r => post r ⦄ := by
  have hL : Nat.log 2 n.val < U.numBits :=
    Nat.log_lt_of_lt_pow (Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.two_pos h2)) n.hBounds
  refine WP.spec_bind (UScalar.sub_spec (x := B) (y := i)
    (by rw [hB, hi]; exact Nat.sub_le_sub_right (Nat.sub_le _ _) 1 |>.trans (Nat.sub_le _ _)))
    fun bits ⟨hbits, _⟩ => ?_
  have hb : bits.val = Nat.log 2 n.val + 1 := by
    rw [hbits, hB, hi, Nat.sub_sub, Nat.sub_sub_self hL]
  have hj : (if bits ≤ 8#u32 then ok 0#u32 else do
        let i1 ← bits - 7#u32
        i1 / 2#u32)
      ⦃ j => j.val = if Nat.log 2 n.val + 1 ≤ 8 then 0 else (Nat.log 2 n.val - 6) / 2 ⦄ := by
    by_cases h8 : bits ≤ 8#u32
    · rw [ite_eq_left h8, WP.spec_ok, ite_eq_left (hb ▸ (show bits.val ≤ 8 from h8))]
      rfl
    · have h8' : ¬ Nat.log 2 n.val + 1 ≤ 8 := hb ▸ h8
      rw [ite_eq_right h8, ite_eq_right h8']
      refine WP.spec_bind (UScalar.sub_spec (x := bits) (y := 7#u32)
        (by rw [lit_val]; exact Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.le_succ 7)
          (not_le.mp (show ¬ bits.val ≤ 8 from h8))))) fun i1 ⟨hi1, _⟩ => ?_
      obtain ⟨q, hq, hqv⟩ := UScalar.div_spec i1 (y := 2#u32) (Nat.succ_ne_zero _)
      rw [hq, WP.spec_ok, hqv, hi1, lit_val, lit_val, hb]
      rfl
  refine WP.spec_bind hj fun j hjv => ?_
  obtain ⟨j2, t256⟩ := start_shift_le n.val j.val hjv
  refine WP.spec_bind sqrt_start_spec fun a ha => ?_
  refine WP.spec_bind (UScalar.mul_spec (x := 2#u32) (y := j)
    (by rw [lit_val, U32_max_val]; exact Nat.le_sub_one_of_lt (j2.trans_lt (hL.trans hU))))
    fun i1 hi1 => ?_
  rw [lit_val] at hi1
  refine WP.spec_bind (UScalar.ShiftRight_spec n i1 (by rw [hi1]; exact j2.trans_lt hL))
    fun i2 ⟨hi2, _⟩ => ?_
  rw [hi1, Nat.shiftRight_eq_div_pow] at hi2
  rw [lift, bind_ok]
  have c3 : (UScalar.cast .Usize i2).val = n.val / 2 ^ (2 * j.val) :=
    (usize_cast_val i2 (by rw [hi2]; exact t256.trans (Nat.le_of_ble_eq_true rfl))).trans hi2
  have hidx : (UScalar.cast .Usize i2).val < a.val.length := by rw [c3, a.property]; exact t256
  refine WP.spec_bind (Array.index_usize_spec a _ hidx) fun t ht => ?_
  exact hk j t hjv (by rw [ht, ← getElem!_pos a.val _ hidx, c3]; exact ha _ t256)

/-- The rest of `isqrt` of `k8` and `k16` after the table entry `t`: the start
`t` scaled by `2^j`, one Newton step `newton`, the square check and the final
loop give `⌊√n⌋` for `2 ≤ n ≤ 3 · P² / 4`, where `P` is the half width. -/
theorem start_tail_spec {U} (n t one : UScalar U) (j : Std.U32)
    (newton : UScalar U → Result (UScalar U)) (P : ℕ) (hU : 16 ≤ U.numBits) (h1 : one.val = 1)
    (hP : 256 ≤ P) (h2 : 2 ≤ n.val) (hn : 4 * n.val ≤ 3 * (P * P))
    (hPx : 3 * P ≤ UScalar.max U) (hPD : (P - 2) * (P - 2) + 3 * (P * P) ≤ 4 * UScalar.max U)
    (hj : j.val = if Nat.log 2 n.val + 1 ≤ 8 then 0 else (Nat.log 2 n.val - 6) / 2)
    (ht : t.val = Nat.sqrt ((2 * (n.val / 2 ^ (2 * j.val)) + 1) * 2 ^ 15))
    (hN : ∀ x : UScalar U, 0 < x.val → x.val + n.val / x.val ≤ UScalar.max U →
      newton x ⦃ r => r.val = (x.val + n.val / x.val) / 2 ⦄) :
    (do
      let x ←
        if j ≥ 8#u32 then do
          let i5 ← j - 8#u32
          t <<< i5
        else do
          let i5 ← 8#u32 - j
          t >>> i5
      let x1 ← newton x
      let i ← x1 * x1
      if i > n then do
        let x2 ← x1 - one
        loop (fun (y : UScalar U) => do
            let i ← y * y
            if i > n then do let y2 ← y - one; ok (ControlFlow.cont y2)
            else ok (ControlFlow.done y))
          x2
      else ok x1) ⦃ r => r.val = Nat.sqrt n.val ⦄ := by
  obtain ⟨j2, t256⟩ := start_shift_le n.val j.val hj
  have hL : Nat.log 2 n.val < U.numBits :=
    Nat.log_lt_of_lt_pow (Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.two_pos h2)) n.hBounds
  have T12 : t.val < 2 ^ 12 := by
    rw [ht, Nat.sqrt_lt']
    calc (2 * (n.val / 2 ^ (2 * j.val)) + 1) * 2 ^ 15 < 512 * 2 ^ 15 :=
          Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_of_le (Nat.succ_le_succ
            (Nat.mul_le_mul_left 2 (Nat.le_of_lt_succ t256)))) (pow_pos zero_lt_two _)
      _ = (2 ^ 12) ^ 2 := rfl
  have hx : (if j ≥ 8#u32 then do
        let i5 ← j - 8#u32
        t <<< i5
      else do
        let i5 ← 8#u32 - j
        t >>> i5)
      ⦃ x => x.val =
        if 8 ≤ j.val then t.val * 2 ^ (j.val - 8) else t.val / 2 ^ (8 - j.val) ⦄ := by
    by_cases h8 : j ≥ 8#u32
    · have h8' : 8 ≤ j.val := h8
      rw [ite_eq_left h8, ite_eq_left h8']
      refine WP.spec_bind (UScalar.sub_spec (x := j) (y := 8#u32) h8') fun i5 ⟨hi5, _⟩ => ?_
      rw [lit_val] at hi5
      refine WP.spec_mono (UScalar.ShiftLeft_spec t i5 _
        (by rw [hi5]; exact (Nat.sub_le _ _).trans_lt ((Nat.le_mul_of_pos_left _ Nat.two_pos).trans
          j2 |>.trans_lt hL)) rfl)
        fun x ⟨hxv, _⟩ => ?_
      rw [hxv, hi5, Nat.shiftLeft_eq, UScalar.size_def]
      exact Nat.mod_eq_of_lt
        (calc t.val * 2 ^ (j.val - 8) < 2 ^ 12 * 2 ^ (j.val - 8) :=
              Nat.mul_lt_mul_of_pos_right T12 (pow_pos zero_lt_two _)
          _ = 2 ^ (12 + (j.val - 8)) := (pow_add _ _ _).symm
          _ ≤ 2 ^ U.numBits := Nat.pow_le_pow_right zero_lt_two (by omega))
    · have h8' : ¬ 8 ≤ j.val := h8
      rw [ite_eq_right h8, ite_eq_right h8']
      refine WP.spec_bind (UScalar.sub_spec (x := 8#u32) (y := j)
        (by rw [lit_val]; exact Nat.le_of_lt (not_le.mp h8'))) fun i5 ⟨hi5, _⟩ => ?_
      rw [lit_val] at hi5
      refine WP.spec_mono (UScalar.ShiftRight_spec t i5
        (by rw [hi5]; exact (Nat.sub_le 8 _).trans_lt (Nat.lt_of_lt_of_le (Nat.le_of_ble_eq_true rfl) hU)))
        fun x ⟨hxv, _⟩ => ?_
      rw [hxv, hi5, Nat.shiftRight_eq_div_pow]
  refine WP.spec_bind hx fun x hxv => ?_
  obtain ⟨g1, gP, gu, gl⟩ := start_good n.val j.val t.val x.val P hP h2 hn hj ht hxv
  have nb := newton_bound n.val x.val (P - 2) g1 gu gl
  refine WP.spec_bind (hN x g1 (nb.1.trans (((Nat.add_le_add (Nat.mul_le_mul_left 2 gP.le)
    (Nat.sub_le P 2)).trans_eq (Nat.succ_mul 2 P).symm).trans hPx))) fun x1 hx1 => ?_
  have ge := sqrt_le_newton n.val x.val g1
  rw [← hx1] at ge nb
  exact check_descend_spec n x1 one h1 ge
    (Nat.le_of_mul_le_mul_left (nb.2.trans ((Nat.add_le_add_left hn _).trans hPD)) (Nat.succ_pos 3))

end Fulcrum

end
