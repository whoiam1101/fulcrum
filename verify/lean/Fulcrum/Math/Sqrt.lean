module

public import Fulcrum.Lemmas.Nat
public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic.Ring

/-!
# The start of `isqrt` of `k8` and `k16`

The entry `T = ⌊√((2t + 1) · 2^15)⌋` of `SQRT_START` at the leading bits
`t = ⌊n / 4^j⌋` of `n`, scaled by `Q = 2^j`, gives a start `x₀` whose square
is within `(P - 2) · x₀` of `n` for every `n ≤ 3 · P² / 4` (`start_good`), with
`P = 2^8` in `k8` and `P = 2^16` in `k16`; the shift `j` keeps `t` below `256`
(`start_shift_le`). No code here.
-/

@[expose] public section

namespace Fulcrum

/-- From the table entry `T ≤ √((2t + 1) · 2^15)` and `x₀ · 2^8 ≤ T · Q`,
`t · Q² ≤ n`: `2 · x₀² ≤ 2 · n + Q²`. -/
theorem start_upper (n t T x0 Q : ℕ) (hx : x0 * 256 ≤ T * Q)
    (hT : T * T ≤ (2 * t + 1) * 2 ^ 15) (ht : t * (Q * Q) ≤ n) : 2 * (x0 * x0) ≤ 2 * n + Q * Q :=
  calc 2 * (x0 * x0) ≤ (2 * t + 1) * (Q * Q) := Nat.le_of_mul_le_mul_right (c := 32768)
        (calc 2 * (x0 * x0) * 32768 = (x0 * 256) * (x0 * 256) := by ring
          _ ≤ (T * Q) * (T * Q) := Nat.mul_le_mul hx hx
          _ = (T * T) * (Q * Q) := by ring
          _ ≤ ((2 * t + 1) * 2 ^ 15) * (Q * Q) := Nat.mul_le_mul_right _ hT
          _ = (2 * t + 1) * (Q * Q) * 32768 := by ring) (Nat.succ_pos _)
    _ = 2 * (t * (Q * Q)) + Q * Q := by ring
    _ ≤ 2 * n + Q * Q := Nat.add_le_add_right (Nat.mul_le_mul_left 2 ht) _

/-- From `(2t + 1) · 2^15 < (T + 1)²`, `T · Q < (x₀ + 1) · 2^8` and
`n < (t + 1) · Q²`: `2^16 · n < ((x₀ + 1) · 2^8 + Q)² + 2^16 · Q²`. -/
theorem start_lower (n t T x0 Q : ℕ) (hQ : 0 < Q) (hx : T * Q < (x0 + 1) * 256)
    (hT : (2 * t + 1) * 2 ^ 15 < (T + 1) * (T + 1)) (ht : n < (t + 1) * (Q * Q)) :
    65536 * n < ((x0 + 1) * 256 + Q) * ((x0 + 1) * 256 + Q) + 65536 * (Q * Q) := by
  have hq : (T + 1) * Q ≤ (x0 + 1) * 256 + Q := by
    rw [Nat.add_mul, one_mul]; exact Nat.add_le_add_right hx.le Q
  have hT' : 65536 * t < (T + 1) * (T + 1) :=
    calc 65536 * t ≤ 65536 * t + 32768 := Nat.le_add_right _ _
      _ = (2 * t + 1) * 2 ^ 15 := by ring
      _ < (T + 1) * (T + 1) := hT
  have h1 : 65536 * (t * (Q * Q)) < ((x0 + 1) * 256 + Q) * ((x0 + 1) * 256 + Q) :=
    calc 65536 * (t * (Q * Q)) = (65536 * t) * (Q * Q) := by ring
      _ < ((T + 1) * (T + 1)) * (Q * Q) := Nat.mul_lt_mul_of_pos_right hT' (Nat.mul_pos hQ hQ)
      _ = ((T + 1) * Q) * ((T + 1) * Q) := by ring
      _ ≤ ((x0 + 1) * 256 + Q) * ((x0 + 1) * 256 + Q) := Nat.mul_le_mul hq hq
  calc 65536 * n < 65536 * ((t + 1) * (Q * Q)) := Nat.mul_lt_mul_of_pos_left ht (Nat.succ_pos _)
    _ = 65536 * (t * (Q * Q)) + 65536 * (Q * Q) := by ring
    _ < _ := Nat.add_lt_add_right h1 _

/-- The start above eight bits: from the table entry `T` at the leading bits
`t ≥ 64` of `n ≤ 3 · P² / 4`, scaled by `Q`, `x₀` is within `(P - 2) · x₀` of
`n` in square. -/
theorem start_close (n t T x0 Q P : ℕ) (hQ : 0 < Q) (hP : 256 ≤ P) (hn : 4 * n ≤ 3 * (P * P))
    (hlo : x0 * 256 ≤ T * Q) (hhi : T * Q < (x0 + 1) * 256)
    (hT1 : T * T ≤ (2 * t + 1) * 2 ^ 15) (hT2 : (2 * t + 1) * 2 ^ 15 < (T + 1) * (T + 1))
    (ht1 : t * (Q * Q) ≤ n) (ht2 : n < (t + 1) * (Q * Q)) (h64 : 64 ≤ t) :
    1 ≤ x0 ∧ x0 < P ∧ x0 * x0 ≤ n + (P - 2) * x0 ∧ n ≤ x0 * x0 + (P - 2) * x0 := by
  have U := start_upper n t T x0 Q hlo hT1 ht1
  have L := start_lower n t T x0 Q hQ hhi hT2 ht2
  have T11 : 2 ^ 11 ≤ T := le_of_not_gt fun hc => absurd hT2 (not_lt.mpr
    (calc (T + 1) * (T + 1) ≤ 2 ^ 11 * 2 ^ 11 := Nat.mul_le_mul hc hc
      _ = 128 * 2 ^ 15 := rfl
      _ ≤ (2 * t + 1) * 2 ^ 15 :=
        Nat.mul_le_mul_right _ (Nat.le_succ_of_le (Nat.mul_le_mul_left 2 h64))))
  have q8 : Q * 8 < x0 + 1 := Nat.lt_of_mul_lt_mul_right (a := 256)
    (calc Q * 8 * 256 = 2 ^ 11 * Q := by ring
      _ ≤ T * Q := Nat.mul_le_mul_right _ T11
      _ < (x0 + 1) * 256 := hhi)
  have q4 : Q * 4 ≤ x0 :=
    (Nat.mul_le_mul_left Q (show 4 ≤ 8 from Nat.le_of_ble_eq_true rfl)).trans (Nat.le_of_lt_succ q8)
  have qq : Q * Q * 16 ≤ x0 * x0 :=
    calc Q * Q * 16 = (Q * 4) * (Q * 4) := by ring
      _ ≤ x0 * x0 := Nat.mul_le_mul q4 q4
  have pq : x0 * Q * 4 ≤ x0 * x0 :=
    calc x0 * Q * 4 = x0 * (Q * 4) := by ring
      _ ≤ x0 * x0 := Nat.mul_le_mul_left _ q4
  have P0 : 0 < P := Nat.lt_of_lt_of_le (Nat.succ_pos 255) hP
  have PP := Nat.mul_pos P0 P0
  have xb : x0 < P := Nat.mul_self_lt_mul_self_iff.mp (by omega)
  have xx : x0 * x0 ≤ P * x0 := Nat.mul_le_mul_right _ xb.le
  have xP : 256 * x0 ≤ P * x0 := Nat.mul_le_mul_right _ hP
  have e : ((x0 + 1) * 256 + Q) * ((x0 + 1) * 256 + Q) =
      65536 * (x0 * x0) + 131072 * x0 + 65536 + 512 * (x0 * Q) + 512 * Q + Q * Q := by ring
  rw [Nat.sub_mul]
  exact ⟨(Nat.mul_pos hQ (Nat.succ_pos 3)).trans_le q4, xb, by omega, by omega⟩

/-- The shift `j` of the start: `2j ≤ ⌊log₂ n⌋`, and the leading bits
`⌊n / 4^j⌋` stay below `256`. -/
theorem start_shift_le (n j : ℕ)
    (hj : j = if Nat.log 2 n + 1 ≤ 8 then 0 else (Nat.log 2 n - 6) / 2) :
    2 * j ≤ Nat.log 2 n ∧ n / 2 ^ (2 * j) < 256 := by
  have hL : Nat.log 2 n + 1 ≤ 8 + 2 * j := by rw [hj]; split <;> omega
  refine ⟨?_, (Nat.div_lt_iff_lt_mul (pow_pos zero_lt_two _)).mpr ?_⟩
  · rw [hj]
    split
    exacts [Nat.zero_le _, (Nat.mul_div_le _ 2).trans (Nat.sub_le _ _)]
  calc n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two _
    _ ≤ 2 ^ (8 + 2 * j) := Nat.pow_le_pow_right zero_lt_two hL
    _ = 256 * 2 ^ (2 * j) := by rw [pow_add]; rfl

/-- The start of `isqrt` of `k8` and `k16`: for `2 ≤ n ≤ 3 · P² / 4`, the
entry `T` at the leading bits of `n`, scaled by `2^j`, is within `(P - 2) · x₀`
of `n` in square. -/
theorem start_good (n j T x P : ℕ) (hP : 256 ≤ P) (h2 : 2 ≤ n) (hn : 4 * n ≤ 3 * (P * P))
    (hj : j = if Nat.log 2 n + 1 ≤ 8 then 0 else (Nat.log 2 n - 6) / 2)
    (hT : T = Nat.sqrt ((2 * (n / 2 ^ (2 * j)) + 1) * 2 ^ 15))
    (hx : x = if 8 ≤ j then T * 2 ^ (j - 8) else T / 2 ^ (8 - j)) :
    1 ≤ x ∧ x < P ∧ x * x ≤ n + (P - 2) * x ∧ n ≤ x * x + (P - 2) * x := by
  have hP2 : 2 ≤ P - 2 := Nat.le_sub_of_add_le ((Nat.le_of_ble_eq_true rfl : 2 + 2 ≤ 256).trans hP)
  have hlo : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (Nat.ne_of_gt (Nat.lt_of_lt_of_le
    Nat.two_pos h2))
  by_cases hs : Nat.log 2 n + 1 ≤ 8
  · have j0 : j = 0 := by rw [hj, ite_eq_left hs]
    have hx' : x = Nat.sqrt n := by
      rw [hx, ite_eq_right (j0 ▸ Nat.not_succ_le_zero 7), hT, j0, sqrt_div_eq _ _ (pow_pos zero_lt_two _)]
      congr 1
      rw [Nat.mul_zero, pow_zero, Nat.div_one, show 2 ^ (8 - 0) * 2 ^ (8 - 0) = 2 * 2 ^ 15 from rfl,
        Nat.mul_div_mul_right _ _ (pow_pos zero_lt_two _), Nat.mul_add_div Nat.two_pos]
      rfl
    have n8 : n < 2 ^ 8 := (Nat.lt_pow_succ_log_self Nat.one_lt_two _).trans_le
      (Nat.pow_le_pow_right zero_lt_two hs)
    rw [hx']
    exact ⟨Nat.sqrt_pos.mpr (Nat.lt_of_lt_of_le Nat.two_pos h2),
      Nat.sqrt_lt.mpr (n8.trans_le (hP.trans (Nat.le_mul_self P))),
      (Nat.sqrt_le n).trans (Nat.le_add_right _ _),
      le_sq_add_of_lt_succ_sq n _ _ hP2 (Nat.lt_succ_sqrt n)⟩
  · have jv : j = (Nat.log 2 n - 6) / 2 := by rw [hj, ite_eq_right hs]
    have Q0 : 0 < 2 ^ j := pow_pos zero_lt_two _
    have tQ : 2 ^ (2 * j) = 2 ^ j * 2 ^ j := by rw [two_mul, pow_add]
    have hb1 : x * 256 ≤ T * 2 ^ j ∧ T * 2 ^ j < (x + 1) * 256 := by
      rw [hx]
      split
      · next h8 =>
        have e : T * 2 ^ j = T * 2 ^ (j - 8) * 256 := by
          rw [mul_assoc, show (256 : ℕ) = 2 ^ 8 from rfl, ← pow_add, Nat.sub_add_cancel h8]
        rw [e, Nat.add_mul, one_mul]
        exact ⟨le_rfl, Nat.lt_add_of_pos_right (Nat.succ_pos _)⟩
      · next h8 =>
        have e : (256 : ℕ) = 2 ^ (8 - j) * 2 ^ j := by
          rw [← pow_add, Nat.sub_add_cancel (Nat.le_of_lt (not_le.mp h8))]; rfl
        rw [e, ← mul_assoc, ← mul_assoc]
        exact ⟨Nat.mul_le_mul_right _ (Nat.div_mul_le_self T _),
          Nat.mul_lt_mul_of_pos_right (lt_succ_div_mul T _ (pow_pos zero_lt_two _)) Q0⟩
    have h64 : 64 ≤ n / 2 ^ (2 * j) := by
      rw [Nat.le_div_iff_mul_le (pow_pos zero_lt_two _)]
      calc 64 * 2 ^ (2 * j) = 2 ^ (6 + 2 * j) := by rw [pow_add]; rfl
        _ ≤ 2 ^ Nat.log 2 n := Nat.pow_le_pow_right zero_lt_two
          (Nat.add_le_of_le_sub' (Nat.le_of_lt_succ ((show 6 < 8 from Nat.le_of_ble_eq_true rfl).trans
            (not_le.mp hs))) (jv ▸ Nat.mul_div_le _ 2))
        _ ≤ n := hlo
    exact start_close n (n / 2 ^ (2 * j)) T x (2 ^ j) P Q0 hP hn hb1.1 hb1.2
      (hT ▸ Nat.sqrt_le _) (hT ▸ Nat.lt_succ_sqrt _) (tQ ▸ Nat.div_mul_le_self _ _)
      (tQ ▸ lt_succ_div_mul _ _ (pow_pos zero_lt_two _)) h64

end Fulcrum

end
