module

public import Fulcrum.L3.Div.Magnitude
public import Fulcrum.L3.Sqrt.K8
public import Fulcrum.L3.Sqrt.K16
public import Fulcrum.L3.Sqrt.K32
public import Fulcrum.L3.Sqrt.K64
public import Fulcrum.Math.RoundSqrt

/-!
# L5: square roots and lengths of `kernel::kN`

On the code of every width, as Aeneas extracts it, none fails: `sqrt_round(n)`
is `round √n` (`sqrtRound`, `Math/RoundSqrt.lean`) on the domain of `isqrt`;
`sqrt(a)` is `round √(a · 2^F)` for `a ≥ 0`, `rsqrt(a)` is
`round √(2^(3F) / a)` for `a > 0`, `hypot` and `hypot3` are the rounded
lengths of two and three raw components; `norm_sq` and `sq` are the exact
squares on `u128`, and `cmp_length` is the sign of `a² + b² + c² - k²`.
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace Fulcrum

/-- The body of `kernel::kN::sqrt_round`: `s = isqrt(n)`, plus one when
`n - s² > s`, without overflow. -/
theorem sqrt_round_shape {U} (n : UScalar U) (isq : Result (UScalar U))
    (h : isq ⦃ s => s.val = Nat.sqrt n.val ⦄) :
    (do
        let s ← isq
        let i ← s * s
        let i1 ← n - i
        let i2 ← lift (UScalar.cast_fromBool U (i1 > s))
        s + i2) ⦃ r => r.val = sqrtRound n.val ⦄ := by
  refine WP.spec_bind h fun s hs => ?_
  have sq : s.val * s.val ≤ n.val := hs ▸ Nat.sqrt_le _
  have nmax : n.val ≤ UScalar.max U := by have := n.hmax; rw [UScalar.max_def]; omega
  refine WP.spec_bind (UScalar.mul_spec (sq.trans nmax)) fun i hi => ?_
  refine WP.spec_bind (UScalar.sub_spec (hi ▸ sq)) fun i1 ⟨hi1, _⟩ => ?_
  rw [lift, bind_ok]
  have hc := UScalar.cast_fromBool_val_eq U (decide (i1 > s))
  have e : (decide (i1 > s)).toNat =
      if Nat.sqrt n.val * Nat.sqrt n.val + Nat.sqrt n.val < n.val then 1 else 0 := by
    have : (i1 > s) ↔ Nat.sqrt n.val * Nat.sqrt n.val + Nat.sqrt n.val < n.val := by
      show s.val < i1.val ↔ _
      rw [hi1, hi, hs]; omega
    by_cases g : Nat.sqrt n.val * Nat.sqrt n.val + Nat.sqrt n.val < n.val
    · rw [ite_eq_left g, decide_eq_true (this.mpr g)]; rfl
    · rw [ite_eq_right g, decide_eq_false (fun h => g (this.mp h))]; rfl
  have fit : s.val + (UScalar.cast_fromBool U (decide (i1 > s))).val ≤ UScalar.max U := by
    rw [hc, e, hs]
    have := Nat.sqrt_le_self n.val
    by_cases g : Nat.sqrt n.val * Nat.sqrt n.val + Nat.sqrt n.val < n.val
    · rw [ite_eq_left g]; rw [hs] at sq; omega
    · rw [ite_eq_right g]; rw [hs] at sq; omega
  refine WP.spec_mono (UScalar.add_spec fit) fun r hr => ?_
  rw [hr, hc, e, hs, sqrtRound]

/-- The body of `kernel::kN::sq`: `|m|²` on `u128`. -/
theorem sq_shape {S V} (abs : IScalar S → Result (UScalar V))
    (habs : ∀ x, abs x ⦃ u => u.val = x.val.natAbs ⦄) (hV : V.numBits ≤ 64) (m : IScalar S)
    (hm : m.val.natAbs ≤ 2 ^ 63) :
    (do
        let i ← abs m
        let um ← lift (UScalar.cast .U128 i)
        um * um) ⦃ r => (r.val : ℤ) = m.val ^ 2 ⦄ :=
  abs_cast_bind abs habs (hV.trans (by decide)) m _ _ fun u hu => by
    have : u.val * u.val ≤ UScalar.max .U128 := by
      rw [U128_max_val, hu]
      have := Nat.mul_le_mul hm hm
      have : 2 ^ 63 * 2 ^ 63 < 2 ^ 128 - 1 := by norm_num
      omega
    refine WP.spec_mono (UScalar.mul_spec this) fun r hr => ?_
    rw [hr, hu, Nat.cast_mul, Int.natCast_natAbs, ← sq, sq_abs]

/-- The body of `kernel::kN::norm_sq`: `|a|² + |b|² + |c|²` on `u128`. -/
theorem norm_sq_shape {S V} (abs : IScalar S → Result (UScalar V))
    (habs : ∀ x, abs x ⦃ u => u.val = x.val.natAbs ⦄) (hV : V.numBits ≤ 64) (a b c : IScalar S)
    (ha : a.val.natAbs ≤ 2 ^ 63) (hb : b.val.natAbs ≤ 2 ^ 63) (hc : c.val.natAbs ≤ 2 ^ 63) :
    (do
        let i ← abs a
        let ua ← lift (UScalar.cast .U128 i)
        let i1 ← abs b
        let ub ← lift (UScalar.cast .U128 i1)
        let i2 ← abs c
        let uc ← lift (UScalar.cast .U128 i2)
        let i3 ← ua * ua
        let i4 ← ub * ub
        let i5 ← i3 + i4
        let i6 ← uc * uc
        i5 + i6) ⦃ r => (r.val : ℤ) = a.val ^ 2 + b.val ^ 2 + c.val ^ 2 ⦄ := by
  have hV' : V.numBits ≤ UScalarTy.U128.numBits := hV.trans (by decide)
  refine abs_cast_bind abs habs hV' a _ _ fun ua hua => ?_
  refine abs_cast_bind abs habs hV' b _ _ fun ub hub => ?_
  refine abs_cast_bind abs habs hV' c _ _ fun uc huc => ?_
  have m := U128_max_val
  have pa := Nat.mul_le_mul ha ha
  have pb := Nat.mul_le_mul hb hb
  have pc := Nat.mul_le_mul hc hc
  have P : 2 ^ 63 * 2 ^ 63 = 2 ^ 126 := by norm_num
  have Q : 3 * 2 ^ 126 ≤ 2 ^ 128 - 1 := by norm_num
  refine WP.spec_bind (UScalar.mul_spec (by rw [m, hua]; omega)) fun i3 hi3 => ?_
  refine WP.spec_bind (UScalar.mul_spec (by rw [m, hub]; omega)) fun i4 hi4 => ?_
  refine WP.spec_bind (UScalar.add_spec (by rw [m, hi3, hi4, hua, hub]; omega)) fun i5 hi5 => ?_
  refine WP.spec_bind (UScalar.mul_spec (by rw [m, huc]; omega)) fun i6 hi6 => ?_
  refine WP.spec_mono (UScalar.add_spec (by rw [m, hi5, hi6, hi3, hi4, hua, hub, huc]; omega))
    fun r hr => ?_
  rw [hr, hi5, hi6, hi3, hi4, hua, hub, huc]
  push_cast
  rw [abs_mul_abs_self, abs_mul_abs_self, abs_mul_abs_self]; ring

/-- The body of `kernel::kN::cmp_length`: the sign of `s - k²` from the exact
squares. -/
theorem cmp_length_shape (ns sq : Result Std.U128) (s2 k2 : ℤ)
    (hns : ns ⦃ r => (r.val : ℤ) = s2 ⦄) (hsq : sq ⦃ r => (r.val : ℤ) = k2 ⦄) :
    (do
        let s ← ns
        let k2 ← sq
        if s < k2 then ok (-1)#i8
        else if s > k2 then ok 1#i8
        else ok 0#i8) ⦃ r => r.val = Int.sign (s2 - k2) ⦄ := by
  refine WP.spec_bind hns fun s hs => WP.spec_bind hsq fun k hk => ?_
  by_cases l : s < k
  · have : s2 < k2 := by rw [← hs, ← hk]; exact_mod_cast (show s.val < k.val from l)
    rw [ite_eq_left l, WP.spec_ok, Int.sign_eq_neg_one_of_neg (by omega)]; rfl
  rw [ite_eq_right l]
  by_cases g : s > k
  · have : k2 < s2 := by rw [← hs, ← hk]; exact_mod_cast (show k.val < s.val from g)
    rw [ite_eq_left g, WP.spec_ok, Int.sign_eq_one_of_pos (by omega)]; rfl
  · have : s2 = k2 := by
      rw [← hs, ← hk]
      have := not_lt.mp (show ¬ s.val < k.val from l)
      have := not_lt.mp (show ¬ k.val < s.val from g)
      omega
    rw [ite_eq_right g, WP.spec_ok, this, sub_self, Int.sign_zero]; rfl

/-- An unsigned value below `2^b` keeps its value in the cast to a signed type
of `b + 1` bits. -/
theorem hcast_small {U B} (x : UScalar U) (b : ℕ) (hB : B.numBits = b + 1) (h : x.val < 2 ^ b) :
    (UScalar.hcast B x).val = x.val := by
  rw [UScalar.hcast_val_eq, hB]
  have : ((x.val : ℕ) : ℤ) < 2 ^ b := by exact_mod_cast h
  exact Int.bmod_eq_of_le (by rw [pow_succ]; omega) (by rw [pow_succ]; omega)

/-- The body of `kernel::kN::sqrt`: `a · 2^F` on the unsigned wide type, its
rounded root narrowed back, for `0 ≤ a < 2^b`. -/
theorem sqrt_shape {B U} (a : IScalar B) (sh : Std.I32) (F b D : ℕ) (hB : B.numBits = b + 1)
    (hsh : sh.val = F) (hF : F < U.numBits) (hD : D < 2 ^ U.numBits)
    (h1 : 2 ^ b * 2 ^ F ≤ D) (h2 : 2 ^ b * 2 ^ F ≤ (2 ^ b - 1) * (2 ^ b - 1))
    (sr : UScalar U → Result (UScalar U))
    (hsr : ∀ n : UScalar U, n.val ≤ D → sr n ⦃ r => r.val = sqrtRound n.val ⦄)
    (ha : 0 ≤ a.val) :
    (do
        let i ← lift (IScalar.hcast U a)
        let i1 ← i <<< sh
        let i2 ← sr i1
        ok (UScalar.hcast B i2)) ⦃ r => r.val = round (Real.sqrt ((a.val : ℝ) * 2 ^ F)) ⦄ := by
  have ⟨_, ua⟩ := val_bounds a hB
  have an : a.val.toNat < 2 ^ b := by
    have : a.val < ((2 ^ b : ℕ) : ℤ) := by exact_mod_cast ua
    omega
  have hn : a.val.toNat ≤ UScalar.max U := by
    rw [UScalar.max_def]; have := Nat.le_mul_of_pos_right (2 ^ b) (Nat.two_pow_pos F); omega
  have hmax : a.val ≤ ((UScalar.max U : ℕ) : ℤ) := by
    have := Int.toNat_of_nonneg ha; omega
  refine WP.spec_bind (IScalar.hcast_inBounds_spec U a ⟨ha, hmax⟩) fun i hi => ?_
  have iv : i.val = a.val.toNat := by omega
  have lt : i.val * 2 ^ F < 2 ^ b * 2 ^ F := by
    rw [iv]; exact Nat.mul_lt_mul_of_pos_right an (Nat.two_pow_pos F)
  refine WP.spec_bind (shl_i32_spec i sh F hsh hF (lt.trans_le h1 |>.trans hD)) fun i1 hi1 => ?_
  refine WP.spec_bind (hsr i1 (hi1 ▸ (lt.le.trans h1))) fun i2 hi2 => ?_
  have le := sqrtRound_le i1.val (2 ^ b - 1) (hi1 ▸ lt.trans_le h2)
  rw [WP.spec_ok, hcast_small i2 b hB (by rw [hi2]; have := Nat.one_le_two_pow (n := b); omega),
    hi2, hi1, iv, ← round_sqrt_nat]
  have : ((a.val.toNat : ℕ) : ℝ) = (a.val : ℝ) := by exact_mod_cast Int.toNat_of_nonneg ha
  push_cast
  rw [this]

/-- `|a|² + |b|²` of naturals is `a² + b²`. -/
theorem natAbs_sq_add (a b : ℤ) :
    ((a.natAbs * a.natAbs + b.natAbs * b.natAbs : ℕ) : ℝ) = ((a ^ 2 + b ^ 2 : ℤ) : ℝ) := by
  push_cast [Nat.cast_natAbs, Int.cast_abs]
  rw [abs_mul_abs_self, abs_mul_abs_self]; ring

/-- The body of `kernel::kN::hypot`: the rounded root of `|a|² + |b|²` on the
unsigned wide type, cast to the signed wide type of `w + 1` bits. -/
theorem hypot_shape {S V U W} (abs : IScalar S → Result (UScalar V))
    (habs : ∀ x, abs x ⦃ u => u.val = x.val.natAbs ⦄) (hVU : V.numBits ≤ U.numBits)
    (a b : IScalar S) (k w D : ℕ) (hS : S.numBits = k + 1) (hW : W.numBits = w + 1)
    (hD : D < 2 ^ U.numBits) (h1 : 2 * (2 ^ k * 2 ^ k) ≤ D)
    (h2 : 2 * (2 ^ k * 2 ^ k) < (2 ^ w - 1) * (2 ^ w - 1))
    (sr : UScalar U → Result (UScalar U))
    (hsr : ∀ n : UScalar U, n.val ≤ D → sr n ⦃ r => r.val = sqrtRound n.val ⦄) :
    (do
        let i ← abs a
        let ua ← lift (UScalar.cast U i)
        let i1 ← abs b
        let ub ← lift (UScalar.cast U i1)
        let i2 ← ua * ua
        let i3 ← ub * ub
        let i4 ← i2 + i3
        let i5 ← sr i4
        ok (UScalar.hcast W i5))
      ⦃ r => r.val = round (Real.sqrt ((a.val ^ 2 + b.val ^ 2 : ℤ) : ℝ)) ⦄ := by
  refine abs_cast_bind abs habs hVU a _ _ fun ua hua => ?_
  refine abs_cast_bind abs habs hVU b _ _ fun ub hub => ?_
  have pa := Nat.mul_le_mul (natAbs_le_pow a k hS) (natAbs_le_pow a k hS)
  have pb := Nat.mul_le_mul (natAbs_le_pow b k hS) (natAbs_le_pow b k hS)
  have m : D ≤ UScalar.max U := by rw [UScalar.max_def]; omega
  refine WP.spec_bind (UScalar.mul_spec (by rw [hua]; omega)) fun i2 hi2 => ?_
  refine WP.spec_bind (UScalar.mul_spec (by rw [hub]; omega)) fun i3 hi3 => ?_
  refine WP.spec_bind (UScalar.add_spec (by rw [hi2, hi3, hua, hub]; omega)) fun i4 hi4 => ?_
  have v : i4.val = a.val.natAbs * a.val.natAbs + b.val.natAbs * b.val.natAbs := by
    rw [hi4, hi2, hi3, hua, hub]
  refine WP.spec_bind (hsr i4 (by rw [v]; omega)) fun i5 hi5 => ?_
  have le := sqrtRound_le i4.val (2 ^ w - 1) (by rw [v]; omega)
  rw [WP.spec_ok, hcast_small i5 w hW (by rw [hi5]; have := Nat.one_le_two_pow (n := w); omega),
    hi5, ← natAbs_sq_add, ← v, ← round_sqrt_nat]

/-- The body of `kernel::kN::hypot3`: the rounded root of `|a|² + |b|² + |c|²`
on the unsigned wide type, cast to the signed wide type of `w + 1` bits. -/
theorem hypot3_shape {S V U W} (abs : IScalar S → Result (UScalar V))
    (habs : ∀ x, abs x ⦃ u => u.val = x.val.natAbs ⦄) (hVU : V.numBits ≤ U.numBits)
    (a b c : IScalar S) (k w D : ℕ) (hS : S.numBits = k + 1) (hW : W.numBits = w + 1)
    (hD : D < 2 ^ U.numBits) (h1 : 3 * (2 ^ k * 2 ^ k) ≤ D)
    (h2 : 3 * (2 ^ k * 2 ^ k) < (2 ^ w - 1) * (2 ^ w - 1))
    (sr : UScalar U → Result (UScalar U))
    (hsr : ∀ n : UScalar U, n.val ≤ D → sr n ⦃ r => r.val = sqrtRound n.val ⦄) :
    (do
        let i ← abs a
        let ua ← lift (UScalar.cast U i)
        let i1 ← abs b
        let ub ← lift (UScalar.cast U i1)
        let i2 ← abs c
        let uc ← lift (UScalar.cast U i2)
        let i3 ← ua * ua
        let i4 ← ub * ub
        let i5 ← i3 + i4
        let i6 ← uc * uc
        let i7 ← i5 + i6
        let i8 ← sr i7
        ok (UScalar.hcast W i8))
      ⦃ r => r.val = round (Real.sqrt ((a.val ^ 2 + b.val ^ 2 + c.val ^ 2 : ℤ) : ℝ)) ⦄ := by
  refine abs_cast_bind abs habs hVU a _ _ fun ua hua => ?_
  refine abs_cast_bind abs habs hVU b _ _ fun ub hub => ?_
  refine abs_cast_bind abs habs hVU c _ _ fun uc huc => ?_
  have pa := Nat.mul_le_mul (natAbs_le_pow a k hS) (natAbs_le_pow a k hS)
  have pb := Nat.mul_le_mul (natAbs_le_pow b k hS) (natAbs_le_pow b k hS)
  have pc := Nat.mul_le_mul (natAbs_le_pow c k hS) (natAbs_le_pow c k hS)
  have m : D ≤ UScalar.max U := by rw [UScalar.max_def]; omega
  refine WP.spec_bind (UScalar.mul_spec (by rw [hua]; omega)) fun i3 hi3 => ?_
  refine WP.spec_bind (UScalar.mul_spec (by rw [hub]; omega)) fun i4 hi4 => ?_
  refine WP.spec_bind (UScalar.add_spec (by rw [hi3, hi4, hua, hub]; omega)) fun i5 hi5 => ?_
  refine WP.spec_bind (UScalar.mul_spec (by rw [huc]; omega)) fun i6 hi6 => ?_
  refine WP.spec_bind (UScalar.add_spec (by rw [hi5, hi6, hi3, hi4, hua, hub, huc]; omega))
    fun i7 hi7 => ?_
  have v : i7.val = a.val.natAbs * a.val.natAbs + b.val.natAbs * b.val.natAbs +
      c.val.natAbs * c.val.natAbs := by
    rw [hi7, hi5, hi6, hi3, hi4, hua, hub, huc]
  refine WP.spec_bind (hsr i7 (by rw [v]; omega)) fun i8 hi8 => ?_
  have le := sqrtRound_le i7.val (2 ^ w - 1) (by rw [v]; omega)
  have e : ((i7.val : ℕ) : ℝ) = ((a.val ^ 2 + b.val ^ 2 + c.val ^ 2 : ℤ) : ℝ) := by
    rw [v]; push_cast [Nat.cast_natAbs, Int.cast_abs]
    rw [abs_mul_abs_self, abs_mul_abs_self, abs_mul_abs_self]; ring
  rw [WP.spec_ok, hcast_small i8 w hW (by rw [hi8]; have := Nat.one_le_two_pow (n := w); omega),
    hi8, ← e, ← round_sqrt_nat]

/-- The body of `kernel::kN::rsqrt` for `0 < a < 2^b`: `s = isqrt(⌊2^(3F) / a⌋)`,
plus one when `(2s + 1)² · a < 2^(3F + 2)`, every product inside the unsigned
wide type, narrowed back. -/
theorem rsqrt_shape {B U} (a : IScalar B) (three fF two : Std.I32) (one twoU : UScalar U)
    (F b D : ℕ) (hB : B.numBits = b + 1) (hthree : three.val = 3) (hfF : fF.val = F)
    (htwo : two.val = 2) (hone : one.val = 1) (htwoU : twoU.val = 2)
    (hU : U.numBits ≤ 128) (h3 : 3 * F + 2 < U.numBits) (hD : D < 2 ^ U.numBits)
    (hdom : 2 ^ (3 * F) ≤ D) (hfit : 8 * 2 ^ (3 * F) + 5 * 2 ^ b < 2 ^ U.numBits)
    (hres : 2 ^ (3 * F) < (2 ^ b - 1) * (2 ^ b - 1)) (hab : 2 ^ b ≤ 4 * 2 ^ (3 * F))
    (isq : UScalar U → Result (UScalar U))
    (hisq : ∀ n : UScalar U, n.val ≤ D → isq n ⦃ r => r.val = Nat.sqrt n.val ⦄)
    (ha : 0 < a.val) :
    (do
        let ua ← lift (IScalar.hcast U a)
        let i ← three * fF
        let i1 ← one <<< i
        let i2 ← i1 / ua
        let s ← isq i2
        let i3 ← twoU * s
        let odd ← i3 + one
        let i4 ← odd * odd
        let i5 ← i4 * ua
        let i6 ← i + two
        let i7 ← one <<< i6
        let i8 ← lift (UScalar.cast_fromBool U (i5 < i7))
        let i9 ← s + i8
        ok (UScalar.hcast B i9))
      ⦃ r => r.val = round (Real.sqrt ((2 : ℝ) ^ (3 * F) / a.val)) ⦄ := by
  have ⟨_, ua⟩ := val_bounds a hB
  set A := a.val.toNat with hAdef
  have aA : (A : ℤ) = a.val := Int.toNat_of_nonneg ha.le
  have A1 : 1 ≤ A := by omega
  have Ab : A < 2 ^ b := by
    have : a.val < ((2 ^ b : ℕ) : ℤ) := by exact_mod_cast ua
    omega
  have mx : UScalar.max U = 2 ^ U.numBits - 1 := UScalar.max_def U
  set N := 2 ^ (3 * F) with hN
  have hmax : a.val ≤ ((UScalar.max U : ℕ) : ℤ) := by rw [mx]; omega
  refine WP.spec_bind (IScalar.hcast_inBounds_spec U a ⟨ha.le, hmax⟩) fun u hu => ?_
  have uv : u.val = A := by omega
  have ⟨ml, mu⟩ := in_bounds_of_pow (W := .I32) (m := 31) rfl (x := three.val * fF.val)
    (by rw [hthree, hfF]; omega) (by rw [hthree, hfF]; omega)
  refine WP.spec_bind (IScalar.mul_spec ml mu) fun i hi => ?_
  have iv : i.val = ((3 * F : ℕ) : ℤ) := by rw [hi, hthree, hfF]; push_cast; ring
  have N1 : N < 2 ^ U.numBits := by omega
  refine WP.spec_bind (shl_i32_spec one i (3 * F) iv (by omega) (by rw [hone]; omega))
    fun i1 hi1 => ?_
  rw [hone, one_mul] at hi1
  obtain ⟨i2, hi2, hi2v⟩ := UScalar.div_spec i1 (y := u) (by rw [uv]; omega)
  rw [hi2, bind_ok]
  rw [hi1, uv, ← hN] at hi2v
  have q : N / A ≤ N := Nat.div_le_self _ _
  refine WP.spec_bind (hisq i2 (by rw [hi2v]; omega)) fun s hs => ?_
  rw [hi2v] at hs
  have ss : s.val * s.val ≤ N / A := hs ▸ Nat.sqrt_le _
  have e1 : s.val * s.val * A ≤ N := (Nat.mul_le_mul_right A ss).trans (Nat.div_mul_le_self N A)
  have e2 : s.val * A ≤ s.val * s.val * A + A := by
    have : s.val ≤ s.val * s.val + 1 := by nlinarith
    calc s.val * A ≤ (s.val * s.val + 1) * A := Nat.mul_le_mul_right A this
      _ = s.val * s.val * A + A := by ring
  have e3 : (2 * s.val + 1) * (2 * s.val + 1) * A =
      4 * (s.val * s.val * A) + 4 * (s.val * A) + A := by ring
  have b5 : (2 * s.val + 1) * (2 * s.val + 1) * A ≤ UScalar.max U := by rw [e3, mx]; omega
  have b4 : (2 * s.val + 1) * (2 * s.val + 1) ≤ (2 * s.val + 1) * (2 * s.val + 1) * A :=
    Nat.le_mul_of_pos_right _ A1
  have b2 : 2 * s.val + 1 ≤ (2 * s.val + 1) * (2 * s.val + 1) :=
    Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  refine WP.spec_bind (UScalar.mul_spec (by rw [htwoU]; omega)) fun i3 hi3 => ?_
  refine WP.spec_bind (UScalar.add_spec (by rw [hi3, htwoU, hone]; omega)) fun o ho => ?_
  have ov : o.val = 2 * s.val + 1 := by rw [ho, hi3, htwoU, hone]
  refine WP.spec_bind (UScalar.mul_spec (by rw [ov]; omega)) fun i4 hi4 => ?_
  refine WP.spec_bind (UScalar.mul_spec (by rw [hi4, ov, uv]; omega)) fun i5 hi5 => ?_
  have ⟨al, au⟩ := in_bounds_of_pow (W := .I32) (m := 31) rfl (x := i.val + two.val)
    (by rw [iv, htwo]; omega) (by rw [iv, htwo]; omega)
  refine WP.spec_bind (IScalar.add_spec al au) fun i6 hi6 => ?_
  have i6v : i6.val = ((3 * F + 2 : ℕ) : ℤ) := by rw [hi6, iv, htwo]; push_cast; ring
  have N4 : 2 ^ (3 * F + 2) = 4 * N := by rw [pow_add, hN]; ring
  refine WP.spec_bind (shl_i32_spec one i6 (3 * F + 2) i6v h3 (by rw [hone]; rw [N4]; omega))
    fun i7 hi7 => ?_
  rw [hone, one_mul, N4] at hi7
  rw [lift, bind_ok]
  have hc := UScalar.cast_fromBool_val_eq U (decide (i5 < i7))
  have sb : s.val < 2 ^ b - 1 :=
    Nat.mul_self_lt_mul_self_iff.mp (lt_of_le_of_lt (ss.trans q) hres)
  have hcv : (decide (i5 < i7)).toNat =
      if (2 * s.val + 1) * (2 * s.val + 1) * A < 4 * N then 1 else 0 := by
    have : (i5 < i7) ↔ (2 * s.val + 1) * (2 * s.val + 1) * A < 4 * N := by
      show i5.val < i7.val ↔ _
      rw [hi5, hi4, ov, uv, hi7]
    by_cases g : (2 * s.val + 1) * (2 * s.val + 1) * A < 4 * N
    · rw [ite_eq_left g, decide_eq_true (this.mpr g)]; rfl
    · rw [ite_eq_right g, decide_eq_false (fun h => g (this.mp h))]; rfl
  have bnd : s.val + (UScalar.cast_fromBool U (decide (i5 < i7))).val < 2 ^ b := by
    rw [hc, hcv]; split <;> omega
  refine WP.spec_bind (UScalar.add_spec (by rw [mx]; omega)) fun i9 hi9 => ?_
  rw [WP.spec_ok, hcast_small i9 b hB (hi9 ▸ bnd), hi9, hc, hcv, hs]
  have r := round_sqrt_pow_div (3 * F) A (by omega) (by omega)
  have cA : ((A : ℕ) : ℝ) = (a.val : ℝ) := by exact_mod_cast aA
  rw [Nat.cast_pow, Nat.cast_ofNat, cA] at r
  rw [r, ← hN]
  push_cast
  rfl

/-- `kernel::k8::sqrt_round` is `round √n` on the domain of `isqrt`. -/
theorem k8_sqrt_round_spec (n : Std.U16) (hn : n.val ≤ 3 * 2 ^ 14) :
    fulcrum.kernel.k8.sqrt_round n ⦃ r => r.val = sqrtRound n.val ⦄ := by
  unfold fulcrum.kernel.k8.sqrt_round
  exact sqrt_round_shape n _ (k8_isqrt_spec n hn)

/-- L5 on the code: `kernel::k8::sqrt` is `round √(a · 2^4)` for `a ≥ 0`. -/
theorem k8_sqrt_spec (a : Std.I8) (ha : 0 ≤ a.val) :
    fulcrum.kernel.k8.sqrt a ⦃ r => r.val = round (Real.sqrt ((a.val : ℝ) * 2 ^ 4)) ⦄ :=
  sqrt_shape a 4#i32 4 7 (3 * 2 ^ 14) rfl rfl (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) _
    k8_sqrt_round_spec ha

/-- L5 on the code: `kernel::k8::rsqrt` is `round √(2^12 / a)` for `a > 0`. -/
theorem k8_rsqrt_spec (a : Std.I8) (ha : 0 < a.val) :
    fulcrum.kernel.k8.rsqrt a ⦃ r => r.val = round (Real.sqrt ((2 : ℝ) ^ (3 * 4) / a.val)) ⦄ :=
  rsqrt_shape a 3#i32 4#i32 2#i32 1#u16 2#u16 4 7 (3 * 2 ^ 14) rfl rfl rfl rfl rfl rfl
    (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) _ k8_isqrt_spec ha

/-- L5 on the code: `kernel::k8::hypot` is `round √(a² + b²)`. -/
theorem k8_hypot_spec (a b : Std.I8) :
    fulcrum.kernel.k8.hypot a b ⦃ r => r.val = round (Real.sqrt ((a.val ^ 2 + b.val ^ 2 : ℤ) : ℝ)) ⦄ :=
  hypot_shape _ I8_unsigned_abs_spec (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) a b 7 15 (3 * 2 ^ 14) rfl rfl (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) _
    k8_sqrt_round_spec

/-- L5 on the code: `kernel::k8::hypot3` is `round √(a² + b² + c²)`. -/
theorem k8_hypot3_spec (a b c : Std.I8) :
    fulcrum.kernel.k8.hypot3 a b c
      ⦃ r => r.val = round (Real.sqrt ((a.val ^ 2 + b.val ^ 2 + c.val ^ 2 : ℤ) : ℝ)) ⦄ :=
  hypot3_shape _ I8_unsigned_abs_spec (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) a b c 7 15 (3 * 2 ^ 14) rfl rfl (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) _
    k8_sqrt_round_spec

/-- L5 on the code: `kernel::k8::sq` is `m²` exactly. -/
theorem k8_sq_spec (m : Std.I8) : fulcrum.kernel.k8.sq m ⦃ r => (r.val : ℤ) = m.val ^ 2 ⦄ :=
  sq_shape _ I8_unsigned_abs_spec (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) m
    ((natAbs_le_pow m 7 rfl).trans (Nat.pow_le_pow_right two_pos (by norm_num [UScalarTy.numBits, IScalarTy.numBits])))

/-- L5 on the code: `kernel::k8::norm_sq` is `a² + b² + c²` exactly. -/
theorem k8_norm_sq_spec (a b c : Std.I8) :
    fulcrum.kernel.k8.norm_sq a b c ⦃ r => (r.val : ℤ) = a.val ^ 2 + b.val ^ 2 + c.val ^ 2 ⦄ :=
  norm_sq_shape _ I8_unsigned_abs_spec (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) a b c
    ((natAbs_le_pow a 7 rfl).trans (Nat.pow_le_pow_right two_pos (by norm_num [UScalarTy.numBits, IScalarTy.numBits])))
    ((natAbs_le_pow b 7 rfl).trans (Nat.pow_le_pow_right two_pos (by norm_num [UScalarTy.numBits, IScalarTy.numBits])))
    ((natAbs_le_pow c 7 rfl).trans (Nat.pow_le_pow_right two_pos (by norm_num [UScalarTy.numBits, IScalarTy.numBits])))

/-- L5 on the code: `kernel::k8::cmp_length` is the sign of `a² + b² + c² - k²`. -/
theorem k8_cmp_length_spec (a b c k : Std.I8) :
    fulcrum.kernel.k8.cmp_length a b c k
      ⦃ r => r.val = Int.sign (a.val ^ 2 + b.val ^ 2 + c.val ^ 2 - k.val ^ 2) ⦄ :=
  cmp_length_shape _ _ _ _ (k8_norm_sq_spec a b c) (k8_sq_spec k)

/-- `kernel::k16::sqrt_round` is `round √n` on the domain of `isqrt`. -/
theorem k16_sqrt_round_spec (n : Std.U32) (hn : n.val ≤ 3 * 2 ^ 30) :
    fulcrum.kernel.k16.sqrt_round n ⦃ r => r.val = sqrtRound n.val ⦄ := by
  unfold fulcrum.kernel.k16.sqrt_round
  exact sqrt_round_shape n _ (k16_isqrt_spec n hn)

/-- L5 on the code: `kernel::k16::sqrt` is `round √(a · 2^8)` for `a ≥ 0`. -/
theorem k16_sqrt_spec (a : Std.I16) (ha : 0 ≤ a.val) :
    fulcrum.kernel.k16.sqrt a ⦃ r => r.val = round (Real.sqrt ((a.val : ℝ) * 2 ^ 8)) ⦄ :=
  sqrt_shape a 8#i32 8 15 (3 * 2 ^ 30) rfl rfl (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) _
    k16_sqrt_round_spec ha

/-- L5 on the code: `kernel::k16::rsqrt` is `round √(2^24 / a)` for `a > 0`. -/
theorem k16_rsqrt_spec (a : Std.I16) (ha : 0 < a.val) :
    fulcrum.kernel.k16.rsqrt a ⦃ r => r.val = round (Real.sqrt ((2 : ℝ) ^ (3 * 8) / a.val)) ⦄ :=
  rsqrt_shape a 3#i32 8#i32 2#i32 1#u32 2#u32 8 15 (3 * 2 ^ 30) rfl rfl rfl rfl rfl rfl
    (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) _ k16_isqrt_spec ha

/-- L5 on the code: `kernel::k16::hypot` is `round √(a² + b²)`. -/
theorem k16_hypot_spec (a b : Std.I16) :
    fulcrum.kernel.k16.hypot a b ⦃ r => r.val = round (Real.sqrt ((a.val ^ 2 + b.val ^ 2 : ℤ) : ℝ)) ⦄ :=
  hypot_shape _ I16_unsigned_abs_spec (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) a b 15 31 (3 * 2 ^ 30) rfl rfl (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) _
    k16_sqrt_round_spec

/-- L5 on the code: `kernel::k16::hypot3` is `round √(a² + b² + c²)`. -/
theorem k16_hypot3_spec (a b c : Std.I16) :
    fulcrum.kernel.k16.hypot3 a b c
      ⦃ r => r.val = round (Real.sqrt ((a.val ^ 2 + b.val ^ 2 + c.val ^ 2 : ℤ) : ℝ)) ⦄ :=
  hypot3_shape _ I16_unsigned_abs_spec (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) a b c 15 31 (3 * 2 ^ 30) rfl rfl (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) _
    k16_sqrt_round_spec

/-- L5 on the code: `kernel::k16::sq` is `m²` exactly. -/
theorem k16_sq_spec (m : Std.I16) : fulcrum.kernel.k16.sq m ⦃ r => (r.val : ℤ) = m.val ^ 2 ⦄ :=
  sq_shape _ I16_unsigned_abs_spec (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) m
    ((natAbs_le_pow m 15 rfl).trans (Nat.pow_le_pow_right two_pos (by norm_num [UScalarTy.numBits, IScalarTy.numBits])))

/-- L5 on the code: `kernel::k16::norm_sq` is `a² + b² + c²` exactly. -/
theorem k16_norm_sq_spec (a b c : Std.I16) :
    fulcrum.kernel.k16.norm_sq a b c ⦃ r => (r.val : ℤ) = a.val ^ 2 + b.val ^ 2 + c.val ^ 2 ⦄ :=
  norm_sq_shape _ I16_unsigned_abs_spec (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) a b c
    ((natAbs_le_pow a 15 rfl).trans (Nat.pow_le_pow_right two_pos (by norm_num [UScalarTy.numBits, IScalarTy.numBits])))
    ((natAbs_le_pow b 15 rfl).trans (Nat.pow_le_pow_right two_pos (by norm_num [UScalarTy.numBits, IScalarTy.numBits])))
    ((natAbs_le_pow c 15 rfl).trans (Nat.pow_le_pow_right two_pos (by norm_num [UScalarTy.numBits, IScalarTy.numBits])))

/-- L5 on the code: `kernel::k16::cmp_length` is the sign of `a² + b² + c² - k²`. -/
theorem k16_cmp_length_spec (a b c k : Std.I16) :
    fulcrum.kernel.k16.cmp_length a b c k
      ⦃ r => r.val = Int.sign (a.val ^ 2 + b.val ^ 2 + c.val ^ 2 - k.val ^ 2) ⦄ :=
  cmp_length_shape _ _ _ _ (k16_norm_sq_spec a b c) (k16_sq_spec k)

/-- `kernel::k32::sqrt_round` is `round √n` on the domain of `isqrt`. -/
theorem k32_sqrt_round_spec (n : Std.U64) (hn : n.val ≤ 3 * 2 ^ 62) :
    fulcrum.kernel.k32.sqrt_round n ⦃ r => r.val = sqrtRound n.val ⦄ := by
  unfold fulcrum.kernel.k32.sqrt_round
  exact sqrt_round_shape n _ (k32_isqrt_spec n hn)

/-- L5 on the code: `kernel::k32::sqrt` is `round √(a · 2^16)` for `a ≥ 0`. -/
theorem k32_sqrt_spec (a : Std.I32) (ha : 0 ≤ a.val) :
    fulcrum.kernel.k32.sqrt a ⦃ r => r.val = round (Real.sqrt ((a.val : ℝ) * 2 ^ 16)) ⦄ :=
  sqrt_shape a 16#i32 16 31 (3 * 2 ^ 62) rfl rfl (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) _
    k32_sqrt_round_spec ha

/-- L5 on the code: `kernel::k32::rsqrt` is `round √(2^48 / a)` for `a > 0`. -/
theorem k32_rsqrt_spec (a : Std.I32) (ha : 0 < a.val) :
    fulcrum.kernel.k32.rsqrt a ⦃ r => r.val = round (Real.sqrt ((2 : ℝ) ^ (3 * 16) / a.val)) ⦄ :=
  rsqrt_shape a 3#i32 16#i32 2#i32 1#u64 2#u64 16 31 (3 * 2 ^ 62) rfl rfl rfl rfl rfl rfl
    (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) _ k32_isqrt_spec ha

/-- L5 on the code: `kernel::k32::hypot` is `round √(a² + b²)`. -/
theorem k32_hypot_spec (a b : Std.I32) :
    fulcrum.kernel.k32.hypot a b ⦃ r => r.val = round (Real.sqrt ((a.val ^ 2 + b.val ^ 2 : ℤ) : ℝ)) ⦄ :=
  hypot_shape _ I32_unsigned_abs_spec (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) a b 31 63 (3 * 2 ^ 62) rfl rfl (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) _
    k32_sqrt_round_spec

/-- L5 on the code: `kernel::k32::hypot3` is `round √(a² + b² + c²)`. -/
theorem k32_hypot3_spec (a b c : Std.I32) :
    fulcrum.kernel.k32.hypot3 a b c
      ⦃ r => r.val = round (Real.sqrt ((a.val ^ 2 + b.val ^ 2 + c.val ^ 2 : ℤ) : ℝ)) ⦄ :=
  hypot3_shape _ I32_unsigned_abs_spec (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) a b c 31 63 (3 * 2 ^ 62) rfl rfl (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) _
    k32_sqrt_round_spec

/-- L5 on the code: `kernel::k32::sq` is `m²` exactly. -/
theorem k32_sq_spec (m : Std.I32) : fulcrum.kernel.k32.sq m ⦃ r => (r.val : ℤ) = m.val ^ 2 ⦄ :=
  sq_shape _ I32_unsigned_abs_spec (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) m
    ((natAbs_le_pow m 31 rfl).trans (Nat.pow_le_pow_right two_pos (by norm_num [UScalarTy.numBits, IScalarTy.numBits])))

/-- L5 on the code: `kernel::k32::norm_sq` is `a² + b² + c²` exactly. -/
theorem k32_norm_sq_spec (a b c : Std.I32) :
    fulcrum.kernel.k32.norm_sq a b c ⦃ r => (r.val : ℤ) = a.val ^ 2 + b.val ^ 2 + c.val ^ 2 ⦄ :=
  norm_sq_shape _ I32_unsigned_abs_spec (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) a b c
    ((natAbs_le_pow a 31 rfl).trans (Nat.pow_le_pow_right two_pos (by norm_num [UScalarTy.numBits, IScalarTy.numBits])))
    ((natAbs_le_pow b 31 rfl).trans (Nat.pow_le_pow_right two_pos (by norm_num [UScalarTy.numBits, IScalarTy.numBits])))
    ((natAbs_le_pow c 31 rfl).trans (Nat.pow_le_pow_right two_pos (by norm_num [UScalarTy.numBits, IScalarTy.numBits])))

/-- L5 on the code: `kernel::k32::cmp_length` is the sign of `a² + b² + c² - k²`. -/
theorem k32_cmp_length_spec (a b c k : Std.I32) :
    fulcrum.kernel.k32.cmp_length a b c k
      ⦃ r => r.val = Int.sign (a.val ^ 2 + b.val ^ 2 + c.val ^ 2 - k.val ^ 2) ⦄ :=
  cmp_length_shape _ _ _ _ (k32_norm_sq_spec a b c) (k32_sq_spec k)

/-- `kernel::k64::sqrt_round` is `round √n` on the domain of `isqrt`. -/
theorem k64_sqrt_round_spec (n : Std.U128) (hn : n.val ≤ 3 * 2 ^ 126) :
    fulcrum.kernel.k64.sqrt_round n ⦃ r => r.val = sqrtRound n.val ⦄ := by
  unfold fulcrum.kernel.k64.sqrt_round
  exact sqrt_round_shape n _ (k64_isqrt_spec n hn)

/-- L5 on the code: `kernel::k64::sqrt` is `round √(a · 2^32)` for `a ≥ 0`. -/
theorem k64_sqrt_spec (a : Std.I64) (ha : 0 ≤ a.val) :
    fulcrum.kernel.k64.sqrt a ⦃ r => r.val = round (Real.sqrt ((a.val : ℝ) * 2 ^ 32)) ⦄ :=
  sqrt_shape a 32#i32 32 63 (3 * 2 ^ 126) rfl rfl (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) _
    k64_sqrt_round_spec ha

/-- L5 on the code: `kernel::k64::rsqrt` is `round √(2^96 / a)` for `a > 0`. -/
theorem k64_rsqrt_spec (a : Std.I64) (ha : 0 < a.val) :
    fulcrum.kernel.k64.rsqrt a ⦃ r => r.val = round (Real.sqrt ((2 : ℝ) ^ (3 * 32) / a.val)) ⦄ :=
  rsqrt_shape a 3#i32 32#i32 2#i32 1#u128 2#u128 32 63 (3 * 2 ^ 126) rfl rfl rfl rfl rfl rfl
    (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) _ k64_isqrt_spec ha

/-- L5 on the code: `kernel::k64::hypot` is `round √(a² + b²)`. -/
theorem k64_hypot_spec (a b : Std.I64) :
    fulcrum.kernel.k64.hypot a b ⦃ r => r.val = round (Real.sqrt ((a.val ^ 2 + b.val ^ 2 : ℤ) : ℝ)) ⦄ :=
  hypot_shape _ I64_unsigned_abs_spec (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) a b 63 127 (3 * 2 ^ 126) rfl rfl (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) _
    k64_sqrt_round_spec

/-- L5 on the code: `kernel::k64::hypot3` is `round √(a² + b² + c²)`. -/
theorem k64_hypot3_spec (a b c : Std.I64) :
    fulcrum.kernel.k64.hypot3 a b c
      ⦃ r => r.val = round (Real.sqrt ((a.val ^ 2 + b.val ^ 2 + c.val ^ 2 : ℤ) : ℝ)) ⦄ :=
  hypot3_shape _ I64_unsigned_abs_spec (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) a b c 63 127 (3 * 2 ^ 126) rfl rfl (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) _
    k64_sqrt_round_spec

/-- L5 on the code: `kernel::k64::sq` is `m²` exactly. -/
theorem k64_sq_spec (m : Std.I64) : fulcrum.kernel.k64.sq m ⦃ r => (r.val : ℤ) = m.val ^ 2 ⦄ :=
  sq_shape _ I64_unsigned_abs_spec (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) m
    ((natAbs_le_pow m 63 rfl).trans (Nat.pow_le_pow_right two_pos (by norm_num [UScalarTy.numBits, IScalarTy.numBits])))

/-- L5 on the code: `kernel::k64::norm_sq` is `a² + b² + c²` exactly. -/
theorem k64_norm_sq_spec (a b c : Std.I64) :
    fulcrum.kernel.k64.norm_sq a b c ⦃ r => (r.val : ℤ) = a.val ^ 2 + b.val ^ 2 + c.val ^ 2 ⦄ :=
  norm_sq_shape _ I64_unsigned_abs_spec (by norm_num [UScalarTy.numBits, IScalarTy.numBits]) a b c
    ((natAbs_le_pow a 63 rfl).trans (Nat.pow_le_pow_right two_pos (by norm_num [UScalarTy.numBits, IScalarTy.numBits])))
    ((natAbs_le_pow b 63 rfl).trans (Nat.pow_le_pow_right two_pos (by norm_num [UScalarTy.numBits, IScalarTy.numBits])))
    ((natAbs_le_pow c 63 rfl).trans (Nat.pow_le_pow_right two_pos (by norm_num [UScalarTy.numBits, IScalarTy.numBits])))

/-- L5 on the code: `kernel::k64::cmp_length` is the sign of `a² + b² + c² - k²`. -/
theorem k64_cmp_length_spec (a b c k : Std.I64) :
    fulcrum.kernel.k64.cmp_length a b c k
      ⦃ r => r.val = Int.sign (a.val ^ 2 + b.val ^ 2 + c.val ^ 2 - k.val ^ 2) ⦄ :=
  cmp_length_shape _ _ _ _ (k64_norm_sq_spec a b c) (k64_sq_spec k)

end Fulcrum

end
