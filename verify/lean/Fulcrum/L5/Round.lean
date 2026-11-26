module

public import Fulcrum.Kernel.Funs
public import Fulcrum.Spec
import Fulcrum.L3.Mul
import Fulcrum.L5.Shift
import Fulcrum.Lemmas.Int
import Fulcrum.Lemmas.Scalar
import Fulcrum.Math.Round

/-!
# L5: `kernel::kN::ceil`, `kernel::kN::round_half_away`, `kernel::kN::round_ties_even`

The integer roundings of `round.rs` on the wide type of every width, as Aeneas
extracts them: none fails. `w & !MASK` with `MASK = 2^F - 1` is
`⌊w / 2^F⌋ · 2^F` and `w & MASK` is `w mod 2^F` for every signed `w`
(`mask_split`), so `ceil` is `⌈a / 2^F⌉ · 2^F`, `round_half_away` rounds the
magnitude to nearest with ties up and keeps the sign, and `round_ties_even`
returns the multiple of `2^F` nearest to `a`, the even one on a tie.
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace Fulcrum

/-- `x & !M` is `⌊x / 2^F⌋ · 2^F` and `x & M` is `x mod 2^F` for a signed bit
vector `x` and the mask `M = 2^F - 1` below the sign bit. -/
theorem mask_split {w : ℕ} (x M : BitVec w) (F : ℕ) (hM : M.toNat = 2 ^ F - 1) (hF : F < w)
    (top : M.msb = false) :
    (x &&& ~~~M).toInt = x.toInt / 2 ^ F * 2 ^ F ∧ (x &&& M).toInt = x.toInt % 2 ^ F := by
  have hlo : (x &&& M).toNat = x.toNat % 2 ^ F := by
    rw [BitVec.toNat_and, hM, Nat.and_two_pow_sub_one_eq_mod]
  have hor : (x &&& ~~~M) ||| (x &&& M) = x := by
    rw [← BitVec.and_or_distrib_left, BitVec.not_or_self, BitVec.and_allOnes]
  have hand : ((x &&& ~~~M) &&& (x &&& M)).toNat = 0 := by
    have : (x &&& ~~~M) &&& (x &&& M) = 0#w := by
      rw [BitVec.and_assoc, BitVec.and_comm x M, ← BitVec.and_assoc (~~~M), BitVec.not_and_self]
      simp
    rw [this, BitVec.toNat_ofNat, Nat.zero_mod]
  have ⟨s1, s2⟩ := bits_split (x &&& ~~~M).toNat (x &&& M).toNat
  have hn : (x &&& ~~~M).toNat ||| (x &&& M).toNat = x.toNat := by rw [← BitVec.toNat_or, hor]
  have ha : (x &&& ~~~M).toNat &&& (x &&& M).toNat = 0 := by rw [← BitVec.toNat_and]; exact hand
  have dv : (2 : ℤ) ^ F ∣ 2 ^ w := pow_dvd_pow 2 hF.le
  have mlo : (x &&& M).msb = false := by rw [BitVec.msb_and, top, Bool.and_false]
  have mhi : (x &&& ~~~M).msb = x.msb := by
    rw [BitVec.msb_and, BitVec.msb_not, top, decide_eq_true (by omega : 0 < w)]; simp
  have emod : x.toInt % 2 ^ F = ((x.toNat % 2 ^ F : ℕ) : ℤ) := by
    rw [BitVec.toInt_eq_msb_cond, Int.natCast_emod]
    push_cast
    split
    · exact Int.ModEq.eq (Int.modEq_iff_dvd.mpr (by rw [sub_sub_cancel]; exact dv))
    · rfl
  have e := Int.ediv_mul_add_emod x.toInt (2 ^ F)
  have hx := BitVec.toInt_eq_msb_cond x
  refine ⟨?_, ?_⟩
  · rw [BitVec.toInt_eq_msb_cond (x &&& ~~~M), mhi]
    have : ((x &&& ~~~M).toNat : ℤ) = x.toNat - ((x.toNat % 2 ^ F : ℕ) : ℤ) := by (clear * - hlo s1 s2 hn ha; omega)
    rw [this, ← emod]
    split <;> simp_all <;> linarith only [e]
  · rw [BitVec.toInt_eq_msb_cond (x &&& M), mlo, emod, hlo]; rfl

/-- `w & !MASK` and `w & MASK` of a signed `w` of `m + 1` bits, for
`MASK = 2^F - 1` with `F < m`. -/
theorem mask_val {W} (x mask : IScalar W) (F m : ℕ) (hW : W.numBits = m + 1) (hF : F < m)
    (hm : mask.val = 2 ^ F - 1) :
    (x &&& ~~~mask).val = x.val / 2 ^ F * 2 ^ F ∧ (x &&& mask).val = x.val % 2 ^ F := by
  have p1 : (1 : ℤ) ≤ 2 ^ F := one_le_pow₀ one_le_two
  have pl : (2 : ℤ) ^ F < 2 ^ m := pow_lt_pow_right₀ one_lt_two hF
  have hc := BitVec.toInt_eq_msb_cond mask.bv
  have lt := mask.bv.isLt
  have ht : (mask.bv.toNat : ℤ) = 2 ^ F - 1 := by
    have hv : mask.bv.toInt = 2 ^ F - 1 := hm
    have lt' : (mask.bv.toNat : ℤ) < ((2 ^ W.numBits : ℕ) : ℤ) := by exact_mod_cast lt
    split at hc
    · omega
    · omega
  have hM : mask.bv.toNat = 2 ^ F - 1 := by
    have : ((2 ^ F - 1 : ℕ) : ℤ) = 2 ^ F - 1 := by
      rw [Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
    omega
  have top : mask.bv.msb = false := by
    have e : W.numBits - 1 = m := by omega
    have h2 : 2 ^ F - 1 < 2 ^ m :=
      Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.pow_lt_pow_right (a := 2) Nat.one_lt_two hF)
    rw [BitVec.msb_eq_decide, e, decide_eq_false_iff_not, not_le, hM]
    exact h2
  exact mask_split x.bv mask.bv F hM (hW ▸ Nat.lt_succ_of_lt hF) top

/-- The body of `kernel::kN::ONE`: `1 << F` is `2^F` for `F` below the top bit. -/
theorem one_shape {W} (f : Std.I32) (one : IScalar W) (F m : ℕ) (hf : f.val = F)
    (hone : one.val = 1) (hW : W.numBits = m + 1) (hF : F < m) :
    (one <<< f) ⦃ h => h.val = 2 ^ F ⦄ := by
  refine WP.spec_mono (IScalar.ShiftLeft_IScalar_spec one f (hf ▸ Int.natCast_nonneg F)
    (hf ▸ Int.ofNat_lt.mpr (hW ▸ Nat.lt_succ_of_lt hF))) fun h ⟨hv, _⟩ => ?_
  rw [hv, IScalar.toNat, hf, Int.toNat_natCast, hone, Int.shiftLeft_eq, one_mul, hW]
  exact (wrap_eq_self_iff m _).2 ⟨(neg_nonpos.mpr (pow_pos zero_lt_two m).le).trans
    (pow_pos zero_lt_two F).le, Int.le_sub_one_of_lt (pow_lt_pow_right₀ one_lt_two hF)⟩

/-- The body of `kernel::kN::MASK`: `ONE - 1` is `2^F - 1`. -/
theorem mask_shape {W} (o : Result (IScalar W)) (one : IScalar W) (F : ℕ)
    (ho : o ⦃ h => h.val = 2 ^ F ⦄) (hone : one.val = 1) :
    (do let i ← o; i - one) ⦃ h => h.val = 2 ^ F - 1 ⦄ := by
  refine WP.spec_bind ho fun i hi => ?_
  have p1 := one_le_pow₀ (M₀ := ℤ) one_le_two (n := F)
  have lo : IScalar.min W ≤ i.val - one.val := by
    have hm : IScalar.min W ≤ 0 := by
      rw [IScalar.min_def]; exact neg_nonpos.mpr (pow_pos zero_lt_two _).le
    rw [hi, hone]; linarith only [p1, hm]
  have hi' : i.val - one.val ≤ IScalar.max W := by
    have := i.hmax; rw [IScalar.max_def, hone]; linarith only [this]
  refine WP.spec_mono (IScalar.sub_spec lo hi') fun r hr => ?_
  rw [hr, hi, hone]

/-- `⌈x / 2^F⌉ = ⌊(x + 2^F - 1) / 2^F⌋`. -/
theorem ceil_exact (x : ℤ) (F : ℕ) : ⌈exact F x⌉ = (x + 2 ^ F - 1) / 2 ^ F := by
  have hP : (0 : ℤ) < 2 ^ F := pow_pos zero_lt_two F
  have e : exact F x = ((x : ℤ) : ℚ) / ((2 ^ F : ℕ) : ℚ) := by
    rw [exact, Nat.cast_pow, Nat.cast_ofNat]
  rw [e, Rat.ceil_intCast_div_natCast, Nat.cast_pow, Nat.cast_ofNat]
  have h1 := Int.ediv_mul_add_emod (x + 2 ^ F - 1) (2 ^ F)
  have h2 := Int.emod_nonneg (x + 2 ^ F - 1) hP.ne'
  have h3 := Int.emod_lt_of_pos (x + 2 ^ F - 1) hP
  have : -x / 2 ^ F = -((x + 2 ^ F - 1) / 2 ^ F) := by
    refine ((Int.ediv_emod_unique (a := -x) (r := 2 ^ F - 1 - (x + 2 ^ F - 1) % 2 ^ F) hP).mpr
      ⟨?_, ?_, ?_⟩).1
    · linarith only [h1]
    · linarith only [h3]
    · linarith only [h2]
  rw [this, neg_neg]

/-- The body of `kernel::kN::ceil`: `(a + MASK) & !MASK` fits the wide type and
is `⌈a / 2^F⌉ · 2^F`. -/
theorem ceil_shape {B W} (a : IScalar B) (n k : ℕ) (hn : k + (k + 1) = n)
    (hB : B.numBits = n + 1) (hW : W.numBits = n + n + 1 + 1) (mask : Result (IScalar W))
    (hmask : mask ⦃ h => h.val = 2 ^ (k + 1) - 1 ⦄) :
    (do
        let i ← lift (IScalar.cast W a)
        let i1 ← mask
        let i2 ← i + i1
        let i3 ← lift (~~~ i1)
        ok (i2 &&& i3))
      ⦃ r => r.val = ⌈exact (k + 1) a.val⌉ * 2 ^ (k + 1) ⦄ := by
  have hk : k + 1 < n + n + 1 := by omega
  have hBW : B.numBits ≤ W.numBits := hB ▸ hW ▸ Nat.succ_le_succ (Nat.le_add_right n (n + 1))
  have ca := IScalar.val_mod_pow_greater_numBits W a hBW
  have ⟨la, ua⟩ := val_bounds a hB
  have pF : (2 : ℤ) ^ (k + 1) ≤ 2 ^ n := pow_le_pow_right₀ one_le_two (by omega)
  have hpow : (2 : ℤ) ^ n + 2 ^ n ≤ 2 ^ (n + n + 1) := by
    rw [pow_succ, pow_add]; nlinarith only [one_le_pow₀ (M₀ := ℤ) one_le_two (n := n), la, ua]
  rw [lift, bind_ok]
  refine WP.spec_bind hmask fun m hm => ?_
  have q1 : (1 : ℤ) ≤ 2 ^ (k + 1) := one_le_pow₀ one_le_two
  have q2 : (0 : ℤ) < 2 ^ n := pow_pos zero_lt_two n
  have ⟨fl, fu⟩ := in_bounds_of_pow hW (x := a.val + m.val) (by rw [hm]; linarith only [la, pF, hpow, q1])
    (by rw [hm]; linarith only [ua, pF, hpow])
  refine WP.spec_bind (IScalar.add_spec (ca ▸ fl) (ca ▸ fu)) fun s hs => ?_
  rw [lift, bind_ok, WP.spec_ok, (mask_val s m (k + 1) (n + n + 1) hW hk hm).1, hs, ca, hm,
    ceil_exact]
  ring_nf

/-- The body of `kernel::kN::round_half_away`: the magnitude plus `HALF`,
masked, with the sign of `a`. -/
theorem round_half_away_shape {B W} (a : IScalar B) (zero : IScalar W) (n k : ℕ)
    (hn : k + (k + 1) = n) (hB : B.numBits = n + 1) (hW : W.numBits = n + n + 1 + 1)
    (hzero : zero.val = 0) (half mask : Result (IScalar W))
    (hhalf : half ⦃ h => h.val = 2 ^ k ⦄) (hmask : mask ⦃ h => h.val = 2 ^ (k + 1) - 1 ⦄) :
    (do
        let w ← lift (IScalar.cast W a)
        if w >= zero
        then
          let i ← half
          let i1 ← w + i
          let i2 ← mask
          let i3 ← lift (~~~ i2)
          ok (i1 &&& i3)
        else
          let i ← half
          let i1 ← i - w
          let i2 ← mask
          let i3 ← lift (~~~ i2)
          let i4 ← lift (i1 &&& i3)
          -. i4)
      ⦃ r => r.val = (if 0 ≤ a.val then roundHalfUp (exact (k + 1) a.val)
        else -roundHalfUp (exact (k + 1) (-a.val))) * 2 ^ (k + 1) ⦄ := by
  have hk : k + 1 < n + n + 1 := by omega
  have hBW : B.numBits ≤ W.numBits := hB ▸ hW ▸ Nat.succ_le_succ (Nat.le_add_right n (n + 1))
  have ca := IScalar.val_mod_pow_greater_numBits W a hBW
  have ⟨la, ua⟩ := val_bounds a hB
  have pk : (2 : ℤ) ^ k < 2 ^ n := pow_lt_pow_right₀ one_lt_two (by omega)
  have p0 : (0 : ℤ) < 2 ^ k := pow_pos zero_lt_two k
  have hpow : (2 : ℤ) ^ n + 2 ^ n ≤ 2 ^ (n + n + 1) := by
    rw [pow_succ, pow_add]; nlinarith only [one_le_pow₀ (M₀ := ℤ) one_le_two (n := n), la, ua]
  have q2 : (0 : ℤ) < 2 ^ n := pow_pos zero_lt_two n
  rw [lift, bind_ok]
  have up : ∀ v : ℤ, ((v + 2 ^ k) / 2 ^ (k + 1)) * 2 ^ (k + 1) =
      roundHalfUp (exact (k + 1) v) * 2 ^ (k + 1) := fun v => by
    rw [← add_half_shr, shr_eq_div]
  by_cases h : IScalar.cast W a >= zero
  · have h0 : 0 ≤ a.val := by have : zero.val ≤ (IScalar.cast W a).val := h; rwa [hzero, ca] at this
    rw [ite_eq_left h]
    refine WP.spec_bind hhalf fun i hi => ?_
    have ⟨fl, fu⟩ := in_bounds_of_pow hW (x := a.val + i.val) (by rw [hi]; linarith only [la, pk, p0, hpow])
      (by rw [hi]; linarith only [ua, pk, hpow])
    refine WP.spec_bind (IScalar.add_spec (ca ▸ fl) (ca ▸ fu)) fun s hs => ?_
    refine WP.spec_bind hmask fun m hm => ?_
    rw [lift, bind_ok, WP.spec_ok, (mask_val s m (k + 1) (n + n + 1) hW hk hm).1, hs, ca, hi,
      ite_eq_left h0, up]
  · have h0 : ¬0 ≤ a.val := fun h0 => h (by
      show zero.val ≤ (IScalar.cast W a).val; rw [hzero, ca]; exact h0)
    rw [ite_eq_right h]
    refine WP.spec_bind hhalf fun i hi => ?_
    have ⟨fl, fu⟩ := in_bounds_of_pow hW (x := i.val - a.val) (by rw [hi]; linarith only [pk, p0, hpow, h0])
      (by rw [hi]; linarith only [la, pk, hpow])
    refine WP.spec_bind (IScalar.sub_spec (ca ▸ fl) (ca ▸ fu)) fun s hs => ?_
    refine WP.spec_bind hmask fun m hm => ?_
    rw [lift, bind_ok, lift, bind_ok]
    have ⟨v, _⟩ := mask_val s m (k + 1) (n + n + 1) hW hk hm
    have hv : (s &&& ~~~m).val = roundHalfUp (exact (k + 1) (-a.val)) * 2 ^ (k + 1) := by
      rw [v, hs, ca, hi, ← up]; ring_nf
    have q0 : 0 ≤ roundHalfUp (exact (k + 1) (-a.val)) := by
      rw [← add_half_shr, shr_eq_div]; exact Int.ediv_nonneg (by linarith only [p0, h0]) (by positivity)
    have hmin : ((s &&& ~~~m : IScalar W) : ℤ) ≠ IScalar.min W := by
      intro this
      rw [hv, IScalar.min_def] at this
      have : (0 : ℤ) ≤ roundHalfUp (exact (k + 1) (-a.val)) * 2 ^ (k + 1) := by positivity
      have : (0 : ℤ) < 2 ^ (W.numBits - 1) := by positivity
      linarith
    refine WP.spec_mono (HNeg.hNeg.step _ hmin) fun r hr => ?_
    rw [hr, hv, ite_eq_right h0]; ring

/-- The body of `kernel::kN::round_ties_even`: the floor, the fraction and the
last bit of the floor pick the nearest multiple of `2^F`, the even one on a tie. -/
theorem round_ties_even_shape {B W} (a : IScalar B) (one1 : IScalar W) (sh : Std.I32)
    (n k : ℕ) (hn : k + (k + 1) = n) (hB : B.numBits = n + 1) (hW : W.numBits = n + n + 1 + 1)
    (hone1 : one1.bv.toNat = 1) (hsh : sh.val = ((k + 1 : ℕ) : ℤ))
    (half mask one : Result (IScalar W)) (hhalf : half ⦃ h => h.val = 2 ^ k ⦄)
    (hmask : mask ⦃ h => h.val = 2 ^ (k + 1) - 1 ⦄) (hone : one ⦃ h => h.val = 2 ^ (k + 1) ⦄) :
    (do
        let w ← lift (IScalar.cast W a)
        let i ← mask
        let i1 ← lift (~~~ i)
        let floor ← lift (w &&& i1)
        let frac ← lift (w &&& i)
        let i2 ← w >>> sh
        let i3 ← lift (i2 &&& one1)
        let i4 ← half
        if frac > i4
        then let i5 ← one
             floor + i5
        else
          if frac = i4
          then if i3 = one1
               then let i5 ← one
                    floor + i5
               else ok floor
          else ok floor)
      ⦃ r => 2 ^ (k + 1) ∣ r.val ∧ 2 * |a.val - r.val| ≤ 2 ^ (k + 1) ∧
        (2 * |a.val - r.val| = 2 ^ (k + 1) → Even (r.val / 2 ^ (k + 1))) ⦄ := by
  have hk : k + 1 < n + n + 1 := by omega
  have hBW : B.numBits ≤ W.numBits := hB ▸ hW ▸ Nat.succ_le_succ (Nat.le_add_right n (n + 1))
  have ca := IScalar.val_mod_pow_greater_numBits W a hBW
  have ⟨la, ua⟩ := val_bounds a hB
  have pF : (0 : ℤ) < 2 ^ (k + 1) := pow_pos zero_lt_two _
  have pkF : (2 : ℤ) ^ (k + 1) = 2 * 2 ^ k := pow_succ' 2 k
  have pFn : (2 : ℤ) ^ (k + 1) ≤ 2 ^ n := pow_le_pow_right₀ one_le_two (by omega)
  have hpow : (2 : ℤ) ^ n + 2 ^ n ≤ 2 ^ (n + n + 1) := by
    rw [pow_succ, pow_add]; nlinarith only [one_le_pow₀ (M₀ := ℤ) one_le_two (n := n), la, ua]
  rw [lift, bind_ok]
  refine WP.spec_bind hmask fun m hm => ?_
  rw [lift, bind_ok, lift, bind_ok, lift, bind_ok]
  have ⟨hfl, hfr⟩ := mask_val (IScalar.cast W a) m (k + 1) (n + n + 1) hW hk hm
  rw [ca] at hfl hfr
  refine WP.spec_bind (IScalar.ShiftRight_IScalar_spec (IScalar.cast W a) sh
    (hsh ▸ Int.natCast_nonneg _) (hsh ▸ Int.ofNat_lt.mpr (hW ▸ by omega))) fun i2 ⟨hi2, _⟩ => ?_
  rw [IScalar.toNat, hsh, Int.toNat_natCast, ca, shr_eq_div] at hi2
  rw [lift, bind_ok]
  have hbit := and_one_val i2 one1 hone1 (n + n) (by rw [hW])
  rw [hi2] at hbit
  refine WP.spec_bind hhalf fun h hh => ?_
  generalize hq : a.val / 2 ^ (k + 1) = q at hfl hbit
  generalize hr : a.val % 2 ^ (k + 1) = rem at hfr
  have dec : q * 2 ^ (k + 1) + rem = a.val := by
    rw [← hq, ← hr, mul_comm]; exact Int.mul_ediv_add_emod _ _
  have r0 : 0 ≤ rem := hr ▸ Int.emod_nonneg _ pF.ne'
  have r1 : rem < 2 ^ (k + 1) := hr ▸ Int.emod_lt_of_pos _ pF
  have hfl' : ((IScalar.cast W a) &&& ~~~m).val = q * 2 ^ (k + 1) := hfl
  have fit : q * 2 ^ (k + 1) + 2 ^ (k + 1) ≤ IScalar.max W ∧
      IScalar.min W ≤ q * 2 ^ (k + 1) + 2 ^ (k + 1) := by
    have ⟨l, u⟩ := in_bounds_of_pow hW (x := q * 2 ^ (k + 1) + 2 ^ (k + 1))
      (by linarith only [la, pF, pFn, hpow, dec, r1]) (by linarith only [ua, pFn, hpow, dec, r0])
    exact ⟨u, l⟩
  have up : ∀ o : Result (IScalar W), o ⦃ h => h.val = 2 ^ (k + 1) ⦄ →
      (do let i5 ← o; ((IScalar.cast W a) &&& ~~~m) + i5)
        ⦃ r => r.val = (q + 1) * 2 ^ (k + 1) ⦄ := fun o ho =>
    WP.spec_bind ho fun i5 hi5 => WP.spec_mono
      (IScalar.add_spec (by rw [hfl', hi5]; exact fit.2) (by rw [hfl', hi5]; exact fit.1))
      fun r hr => by rw [hr, hfl', hi5]; ring
  have even_div : ∀ c : ℤ, Even (c * 2 ^ (k + 1) / 2 ^ (k + 1)) ↔ c % 2 = 0 := fun c => by
    rw [Int.mul_ediv_cancel _ pF.ne', Int.even_iff]
  have goal_up : 2 ^ (k + 1) ∣ (q + 1) * 2 ^ (k + 1) := dvd_mul_left _ _
  have goal_dn : 2 ^ (k + 1) ∣ q * 2 ^ (k + 1) := dvd_mul_left _ _
  have dup : a.val - (q + 1) * 2 ^ (k + 1) = rem - 2 ^ (k + 1) := by linarith only [dec]
  have ddn : a.val - q * 2 ^ (k + 1) = rem := by linarith only [dec]
  have hfrv : ((IScalar.cast W a) &&& m).val = rem := hfr
  by_cases g : ((IScalar.cast W a) &&& m) > h
  · rw [ite_eq_left g]
    have g' : 2 ^ k < rem := by have : h.val < _ := g; rwa [hh, hfrv] at this
    refine WP.spec_mono (up one hone) fun r hr => ?_
    rw [hr, dup, abs_of_neg (by linarith only [r1])]
    exact ⟨goal_up, by linarith only [pkF, g'], fun e => by linarith only [pkF, g', e]⟩
  rw [ite_eq_right g]
  have g' : rem ≤ 2 ^ k := by
    have : ¬ h.val < _ := g; rw [hh, hfrv] at this; exact not_lt.mp this
  by_cases t : ((IScalar.cast W a) &&& m) = h
  · rw [ite_eq_left t]
    have t' : rem = 2 ^ k := by have := congrArg IScalar.val t; rwa [hh, hfrv] at this
    by_cases o : i2 &&& one1 = one1
    · rw [ite_eq_left o]
      have o' : q % 2 = 1 := by
        have := congrArg IScalar.val o
        rw [hbit] at this
        have v1 : one1.val = 1 := by
          rw [IScalar.val, BitVec.toInt_eq_msb_cond, BitVec.msb_eq_decide, hone1]
          have : 1 < 2 ^ (W.numBits - 1) := by
            rw [hW]; exact Nat.one_lt_two_pow (by omega)
          simp [Nat.not_le.mpr this]
        rwa [v1] at this
      refine WP.spec_mono (up one hone) fun r hr => ?_
      rw [hr, dup, abs_of_neg (by linarith only [r1]), t']
      refine ⟨goal_up, by linarith only [pkF], fun _ => (even_div _).2 (by omega)⟩
    · rw [ite_eq_right o, WP.spec_ok, hfl', ddn, abs_of_nonneg r0, t']
      have o' : q % 2 = 0 := by
        by_contra c
        apply o
        apply IScalar.eq_of_val_eq
        rw [hbit]
        have v1 : one1.val = 1 := by
          rw [IScalar.val, BitVec.toInt_eq_msb_cond, BitVec.msb_eq_decide, hone1]
          have : 1 < 2 ^ (W.numBits - 1) := by
            rw [hW]; exact Nat.one_lt_two_pow (by omega)
          simp [Nat.not_le.mpr this]
        rw [v1]; omega
      exact ⟨goal_dn, by linarith only [pkF], fun _ => (even_div _).2 o'⟩
  · rw [ite_eq_right t, WP.spec_ok, hfl', ddn, abs_of_nonneg r0]
    have t' : rem ≠ 2 ^ k := fun e => t (IScalar.eq_of_val_eq (by rw [hh, hfrv]; exact e))
    have : rem < 2 ^ k := lt_of_le_of_ne g' t'
    exact ⟨goal_dn, by linarith only [pkF, this], fun e => by linarith only [pkF, this, e]⟩

/-- `kernel::k8::ONE` is `2^4`. -/
theorem k8_one_spec : fulcrum.kernel.k8.ONE ⦃ h => h.val = 2 ^ 4 ⦄ := by
  unfold fulcrum.kernel.k8.ONE
  exact one_shape 4#i32 1#i16 4 15 rfl rfl rfl (Nat.le_of_ble_eq_true rfl)

/-- `kernel::k8::MASK` is `2^4 - 1`. -/
theorem k8_mask_spec : fulcrum.kernel.k8.MASK ⦃ h => h.val = 2 ^ 4 - 1 ⦄ := by
  unfold fulcrum.kernel.k8.MASK
  exact mask_shape _ 1#i16 4 k8_one_spec rfl

/-- L5 on the code: `kernel::k8::ceil` is `⌈a / 2^4⌉ · 2^4`. -/
theorem k8_ceil_spec (a : Std.I8) :
    fulcrum.kernel.k8.ceil a ⦃ r => r.val = ⌈exact 4 a.val⌉ * 2 ^ 4 ⦄ :=
  ceil_shape a 7 3 rfl rfl rfl _ k8_mask_spec

/-- L5 on the code: `kernel::k8::round_half_away` rounds `a / 2^4` to nearest,
ties away from zero. -/
theorem k8_round_half_away_spec (a : Std.I8) :
    fulcrum.kernel.k8.round_half_away a ⦃ r => r.val = (if 0 ≤ a.val then
      roundHalfUp (exact 4 a.val) else -roundHalfUp (exact 4 (-a.val))) * 2 ^ 4 ⦄ :=
  round_half_away_shape a 0#i16 7 3 rfl rfl rfl rfl _ _ k8_half_spec k8_mask_spec

/-- L5 on the code: `kernel::k8::round_ties_even` is the multiple of `2^4`
nearest to `a`, the even one on a tie. -/
theorem k8_round_ties_even_spec (a : Std.I8) :
    fulcrum.kernel.k8.round_ties_even a ⦃ r => 2 ^ 4 ∣ r.val ∧
      2 * |a.val - r.val| ≤ 2 ^ 4 ∧ (2 * |a.val - r.val| = 2 ^ 4 → Even (r.val / 2 ^ 4)) ⦄ :=
  round_ties_even_shape a 1#i16 4#i32 7 3 rfl rfl rfl rfl rfl _ _ _ k8_half_spec
    k8_mask_spec k8_one_spec

/-- `kernel::k16::ONE` is `2^8`. -/
theorem k16_one_spec : fulcrum.kernel.k16.ONE ⦃ h => h.val = 2 ^ 8 ⦄ := by
  unfold fulcrum.kernel.k16.ONE
  exact one_shape 8#i32 1#i32 8 31 rfl rfl rfl (Nat.le_of_ble_eq_true rfl)

/-- `kernel::k16::MASK` is `2^8 - 1`. -/
theorem k16_mask_spec : fulcrum.kernel.k16.MASK ⦃ h => h.val = 2 ^ 8 - 1 ⦄ := by
  unfold fulcrum.kernel.k16.MASK
  exact mask_shape _ 1#i32 8 k16_one_spec rfl

/-- L5 on the code: `kernel::k16::ceil` is `⌈a / 2^8⌉ · 2^8`. -/
theorem k16_ceil_spec (a : Std.I16) :
    fulcrum.kernel.k16.ceil a ⦃ r => r.val = ⌈exact 8 a.val⌉ * 2 ^ 8 ⦄ :=
  ceil_shape a 15 7 rfl rfl rfl _ k16_mask_spec

/-- L5 on the code: `kernel::k16::round_half_away` rounds `a / 2^8` to nearest,
ties away from zero. -/
theorem k16_round_half_away_spec (a : Std.I16) :
    fulcrum.kernel.k16.round_half_away a ⦃ r => r.val = (if 0 ≤ a.val then
      roundHalfUp (exact 8 a.val) else -roundHalfUp (exact 8 (-a.val))) * 2 ^ 8 ⦄ :=
  round_half_away_shape a 0#i32 15 7 rfl rfl rfl rfl _ _ k16_half_spec k16_mask_spec

/-- L5 on the code: `kernel::k16::round_ties_even` is the multiple of `2^8`
nearest to `a`, the even one on a tie. -/
theorem k16_round_ties_even_spec (a : Std.I16) :
    fulcrum.kernel.k16.round_ties_even a ⦃ r => 2 ^ 8 ∣ r.val ∧
      2 * |a.val - r.val| ≤ 2 ^ 8 ∧ (2 * |a.val - r.val| = 2 ^ 8 → Even (r.val / 2 ^ 8)) ⦄ :=
  round_ties_even_shape a 1#i32 8#i32 15 7 rfl rfl rfl rfl rfl _ _ _ k16_half_spec
    k16_mask_spec k16_one_spec

/-- `kernel::k32::ONE` is `2^16`. -/
theorem k32_one_spec : fulcrum.kernel.k32.ONE ⦃ h => h.val = 2 ^ 16 ⦄ := by
  unfold fulcrum.kernel.k32.ONE
  exact one_shape 16#i32 1#i64 16 63 rfl rfl rfl (Nat.le_of_ble_eq_true rfl)

/-- `kernel::k32::MASK` is `2^16 - 1`. -/
theorem k32_mask_spec : fulcrum.kernel.k32.MASK ⦃ h => h.val = 2 ^ 16 - 1 ⦄ := by
  unfold fulcrum.kernel.k32.MASK
  exact mask_shape _ 1#i64 16 k32_one_spec rfl

/-- L5 on the code: `kernel::k32::ceil` is `⌈a / 2^16⌉ · 2^16`. -/
theorem k32_ceil_spec (a : Std.I32) :
    fulcrum.kernel.k32.ceil a ⦃ r => r.val = ⌈exact 16 a.val⌉ * 2 ^ 16 ⦄ :=
  ceil_shape a 31 15 rfl rfl rfl _ k32_mask_spec

/-- L5 on the code: `kernel::k32::round_half_away` rounds `a / 2^16` to nearest,
ties away from zero. -/
theorem k32_round_half_away_spec (a : Std.I32) :
    fulcrum.kernel.k32.round_half_away a ⦃ r => r.val = (if 0 ≤ a.val then
      roundHalfUp (exact 16 a.val) else -roundHalfUp (exact 16 (-a.val))) * 2 ^ 16 ⦄ :=
  round_half_away_shape a 0#i64 31 15 rfl rfl rfl rfl _ _ k32_half_spec k32_mask_spec

/-- L5 on the code: `kernel::k32::round_ties_even` is the multiple of `2^16`
nearest to `a`, the even one on a tie. -/
theorem k32_round_ties_even_spec (a : Std.I32) :
    fulcrum.kernel.k32.round_ties_even a ⦃ r => 2 ^ 16 ∣ r.val ∧
      2 * |a.val - r.val| ≤ 2 ^ 16 ∧ (2 * |a.val - r.val| = 2 ^ 16 → Even (r.val / 2 ^ 16)) ⦄ :=
  round_ties_even_shape a 1#i64 16#i32 31 15 rfl rfl rfl rfl rfl _ _ _ k32_half_spec
    k32_mask_spec k32_one_spec

/-- `kernel::k64::HALF` is `2^31`. -/
theorem k64_half_spec : fulcrum.kernel.k64.HALF ⦃ h => h.val = 2 ^ 31 ⦄ := by
  unfold fulcrum.kernel.k64.HALF
  exact half_shape 32#i32 1#i128 31 127 rfl rfl rfl (Nat.le_of_ble_eq_true rfl)

/-- `kernel::k64::ONE` is `2^32`. -/
theorem k64_one_spec : fulcrum.kernel.k64.ONE ⦃ h => h.val = 2 ^ 32 ⦄ := by
  unfold fulcrum.kernel.k64.ONE
  exact one_shape 32#i32 1#i128 32 127 rfl rfl rfl (Nat.le_of_ble_eq_true rfl)

/-- `kernel::k64::MASK` is `2^32 - 1`. -/
theorem k64_mask_spec : fulcrum.kernel.k64.MASK ⦃ h => h.val = 2 ^ 32 - 1 ⦄ := by
  unfold fulcrum.kernel.k64.MASK
  exact mask_shape _ 1#i128 32 k64_one_spec rfl

/-- L5 on the code: `kernel::k64::ceil` is `⌈a / 2^32⌉ · 2^32`. -/
theorem k64_ceil_spec (a : Std.I64) :
    fulcrum.kernel.k64.ceil a ⦃ r => r.val = ⌈exact 32 a.val⌉ * 2 ^ 32 ⦄ :=
  ceil_shape a 63 31 rfl rfl rfl _ k64_mask_spec

/-- L5 on the code: `kernel::k64::round_half_away` rounds `a / 2^32` to nearest,
ties away from zero. -/
theorem k64_round_half_away_spec (a : Std.I64) :
    fulcrum.kernel.k64.round_half_away a ⦃ r => r.val = (if 0 ≤ a.val then
      roundHalfUp (exact 32 a.val) else -roundHalfUp (exact 32 (-a.val))) * 2 ^ 32 ⦄ :=
  round_half_away_shape a 0#i128 63 31 rfl rfl rfl rfl _ _ k64_half_spec k64_mask_spec

/-- L5 on the code: `kernel::k64::round_ties_even` is the multiple of `2^32`
nearest to `a`, the even one on a tie. -/
theorem k64_round_ties_even_spec (a : Std.I64) :
    fulcrum.kernel.k64.round_ties_even a ⦃ r => 2 ^ 32 ∣ r.val ∧
      2 * |a.val - r.val| ≤ 2 ^ 32 ∧ (2 * |a.val - r.val| = 2 ^ 32 → Even (r.val / 2 ^ 32)) ⦄ :=
  round_ties_even_shape a 1#i128 32#i32 63 31 rfl rfl rfl rfl rfl _ _ _ k64_half_spec
    k64_mask_spec k64_one_spec

end Fulcrum

end
