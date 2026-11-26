module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# Series of `sin`, `cos`, `arctan`, `log` and `exp` with bounded tails

Each series of Mathlib, cut after `n` terms, is within an explicit bound of its
sum: from `n` on the terms shrink at least geometrically (`abs_sub_sum_le`),
by `n! · (n + 1)^m ≤ (n + m)!` for the factorial ones. At a rational point the
partial sum and the bound are rationals (`sinSum`, `sinRem` and the others),
which the kernel evaluates exactly; `sin_near` and the others carry them to
`ℝ`. No code here: the math of the constants, the tables and the error bounds
of L4.
-/

@[expose] public section

open Finset

namespace Fulcrum

/-- The tail of a series whose terms from `n` on are at most `a · r^i`, `r < 1`, is at
most `a / (1 - r)`. -/
theorem abs_sub_sum_le {f : ℕ → ℝ} {s : ℝ} (hs : HasSum f s) (n : ℕ) (a r : ℝ) (hr0 : 0 ≤ r)
    (hr1 : r < 1) (hb : ∀ i, |f (i + n)| ≤ a * r ^ i) :
    |s - ∑ i ∈ range n, f i| ≤ a / (1 - r) :=
  ((hasSum_nat_add_iff' n).mpr hs).norm_le_of_bounded
    (by simpa [div_eq_mul_inv] using (hasSum_geometric_of_lt_one hr0 hr1).mul_left a) hb

/-- The Taylor series of `sin` cut after `n` terms, with the bound of its tail. -/
theorem sin_sub_sum_le (x : ℝ) (n : ℕ) (hx : x ^ 2 < (2 * n + 2) ^ 2) :
    |Real.sin x - ∑ j ∈ range n, (-1) ^ j * x ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ)| ≤
      |x| ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) / (1 - x ^ 2 / (2 * n + 2) ^ 2) := by
  have p : (0 : ℝ) < (2 * n + 2) ^ 2 := by positivity
  refine abs_sub_sum_le (Real.hasSum_sin x) n _ _ (by positivity) ((div_lt_one p).mpr hx) fun i => ?_
  have hf : ((2 * n + 1).factorial : ℝ) * ((2 * n + 2) ^ 2) ^ i ≤
      ((2 * n + 1 + 2 * i).factorial : ℝ) := by
    rw [← pow_mul]; exact_mod_cast Nat.factorial_mul_pow_le_factorial (m := 2 * n + 1) (n := 2 * i)
  rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_pow, Nat.abs_cast,
    show 2 * (i + n) + 1 = 2 * n + 1 + 2 * i by ring, pow_add, pow_mul, sq_abs, div_pow,
    div_mul_div_comm]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) hf

/-- The Taylor series of `cos` cut after `n` terms, with the bound of its tail. -/
theorem cos_sub_sum_le (x : ℝ) (n : ℕ) (hx : x ^ 2 < (2 * n + 1) ^ 2) :
    |Real.cos x - ∑ j ∈ range n, (-1) ^ j * x ^ (2 * j) / ((2 * j).factorial : ℝ)| ≤
      |x| ^ (2 * n) / ((2 * n).factorial : ℝ) / (1 - x ^ 2 / (2 * n + 1) ^ 2) := by
  have p : (0 : ℝ) < (2 * n + 1) ^ 2 := by positivity
  refine abs_sub_sum_le (Real.hasSum_cos x) n _ _ (by positivity) ((div_lt_one p).mpr hx) fun i => ?_
  have hf : ((2 * n).factorial : ℝ) * ((2 * n + 1) ^ 2) ^ i ≤ ((2 * n + 2 * i).factorial : ℝ) := by
    rw [← pow_mul]; exact_mod_cast Nat.factorial_mul_pow_le_factorial (m := 2 * n) (n := 2 * i)
  rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_pow, Nat.abs_cast,
    show 2 * (i + n) = 2 * n + 2 * i by ring, pow_add, pow_mul |x| 2 i, sq_abs, div_pow,
    div_mul_div_comm]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) hf

/-- The series of `arctan` on `(-1, 1)` cut after `n` terms, with the bound of its
tail. -/
theorem arctan_sub_sum_le (x : ℝ) (n : ℕ) (hx : |x| < 1) :
    |Real.arctan x - ∑ j ∈ range n, (-1) ^ j * x ^ (2 * j + 1) / (2 * j + 1 : ℝ)| ≤
      |x| ^ (2 * n + 1) / (2 * n + 1) / (1 - x ^ 2) := by
  have h2 : x ^ 2 < 1 := by rw [← sq_abs]; exact pow_lt_one₀ (abs_nonneg x) hx two_ne_zero
  refine abs_sub_sum_le (by simpa using Real.hasSum_arctan (x := x) hx) n _ _ (sq_nonneg x) h2
    fun i => ?_
  push_cast
  rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_pow,
    show 2 * ((i : ℝ) + n) + 1 = 2 * n + 1 + 2 * i by ring,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * n + 1 + 2 * i),
    show 2 * (i + n) + 1 = 2 * n + 1 + 2 * i by ring, pow_add, pow_mul, sq_abs, div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (le_add_of_nonneg_right (by positivity))

/-- The series of `log (1 + x) - log (1 - x) = 2 artanh x` on `(-1, 1)` cut after
`n` terms, with the bound of its tail. -/
theorem log_sub_sum_le (x : ℝ) (n : ℕ) (hx : |x| < 1) :
    |(Real.log (1 + x) - Real.log (1 - x)) - ∑ j ∈ range n, 2 * (1 / (2 * j + 1 : ℝ)) * x ^ (2 * j + 1)| ≤
      2 * |x| ^ (2 * n + 1) / (2 * n + 1) / (1 - x ^ 2) := by
  have h2 : x ^ 2 < 1 := by rw [← sq_abs]; exact pow_lt_one₀ (abs_nonneg x) hx two_ne_zero
  refine abs_sub_sum_le (Real.hasSum_log_sub_log_of_abs_lt_one hx) n _ _ (sq_nonneg x) h2 fun i => ?_
  push_cast
  rw [abs_mul, abs_mul, abs_pow, abs_two, one_div, abs_inv,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * ((i : ℝ) + n) + 1),
    show 2 * ((i : ℝ) + n) + 1 = 2 * n + 1 + 2 * i by ring,
    show 2 * (i + n) + 1 = 2 * n + 1 + 2 * i by ring, pow_add, pow_mul, sq_abs]
  have d : (0 : ℝ) < 2 * n + 1 := by positivity
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (inv_anti₀ d (le_add_of_nonneg_right (by positivity))) zero_le_two) (by positivity)).trans_eq
    (by ring)

/-- The Taylor series of `exp` cut after `n` terms, with the bound of its tail. -/
theorem exp_sub_sum_le (x : ℝ) (n : ℕ) (hx : |x| < n + 1) :
    |Real.exp x - ∑ m ∈ range n, x ^ m / (m.factorial : ℝ)| ≤
      |x| ^ n / (n.factorial : ℝ) / (1 - |x| / (n + 1)) := by
  have p : (0 : ℝ) < n + 1 := by positivity
  refine abs_sub_sum_le (by rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp x) n
    _ _ (by positivity) ((div_lt_one p).mpr hx) fun i => ?_
  have hf : (n.factorial : ℝ) * (n + 1) ^ i ≤ ((n + i).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_mul_pow_le_factorial (m := n) (n := i)
  rw [abs_div, abs_pow, Nat.abs_cast, add_comm i n, pow_add, div_pow, div_mul_div_comm]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) hf

/-! ## The same series at a rational point

The partial sums and the tail bounds in `ℚ`, so that the kernel evaluates
them (`decide +kernel`) and the theorems below carry them to `ℝ`. -/

/-- The first `n` terms of the series of `sin q`. -/
def sinSum (q : ℚ) (n : ℕ) : ℚ := ∑ j ∈ range n, (-1) ^ j * q ^ (2 * j + 1) / (2 * j + 1).factorial

/-- The bound of the tail of `sinSum`. -/
def sinRem (q : ℚ) (n : ℕ) : ℚ := |q| ^ (2 * n + 1) / (2 * n + 1).factorial / (1 - q ^ 2 / (2 * n + 2) ^ 2)

/-- The first `n` terms of the series of `cos q`. -/
def cosSum (q : ℚ) (n : ℕ) : ℚ := ∑ j ∈ range n, (-1) ^ j * q ^ (2 * j) / (2 * j).factorial

/-- The bound of the tail of `cosSum`. -/
def cosRem (q : ℚ) (n : ℕ) : ℚ := |q| ^ (2 * n) / (2 * n).factorial / (1 - q ^ 2 / (2 * n + 1) ^ 2)

/-- The first `n` terms of the series of `arctan q`. -/
def atanSum (q : ℚ) (n : ℕ) : ℚ := ∑ j ∈ range n, (-1) ^ j * q ^ (2 * j + 1) / (2 * j + 1)

/-- The bound of the tail of `atanSum`. -/
def atanRem (q : ℚ) (n : ℕ) : ℚ := |q| ^ (2 * n + 1) / (2 * n + 1) / (1 - q ^ 2)

/-- The first `n` terms of the series of `log (1 + q) - log (1 - q)`. -/
def logSum (q : ℚ) (n : ℕ) : ℚ := ∑ j ∈ range n, 2 * (1 / (2 * j + 1)) * q ^ (2 * j + 1)

/-- The bound of the tail of `logSum`. -/
def logRem (q : ℚ) (n : ℕ) : ℚ := 2 * |q| ^ (2 * n + 1) / (2 * n + 1) / (1 - q ^ 2)

/-- The first `n` terms of the series of `exp q`. -/
def expSum (q : ℚ) (n : ℕ) : ℚ := ∑ m ∈ range n, q ^ m / m.factorial

/-- The bound of the tail of `expSum`. -/
def expRem (q : ℚ) (n : ℕ) : ℚ := |q| ^ n / n.factorial / (1 - |q| / (n + 1))

/-- `sin q` is within `sinRem` of `sinSum`. -/
theorem sin_near (q : ℚ) (n : ℕ) (h : q ^ 2 < (2 * n + 2) ^ 2) :
    |Real.sin q - sinSum q n| ≤ sinRem q n := by
  have b := sin_sub_sum_le q n (by exact_mod_cast h)
  unfold sinSum sinRem; push_cast; exact b

/-- `cos q` is within `cosRem` of `cosSum`. -/
theorem cos_near (q : ℚ) (n : ℕ) (h : q ^ 2 < (2 * n + 1) ^ 2) :
    |Real.cos q - cosSum q n| ≤ cosRem q n := by
  have b := cos_sub_sum_le q n (by exact_mod_cast h)
  unfold cosSum cosRem; push_cast; exact b

/-- `arctan q` is within `atanRem` of `atanSum`. -/
theorem arctan_near (q : ℚ) (n : ℕ) (h : |q| < 1) :
    |Real.arctan q - atanSum q n| ≤ atanRem q n := by
  have b := arctan_sub_sum_le q n (by exact_mod_cast h)
  unfold atanSum atanRem; push_cast; exact b

/-- `log (1 + q) - log (1 - q)` is within `logRem` of `logSum`. -/
theorem log_near (q : ℚ) (n : ℕ) (h : |q| < 1) :
    |(Real.log (1 + q) - Real.log (1 - q)) - logSum q n| ≤ logRem q n := by
  have b := log_sub_sum_le q n (by exact_mod_cast h)
  unfold logSum logRem; push_cast; exact b

/-- `exp q` is within `expRem` of `expSum`. -/
theorem exp_near (q : ℚ) (n : ℕ) (h : |q| < n + 1) :
    |Real.exp q - expSum q n| ≤ expRem q n := by
  have b := exp_sub_sum_le q n (by exact_mod_cast h)
  unfold expSum expRem; push_cast; exact b

end Fulcrum

end
