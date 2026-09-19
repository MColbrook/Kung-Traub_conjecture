import support_reference.KungTraub.Coefficients

/-!
# The normalized polynomial derivative bound

The Cauchy–Schwarz estimate in the manuscript's coefficient preliminaries uses
the exact series sum `80/27`. The finite Cauchy–Schwarz inequality and comparison
with a summable series are from Mathlib.
-/

noncomputable section
open scoped BigOperators
namespace KungTraub

theorem polynomial_derivative_eval_sum {n : ℕ} (q : Polynomial ℂ)
    (hq : q.natDegree ≤ n) (s : ℂ) :
    q.derivative.eval s =
      ∑ k ∈ Finset.range n, q.coeff (k + 1) * (k + 1 : ℂ) * s ^ k := by
  sorry

theorem normalized_coefficient_tail_sq_sum_le_one {n : ℕ} (q : Polynomial ℂ)
    (hnorm : ‖coefficientVector n q‖ = 1) :
    ∑ k ∈ Finset.range n, ‖q.coeff (k + 1)‖ ^ 2 ≤ 1 := by
  sorry

theorem derivative_weight_sq_sum_le {n : ℕ} {r : ℝ} (hr : 0 ≤ r) (hhalf : r ≤ 1 / 2) :
    ∑ k ∈ Finset.range n, (((k : ℝ) + 1) * r ^ k) ^ 2 ≤ 80 / 27 := by
  sorry

/-- The exact square-root bound for every normalized polynomial on the closed
complex half-unit disc, including degree zero. -/
theorem polynomial_derivative_norm_le_sqrt {n : ℕ} (q : Polynomial ℂ)
    (hq : q.natDegree ≤ n) (hnorm : ‖coefficientVector n q‖ = 1)
    {s : ℂ} (hs : ‖s‖ ≤ 1 / 2) :
    ‖q.derivative.eval s‖ ≤ Real.sqrt (80 / 27 : ℝ) := by
  sorry

theorem polynomial_derivative_norm_lt_two {n : ℕ} (q : Polynomial ℂ)
    (hq : q.natDegree ≤ n) (hnorm : ‖coefficientVector n q‖ = 1)
    {s : ℂ} (hs : ‖s‖ ≤ 1 / 2) : ‖q.derivative.eval s‖ < 2 := by
  sorry

end KungTraub
