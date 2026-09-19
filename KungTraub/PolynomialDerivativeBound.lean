import KungTraub.Coefficients

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
  rw [Polynomial.derivative_eval,
    q.sum_over_range' (f := fun k a => a * (k : ℂ) * s ^ (k - 1))
      (by intro k; simp) (n + 1) (by omega), Finset.sum_range_succ']
  simp

theorem normalized_coefficient_tail_sq_sum_le_one {n : ℕ} (q : Polynomial ℂ)
    (hnorm : ‖coefficientVector n q‖ = 1) :
    ∑ k ∈ Finset.range n, ‖q.coeff (k + 1)‖ ^ 2 ≤ 1 := by
  have htotal : ∑ k ∈ Finset.range (n + 1), ‖q.coeff k‖ ^ 2 = 1 := by
    have h := EuclideanSpace.norm_sq_eq (coefficientVector n q)
    rw [hnorm, one_pow] at h
    have h' : ∑ i : Fin (n + 1), ‖q.coeff i.val‖ ^ 2 = 1 := h.symm
    rw [Fin.sum_univ_eq_sum_range (fun k => ‖q.coeff k‖ ^ 2)] at h'
    exact h'
  rw [Finset.sum_range_succ'] at htotal
  nlinarith [sq_nonneg ‖q.coeff 0‖]

theorem derivative_weight_sq_sum_le {n : ℕ} {r : ℝ} (hr : 0 ≤ r) (hhalf : r ≤ 1 / 2) :
    ∑ k ∈ Finset.range n, (((k : ℝ) + 1) * r ^ k) ^ 2 ≤ 80 / 27 := by
  calc
    ∑ k ∈ Finset.range n, (((k : ℝ) + 1) * r ^ k) ^ 2 =
        ∑ k ∈ Finset.range n, ((k : ℝ) + 1) ^ 2 * r ^ (2 * k) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [mul_pow, ← pow_mul, Nat.mul_comm]
    _ ≤ ∑ k ∈ Finset.range n, ((k : ℝ) + 1) ^ 2 * (1 / 2 : ℝ) ^ (2 * k) := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr hhalf _) (sq_nonneg _)
    _ ≤ ∑' k : ℕ, ((k : ℝ) + 1) ^ 2 * (1 / 2 : ℝ) ^ (2 * k) :=
      derivative_coefficient_series.summable.sum_le_tsum _ (by intro k _; positivity)
    _ = 80 / 27 := derivative_coefficient_series.tsum_eq

/-- The exact square-root bound for every normalized polynomial on the closed
complex half-unit disc, including degree zero. -/
theorem polynomial_derivative_norm_le_sqrt {n : ℕ} (q : Polynomial ℂ)
    (hq : q.natDegree ≤ n) (hnorm : ‖coefficientVector n q‖ = 1)
    {s : ℂ} (hs : ‖s‖ ≤ 1 / 2) :
    ‖q.derivative.eval s‖ ≤ Real.sqrt (80 / 27 : ℝ) := by
  have hcast (k : ℕ) : ‖(k : ℂ) + 1‖ = (k : ℝ) + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (k + 1)
  have hnormsum : ‖q.derivative.eval s‖ ≤
      ∑ k ∈ Finset.range n, ‖q.coeff (k + 1)‖ * (((k : ℝ) + 1) * ‖s‖ ^ k) := by
    rw [polynomial_derivative_eval_sum q hq]
    simpa only [norm_mul, norm_pow, hcast,
      mul_assoc] using norm_sum_le (Finset.range n)
        (fun k => q.coeff (k + 1) * (k + 1 : ℂ) * s ^ k)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range n)
    (fun k => ‖q.coeff (k + 1)‖) (fun k => ((k : ℝ) + 1) * ‖s‖ ^ k)
  have hcoeff := normalized_coefficient_tail_sq_sum_le_one q hnorm
  have hweights := derivative_weight_sq_sum_le (n := n) (norm_nonneg s) hs
  have hweights_nonneg : 0 ≤ ∑ k ∈ Finset.range n, (((k : ℝ) + 1) * ‖s‖ ^ k) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hsq : (∑ k ∈ Finset.range n,
      ‖q.coeff (k + 1)‖ * (((k : ℝ) + 1) * ‖s‖ ^ k)) ^ 2 ≤ 80 / 27 := by
    exact hcs.trans ((mul_le_mul_of_nonneg_right hcoeff hweights_nonneg).trans
      (by simpa only [one_mul] using hweights))
  have hroot := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 80 / 27)
  have hroot_nonneg := Real.sqrt_nonneg (80 / 27 : ℝ)
  apply hnormsum.trans
  nlinarith

theorem polynomial_derivative_norm_lt_two {n : ℕ} (q : Polynomial ℂ)
    (hq : q.natDegree ≤ n) (hnorm : ‖coefficientVector n q‖ = 1)
    {s : ℂ} (hs : ‖s‖ ≤ 1 / 2) : ‖q.derivative.eval s‖ < 2 :=
  (polynomial_derivative_norm_le_sqrt q hq hnorm hs).trans_lt
    derivative_coefficient_series_sqrt_lt_two

end KungTraub
