import support_reference.KungTraub.GenericPolynomialSensitivity

/-!
# Real sensitivity for a prescribed exponent sequence

A normalized real minimum-degree kernel polynomial determines an admissible
real direction. The exponent follows from the rank-index sum bound.
-/

noncomputable section
open scoped BigOperators
namespace KungTraub

theorem realNormalizedPolynomialDirection_lower_bound_exponent {n j B : ℕ} (hB : 0 < B)
    (q : Polynomial ℝ) (hdegree : q.natDegree ≤ n) (hnorm : ‖realCoefficientVector n q‖ = 1)
    (γ : ℕ → ℝ) (hγ : ∀ i < j, 0 < γ i)
    {ε R wmin w s : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 < R)
    (hwmin : 0 < wmin) (hw : wmin ≤ |w|)
    (hs : |s| ≤ R * ε) (hhalf : R * ε ≤ 1 / 2)
    (hvalue : sensitivityPolynomialConstant n γ j * ε ^ B ≤ |q.eval s|) :
    (wmin * sensitivityPolynomialConstant n γ j / (2 * R + 2)) * ε ^ B ≤
      |inner ℝ (realNormalizedPolynomialDirection (n := n) q ε)
        (realPolynomialEvaluationVector n ε w s)| := by
  sorry

theorem real_polynomial_kernel_projected_sensitivity_lower_bound_exponent {n j B : ℕ} (hB : 0 < B)
    (L : ℕ → Polynomial ℝ →ₗ[ℝ] ℝ) (q : Polynomial ℝ) (hdegree : q.natDegree ≤ n)
    (hnorm : ‖realCoefficientVector n q‖ = 1) (hLq : ∀ i < j, L i q = 0)
    (γ : ℕ → ℝ) (hγ : ∀ i < j, 0 < γ i)
    {ε R wmin w s : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 < R)
    (hwmin : 0 < wmin) (hw : wmin ≤ |w|)
    (hs : |s| ≤ R * ε) (hhalf : R * ε ≤ 1 / 2)
    (hvalue : sensitivityPolynomialConstant n γ j * ε ^ B ≤ |q.eval s|) :
    (wmin * sensitivityPolynomialConstant n γ j / (2 * R + 2)) * ε ^ B ≤
      ‖(scalarPrefixKernel (fun i => (L i).comp (realParameterPolynomialMap n ε)) j).starProjection
        (realPolynomialEvaluationVector n ε w s)‖ := by
  sorry

theorem real_minimum_degree_kernel_value_lower_bound_exponents {n j B : ℕ}
    (E : ℕ → ℕ)
    (hE : ∀ {d : ℕ} (indices : Fin d → Fin j), Function.Injective indices →
      (∑ k : Fin d, E (indices k).val) ≤ B)
    (L : ℕ → Polynomial ℝ →ₗ[ℝ] ℝ) (q : Polynomial ℝ) (hq : q ≠ 0)
    (hLq : ∀ i < j, L i q = 0)
    (hmin : ∀ r : Polynomial ℝ, r ≠ 0 → (∀ i < j, L i r = 0) → q.natDegree ≤ r.natDegree)
    (hdn : q.natDegree ≤ n) (hnorm : ‖realCoefficientVector n q‖ = 1)
    (α x : ℝ) (ha : |α - x| ≤ 1 / 2) (γ : ℕ → ℝ) (hγ : ∀ i < j, 0 < γ i)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (query : ℕ → Option ℂ)
    (havoid : ∀ i < j, ∀ z ∈ polynomialKernelForbiddenSet
      (complexifyPolynomialObservations L) (i + 1) n (x : ℂ) (query i),
      γ i * ε ^ E i ≤ ‖(α : ℂ) - z‖) :
    sensitivityPolynomialConstant n γ j * ε ^ B ≤ |q.eval (α - x)| := by
  sorry

theorem real_kernel_projected_sensitivity_lower_bound_exponents {n j B : ℕ}
    (hB : 0 < B) (E : ℕ → ℕ)
    (hE : ∀ {d : ℕ} (indices : Fin d → Fin j), Function.Injective indices →
      (∑ k : Fin d, E (indices k).val) ≤ B)
    (hjn : j ≤ n)
    (L : ℕ → Polynomial ℝ →ₗ[ℝ] ℝ) (α x : ℝ)
    (γ : ℕ → ℝ) (hγ : ∀ i < j, 0 < γ i)
    {ε R wmin w : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 < R)
    (hwmin : 0 < wmin) (hw : wmin ≤ |w|)
    (ha : |α - x| ≤ R * ε) (hhalf : R * ε ≤ 1 / 2) (query : ℕ → Option ℂ)
    (havoid : ∀ i < j, ∀ z ∈ polynomialKernelForbiddenSet
      (complexifyPolynomialObservations L) (i + 1) n (x : ℂ) (query i),
      γ i * ε ^ E i ≤ ‖(α : ℂ) - z‖) :
    (wmin * sensitivityPolynomialConstant n γ j / (2 * R + 2)) * ε ^ B ≤
      ‖(scalarPrefixKernel (fun i => (L i).comp (realParameterPolynomialMap n ε)) j).starProjection
        (realPolynomialEvaluationVector n ε w (α - x))‖ := by
  sorry

end KungTraub

