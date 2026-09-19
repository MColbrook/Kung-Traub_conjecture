import support_reference.KungTraub.PolynomialDirections
import support_reference.KungTraub.PolynomialKernelSensitivity
import support_reference.KungTraub.RealPolynomialKernels

/-!
# Sensitivity in the real parameter space

Real kernel polynomials are normalized in the coefficient norm before the complex
root argument is applied. The final sensitivity estimate concerns the orthogonal
projection in the real parameter space.
-/

noncomputable section
namespace KungTraub

theorem realCoefficientVector_smul (n : ℕ) (c : ℝ) (q : Polynomial ℝ) :
    realCoefficientVector n (c • q) = c • realCoefficientVector n q := by
  sorry

theorem realCoefficientVector_norm_pos {n : ℕ} (q : Polynomial ℝ)
    (hq : q ≠ 0) (hdegree : q.natDegree ≤ n) :
    0 < ‖realCoefficientVector n q‖ := by
  sorry

/-- A nonzero real minimum-degree kernel polynomial can be chosen with coefficient
norm one, without changing its degree or its kernel minimality. -/
theorem exists_unit_real_minimum_degree_kernel_polynomial {n j : ℕ}
    (L : ℕ → Polynomial ℝ →ₗ[ℝ] ℝ) (hjn : j ≤ n) :
    ∃ q : Polynomial ℝ, q ≠ 0 ∧ q.natDegree ≤ j ∧
      ‖realCoefficientVector n q‖ = 1 ∧ (∀ i < j, L i q = 0) ∧
      ∀ r : Polynomial ℝ, r ≠ 0 → (∀ i < j, L i r = 0) → q.natDegree ≤ r.natDegree := by
  sorry

/-- Complexification preserves the normalized real minimum-degree polynomial and
transfers the complex root-distance argument to its real value. -/
theorem real_minimum_degree_kernel_value_lower_bound {n j : ℕ} (hj : 0 < j)
    (L : ℕ → Polynomial ℝ →ₗ[ℝ] ℝ) (q : Polynomial ℝ) (hq : q ≠ 0)
    (hLq : ∀ i < j, L i q = 0)
    (hmin : ∀ r : Polynomial ℝ, r ≠ 0 → (∀ i < j, L i r = 0) → q.natDegree ≤ r.natDegree)
    (hdn : q.natDegree ≤ n) (hnorm : ‖realCoefficientVector n q‖ = 1)
    (α x : ℝ) (ha : |α - x| ≤ 1 / 2) (γ : ℕ → ℝ) (hγ : ∀ i < j, 0 < γ i)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (query : ℕ → Option ℂ)
    (havoid : ∀ i < j, ∀ z ∈ polynomialKernelForbiddenSet
      (complexifyPolynomialObservations L) (i + 1) n (x : ℂ) (query i),
      γ i * ε ^ orderBound i ≤ ‖(α : ℂ) - z‖) :
    sensitivityPolynomialConstant n γ j * ε ^ orderBound j ≤ |q.eval (α - x)| := by
  sorry

/-- Full positive-stage sensitivity for arbitrary real scalar polynomial observations.
The normalized minimum-degree polynomial and its admissible real direction are
constructed in the proof. The only geometric input is avoidance of the actual
complexified prefix forbidden sets. -/
theorem real_kernel_projected_sensitivity_lower_bound {n j : ℕ} (hj : 0 < j) (hjn : j ≤ n)
    (L : ℕ → Polynomial ℝ →ₗ[ℝ] ℝ) (α x : ℝ)
    (γ : ℕ → ℝ) (hγ : ∀ i < j, 0 < γ i)
    {ε R wmin w : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 < R)
    (hwmin : 0 < wmin) (hw : wmin ≤ |w|)
    (ha : |α - x| ≤ R * ε) (hhalf : R * ε ≤ 1 / 2) (query : ℕ → Option ℂ)
    (havoid : ∀ i < j, ∀ z ∈ polynomialKernelForbiddenSet
      (complexifyPolynomialObservations L) (i + 1) n (x : ℂ) (query i),
      γ i * ε ^ orderBound i ≤ ‖(α : ℂ) - z‖) :
    (wmin * sensitivityPolynomialConstant n γ j / (2 * R + 2)) * ε ^ orderBound j ≤
      ‖(scalarPrefixKernel (fun i => (L i).comp (realParameterPolynomialMap n ε)) j).starProjection
        (realPolynomialEvaluationVector n ε w (α - x))‖ := by
  sorry

end KungTraub
