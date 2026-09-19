import KungTraub.PolynomialDirections
import KungTraub.PolynomialKernelSensitivity
import KungTraub.RealPolynomialKernels

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
  ext i
  simp [realCoefficientVector, Polynomial.coeff_smul]

theorem realCoefficientVector_norm_pos {n : ℕ} (q : Polynomial ℝ)
    (hq : q ≠ 0) (hdegree : q.natDegree ≤ n) :
    0 < ‖realCoefficientVector n q‖ := by
  rw [← coefficientVector_map_real_norm]
  exact norm_pos_iff.mpr (coefficientVector_ne_zero_of_natDegree_le
    (q.map (algebraMap ℝ ℂ)) (Polynomial.map_ne_zero hq)
    (Polynomial.natDegree_map_le.trans hdegree))

/-- A nonzero real minimum-degree kernel polynomial can be chosen with coefficient
norm one, without changing its degree or its kernel minimality. -/
theorem exists_unit_real_minimum_degree_kernel_polynomial {n j : ℕ}
    (L : ℕ → Polynomial ℝ →ₗ[ℝ] ℝ) (hjn : j ≤ n) :
    ∃ q : Polynomial ℝ, q ≠ 0 ∧ q.natDegree ≤ j ∧
      ‖realCoefficientVector n q‖ = 1 ∧ (∀ i < j, L i q = 0) ∧
      ∀ r : Polynomial ℝ, r ≠ 0 → (∀ i < j, L i r = 0) → q.natDegree ≤ r.natDegree := by
  obtain ⟨p, hp, hpdegree, hLp, hmin⟩ := exists_minimum_degree_kernel_polynomial L j
  have hnorm := realCoefficientVector_norm_pos p hp (hpdegree.trans hjn)
  let c : ℝ := ‖realCoefficientVector n p‖⁻¹
  have hc : 0 < c := inv_pos.mpr hnorm
  have hdegree : (c • p).natDegree = p.natDegree := Polynomial.natDegree_smul p hc.ne'
  refine ⟨c • p, smul_ne_zero hc.ne' hp, by rwa [hdegree], ?_, ?_, ?_⟩
  · rw [realCoefficientVector_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    exact inv_mul_cancel₀ hnorm.ne'
  · intro i hi
    rw [map_smul, hLp i hi, smul_zero]
  · intro r hr hLr
    rw [hdegree]
    exact hmin r hr hLr

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
  have hbound := minimum_degree_kernel_value_lower_bound hj (complexifyPolynomialObservations L)
    (q.map (algebraMap ℝ ℂ)) (real_polynomial_map_ne_zero q hq)
    (real_polynomial_map_annihilated L j q hLq)
    (real_minimum_degree_is_complex_minimum L j q hmin)
    (by rwa [real_polynomial_map_natDegree])
    (by rw [coefficientVector_map_real_norm, hnorm])
    (α : ℂ) (x : ℂ) (by simpa only [← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs] using ha) γ hγ hε hε1 query havoid
  have heval : (q.map (algebraMap ℝ ℂ)).eval ((α : ℂ) - (x : ℂ)) =
      ((q.eval (α - x) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_sub]
    exact Polynomial.eval_map_apply (p := q) (algebraMap ℝ ℂ) (α - x)
  simpa only [heval, Complex.norm_real, Real.norm_eq_abs] using hbound

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
  obtain ⟨q, hq, hdegree, hnorm, hLq, hmin⟩ :=
    exists_unit_real_minimum_degree_kernel_polynomial L hjn
  apply real_polynomial_kernel_projected_sensitivity_lower_bound L q (hdegree.trans hjn)
    hnorm hLq γ hγ hε hε1 hR hwmin hw ha hhalf
  exact real_minimum_degree_kernel_value_lower_bound hj L q hq hLq hmin
    (hdegree.trans hjn) hnorm α x (ha.trans hhalf) γ hγ hε hε1 query havoid

end KungTraub
