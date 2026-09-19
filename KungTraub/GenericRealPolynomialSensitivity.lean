import KungTraub.GenericPolynomialSensitivity

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
  have hden : ‖inverseConstantScale ε (coefficientVector n (q.map (algebraMap ℝ ℂ)))‖ =
      ‖realInverseConstantScale ε (realCoefficientVector n q)‖ := by
    rw [← complexify_realCoefficientVector, ← complexify_realInverseConstantScale,
      complexifyEuclidean_norm]
  have heval : (q.map (algebraMap ℝ ℂ)).eval (s : ℂ) = ((q.eval s : ℝ) : ℂ) := by
    exact Polynomial.eval_map_apply (p := q) (algebraMap ℝ ℂ) s
  have hbound := weighted_polynomial_inverse_scale_lower_bound_exponent hB (q.map (algebraMap ℝ ℂ))
    (Polynomial.natDegree_map_le.trans hdegree)
    (by rw [coefficientVector_map_real_norm, hnorm]) γ hγ (a := (s : ℂ)) (w := (w : ℂ))
    hε hε1 hR hwmin (by simpa using hw) (by simpa using hs) hhalf
    (by simpa only [heval, Complex.norm_real, Real.norm_eq_abs] using hvalue)
  rw [realNormalizedPolynomialDirection_value q hdegree hε]
  simpa only [heval, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs, hden] using hbound

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
  have hbound := realNormalizedPolynomialDirection_lower_bound_exponent hB q hdegree hnorm γ hγ
    hε hε1 hR hwmin hw hs hhalf hvalue
  have hproj := abs_inner_le_projected_norm_mul _
    (realNormalizedPolynomialDirection_mem_kernel L q hdegree hLq hε)
    (realPolynomialEvaluationVector n ε w s)
  rw [realNormalizedPolynomialDirection_norm q hnorm hε, mul_one] at hproj
  exact hbound.trans hproj

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
  have hbound := minimum_degree_kernel_value_lower_bound_exponents E hE (complexifyPolynomialObservations L)
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
  obtain ⟨q, hq, hdegree, hnorm, hLq, hmin⟩ :=
    exists_unit_real_minimum_degree_kernel_polynomial L hjn
  apply real_polynomial_kernel_projected_sensitivity_lower_bound_exponent hB L q (hdegree.trans hjn)
    hnorm hLq γ hγ hε hε1 hR hwmin hw ha hhalf
  exact real_minimum_degree_kernel_value_lower_bound_exponents E hE L q hq hLq hmin
    (hdegree.trans hjn) hnorm α x (ha.trans hhalf) γ hγ hε hε1 query havoid

end KungTraub

