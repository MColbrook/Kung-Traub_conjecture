import KungTraubAppendices.ComplexPolynomialInformation
import KungTraubAppendices.ComplexParameterGeometry
import KungTraub.PolynomialKernelSensitivity
import KungTraub.PolynomialNormalization

/-!
# Complex projected sensitivity from polynomial forbidden sets

Bilinear evaluation of the scaled polynomial family is represented by the
Hermitian inner product with the conjugated evaluation vector.

The minimum-degree and Wronskian estimates use `KungTraub.PolynomialInformation`,
`KungTraub.PolynomialNormalization` and `KungTraub.PolynomialKernelSensitivity`.
Normalization and projection follow `KungTraub.RealPolynomialSensitivity`.
A normalized minimum-degree kernel polynomial gives the sensitivity bound
from the distances to the prefix forbidden sets.
-/

noncomputable section

open KungTraub
open scoped BigOperators

namespace KungTraubAppendices

/-- The exact complex evaluation vector, with the constant coordinate scaled by ε. -/
def complexPolynomialEvaluationVector (n : ℕ) (ε : ℝ) (w s : ℂ) :
    EuclideanSpace ℂ (Fin (n + 1)) :=
  WithLp.toLp 2 (fun i => w * (if i = 0 then (ε : ℂ) else s ^ i.val))

/-- Bilinear evaluation of a parameter equals evaluation of its actual polynomial perturbation. -/
theorem complexPolynomialEvaluationVector_bilinear {n : ℕ} (ε : ℝ) (w s : ℂ)
    (h : EuclideanSpace ℂ (Fin (n + 1))) :
    complexBilinearDot h (complexPolynomialEvaluationVector n ε w s) =
      w * (complexParameterPolynomialMap n ε h).eval s := by
  simp only [complexBilinearDot, complexPolynomialEvaluationVector,
    complexParameterPolynomialMap, LinearMap.comp_apply,
    polynomialOfCoefficientsLinearMap_apply, polynomialOfCoefficients,
    Polynomial.eval_finsetSum, Polynomial.eval_monomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i = 0
  · subst i
    simp [complexConstantScaleMap]
    ring
  · simp [complexConstantScaleMap, hi]
    ring

/-- The actual normalized direction has the weighted inverse-scale value used in Appendix A. -/
theorem complexNormalizedPolynomialDirection_value {n : ℕ} (q : Polynomial ℂ)
    (hdegree : q.natDegree ≤ n) {ε : ℝ} (hε : 0 < ε) (w s : ℂ) :
    ‖complexBilinearDot (complexNormalizedPolynomialDirection (n := n) q ε)
      (complexPolynomialEvaluationVector n ε w s)‖ =
      ‖w * q.eval s‖ / ‖inverseConstantScale ε (coefficientVector n q)‖ := by
  rw [complexPolynomialEvaluationVector_bilinear,
    complexNormalizedPolynomialDirection_polynomial q hdegree hε, Polynomial.eval_smul]
  simp only [smul_eq_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm]
  ring

/-- Choose a nonzero minimum-degree complex kernel polynomial with coefficient norm one.
The degree bound includes the constant-polynomial and empty-prefix cases. -/
theorem exists_unit_complex_minimum_degree_kernel_polynomial {n j : ℕ}
    (L : ℕ → Polynomial ℂ →ₗ[ℂ] ℂ) (hjn : j ≤ n) :
    ∃ q : Polynomial ℂ, q ≠ 0 ∧ q.natDegree ≤ j ∧
      ‖coefficientVector n q‖ = 1 ∧ (∀ i < j, L i q = 0) ∧
      ∀ r : Polynomial ℂ, r ≠ 0 → (∀ i < j, L i r = 0) → q.natDegree ≤ r.natDegree := by
  obtain ⟨p, hp, hpdegree, hLp, hmin⟩ := exists_minimum_degree_kernel_polynomial L j
  obtain ⟨c, q, hc, rfl, _, hnorm, _⟩ :=
    exists_polynomial_unit_coefficient_norm p hp (hpdegree.trans hjn)
  have hdegree : (c • p).natDegree = p.natDegree := Polynomial.natDegree_smul p hc
  refine ⟨c • p, smul_ne_zero hc hp, by rwa [hdegree], hnorm, ?_, ?_⟩
  · intro i hi
    rw [map_smul, hLp i hi, smul_zero]
  · intro r hr hLr
    rw [hdegree]
    exact hmin r hr hLr

/-- The positive-stage projected bound follows from the complex prefix forbidden sets. -/
theorem complex_kernel_projected_sensitivity_lower_bound {n j : ℕ}
    (hj : 0 < j) (hjn : j ≤ n)
    (L : ℕ → Polynomial ℂ →ₗ[ℂ] ℂ) (α x : ℂ)
    (γ : ℕ → ℝ) (hγ : ∀ i < j, 0 < γ i)
    {ε R wmin : ℝ} {w : ℂ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 < R)
    (hwmin : 0 < wmin) (hw : wmin ≤ ‖w‖)
    (ha : ‖α - x‖ ≤ R * ε) (hhalf : R * ε ≤ 1 / 2) (query : ℕ → Option ℂ)
    (havoid : ∀ i < j, ∀ z ∈ polynomialKernelForbiddenSet L (i + 1) n x (query i),
      γ i * ε ^ orderBound i ≤ ‖α - z‖) :
    (wmin * sensitivityPolynomialConstant n γ j / (2 * R + 2)) * ε ^ orderBound j ≤
      ‖(scalarPrefixKernel (fun i => (L i).comp (complexParameterPolynomialMap n ε)) j).starProjection
        (complexConjVector (complexPolynomialEvaluationVector n ε w (α - x)))‖ := by
  obtain ⟨q, hq, hdegree, hnorm, hLq, hmin⟩ :=
    exists_unit_complex_minimum_degree_kernel_polynomial L hjn
  have hbound := minimum_degree_kernel_weighted_inverse_scale_lower_bound hj L q hq hLq hmin
    (hdegree.trans hjn) hnorm α x w γ hγ hε hε1 hR hwmin hw ha hhalf query havoid
  rw [← complexNormalizedPolynomialDirection_value q (hdegree.trans hjn) hε w (α - x)] at hbound
  have hproj := norm_complexBilinearDot_le_projected _
    (complexNormalizedPolynomialDirection_mem_kernel L q (hdegree.trans hjn) hLq hε)
    (complexPolynomialEvaluationVector n ε w (α - x))
  rw [complexNormalizedPolynomialDirection_norm q hnorm hε, mul_one] at hproj
  exact hbound.trans hproj

/-- The same bound applies to the actual direction selected by complex affine rules.
The explicit query-location sequence is used only in the forbidden-set premise. -/
theorem ComplexAffineAlgorithm.projected_sensitivity_of_polynomial_forbidden_avoidance
    {n budget j : ℕ}
    (A : ComplexAffineAlgorithm (EuclideanSpace ℂ (Fin (n + 1))) budget)
    (hj : 0 < j) (hjn : j ≤ n)
    (u : EuclideanSpace ℂ (Fin (n + 1))) (α x : ℂ)
    (γ : ℕ → ℝ) (hγ : ∀ i < j, 0 < γ i)
    {ε R wmin : ℝ} {w : ℂ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 < R)
    (hwmin : 0 < wmin) (hw : wmin ≤ ‖w‖)
    (ha : ‖α - x‖ ≤ R * ε) (hhalf : R * ε ≤ 1 / 2) (query : ℕ → Option ℂ)
    (havoid : ∀ i < j, ∀ z ∈ polynomialKernelForbiddenSet
      (A.polynomialObservation u x ε) (i + 1) n x (query i),
      γ i * ε ^ orderBound i ≤ ‖α - z‖) :
    (wmin * sensitivityPolynomialConstant n γ j / (2 * R + 2)) * ε ^ orderBound j ≤
      ‖(A.direction u x j).starProjection
        (complexConjVector (complexPolynomialEvaluationVector n ε w (α - x)))‖ := by
  rw [A.direction_eq_polynomial_kernel u x hε.ne' j]
  exact complex_kernel_projected_sensitivity_lower_bound hj hjn
    (A.polynomialObservation u x ε) α x γ hγ hε hε1 hR hwmin hw ha hhalf query havoid

end KungTraubAppendices
