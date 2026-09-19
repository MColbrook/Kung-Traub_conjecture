import appendix_b_reference.KungTraubAppendices.ComplexPolynomialInformation
import appendix_b_reference.KungTraubAppendices.ComplexParameterGeometry
import appendix_b_reference.KungTraub.PolynomialKernelSensitivity
import appendix_b_reference.KungTraub.PolynomialNormalization

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
  sorry

/-- The actual normalized direction has the weighted inverse-scale value used in Appendix A. -/
theorem complexNormalizedPolynomialDirection_value {n : ℕ} (q : Polynomial ℂ)
    (hdegree : q.natDegree ≤ n) {ε : ℝ} (hε : 0 < ε) (w s : ℂ) :
    ‖complexBilinearDot (complexNormalizedPolynomialDirection (n := n) q ε)
      (complexPolynomialEvaluationVector n ε w s)‖ =
      ‖w * q.eval s‖ / ‖inverseConstantScale ε (coefficientVector n q)‖ := by
  sorry

/-- Choose a nonzero minimum-degree complex kernel polynomial with coefficient norm one.
The degree bound includes the constant-polynomial and empty-prefix cases. -/
theorem exists_unit_complex_minimum_degree_kernel_polynomial {n j : ℕ}
    (L : ℕ → Polynomial ℂ →ₗ[ℂ] ℂ) (hjn : j ≤ n) :
    ∃ q : Polynomial ℂ, q ≠ 0 ∧ q.natDegree ≤ j ∧
      ‖coefficientVector n q‖ = 1 ∧ (∀ i < j, L i q = 0) ∧
      ∀ r : Polynomial ℂ, r ≠ 0 → (∀ i < j, L i r = 0) → q.natDegree ≤ r.natDegree := by
  sorry

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
  sorry

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
  sorry

end KungTraubAppendices
