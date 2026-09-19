import support_reference.KungTraub.RealPolynomialSensitivity
import support_reference.KungTraub.AdaptiveForbiddenSets

/-!
# Sensitivity of the actual adaptive parameter fibre

The finite-stage projection estimate follows from avoidance of the algorithm's
prefix forbidden sets.
-/

noncomputable section
namespace KungTraub

theorem AffineAlgorithm.projected_sensitivity_of_forbidden_avoidance {n j : ℕ}
    (A : AffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) n)
    (hj : 0 < j) (hjn : j ≤ n)
    (u : EuclideanSpace ℝ (Fin (n + 1))) (α x : ℝ)
    (γ : ℕ → ℝ) (hγ : ∀ i < j, 0 < γ i)
    {ε R wmin w : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 < R)
    (hwmin : 0 < wmin) (hw : wmin ≤ |w|)
    (ha : |α - x| ≤ R * ε) (hhalf : R * ε ≤ 1 / 2)
    (havoid : ∀ i < j, ∀ z ∈ A.forbiddenSet u x ε i,
      γ i * ε ^ orderBound i ≤ ‖(α : ℂ) - z‖) :
    (wmin * sensitivityPolynomialConstant n γ j / (2 * R + 2)) * ε ^ orderBound j ≤
      ‖(A.direction u x j).starProjection (realPolynomialEvaluationVector n ε w (α - x))‖ := by
  sorry

end KungTraub
