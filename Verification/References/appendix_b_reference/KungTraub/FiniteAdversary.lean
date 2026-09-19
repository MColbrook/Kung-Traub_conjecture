import appendix_b_reference.KungTraub.FiniteFamilyGeometry
import appendix_b_reference.KungTraub.FiniteStageConstants
import appendix_b_reference.KungTraub.AdaptiveForbiddenSets
import appendix_b_reference.KungTraub.AffinePolynomialSensitivity

/-!
# The finite-scale adaptive adversary

The induction constructs actual parameter balls. Their invariants contain the
proved polynomial forbidden sets, and the sensitivity estimate is obtained from
their avoidance. All constants below depend only on the degree and analytic
family bounds, before the algorithm, scale and transcript are chosen.
-/

noncomputable section

namespace KungTraub

def finiteScaleContraction (n : ℕ) (m M K : ℝ) : ℝ :=
  adversaryRadiusFactor m M (1 + K / (2 * m)) (forbiddenWronskianCountBound n)

def finiteScaleErrorConstant (n : ℕ) (m M R wmin K : ℝ) : ℝ :=
  let θ := finiteScaleContraction n m M K
  finiteStageRadius θ n *
    (finiteStageState n (forbiddenWronskianCountBound n) M R wmin θ n).2 / (2 * M)

theorem finiteScaleContraction_pos (n : ℕ) {m M K : ℝ}
    (hm : 0 < m) (hM : 0 < M) (hK : 0 ≤ K) : 0 < finiteScaleContraction n m M K := by
  sorry

theorem finiteScaleErrorConstant_pos (n : ℕ) {m M R wmin K : ℝ}
    (hm : 0 < m) (hM : 0 < M) (hR : 0 < R) (hwmin : 0 < wmin) (hK : 0 ≤ K) :
    0 < finiteScaleErrorConstant n m M R wmin K := by
  sorry

theorem FiniteRootFamily.initial_sensitivity_at {n : ℕ} {ε x m M R wmin K : ℝ}
    (D : FiniteRootFamily n ε x m M R wmin K)
    (A : AffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) n)
    (u : EuclideanSpace ℝ (Fin (n + 1))) (hu : ‖u‖ ≤ 1) (hε : 0 ≤ ε) :
    wmin * ε ≤ ‖(A.direction u x 0).starProjection (D.vector (D.root u))‖ := by
  sorry

theorem FiniteRootFamily.finite_adversary {n : ℕ} (_hn : 0 < n)
    {ε x m M R wmin K : ℝ} (D : FiniteRootFamily n ε x m M R wmin K)
    (hm : 0 < m) (hM : 0 < M) (hR : 0 < R) (hwmin : 0 < wmin) (hK : 0 ≤ K)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hhalf : R * ε ≤ 1 / 2)
    (A : AffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) n) :
    ∃ u : EuclideanSpace ℝ (Fin (n + 1)), ‖u‖ ≤ 1 ∧
      finiteScaleErrorConstant n m M R wmin K * ε ^ orderBound n ≤ |A.run u x - D.root u| ∧
      ∀ i : Fin n, ∀ z : ℝ, (A.actualObservation u x i).location = some z → D.root u ≠ z := by
  sorry

end KungTraub
