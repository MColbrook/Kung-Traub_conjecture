import support_reference.KungTraub.GroupedAdversaryStep
import support_reference.KungTraub.GroupedStageConstants
import support_reference.KungTraub.GroupedForbiddenSets
import support_reference.KungTraub.GroupedPolynomialSensitivity

/-!
# The finite-scale adversary for prescribed evaluation groups

The induction constructs actual parameter balls. Their invariants contain the
proved polynomial forbidden sets, and the sensitivity estimate is obtained from
their avoidance. All constants below depend only on the degree and analytic
family bounds, before the algorithm, scale and transcript are chosen.
-/

noncomputable section

namespace KungTraub

def groupedFiniteScaleContraction (n : ℕ) (m M K : ℝ) : ℝ :=
  adversaryRadiusFactor m M (1 + K / (2 * m)) ((n * forbiddenWronskianCountBound n))

def groupedFiniteScaleErrorConstant {k : ℕ} (sizes : Fin k → ℕ) (m M R wmin K : ℝ) : ℝ :=
  let n := groupedObservationCount sizes
  let θ := groupedFiniteScaleContraction n m M K
  finiteStageRadius θ k *
    (groupedFiniteStageState sizes n ((n * forbiddenWronskianCountBound n)) M R wmin θ k).2 / (2 * M)

theorem groupedFiniteScaleContraction_pos (n : ℕ) {m M K : ℝ}
    (hm : 0 < m) (hM : 0 < M) (hK : 0 ≤ K) : 0 < groupedFiniteScaleContraction n m M K := by
  sorry

theorem groupedFiniteScaleErrorConstant_pos {k : ℕ} (sizes : Fin k → ℕ) {m M R wmin K : ℝ}
    (hm : 0 < m) (hM : 0 < M) (hR : 0 < R) (hwmin : 0 < wmin) (hK : 0 ≤ K) :
    0 < groupedFiniteScaleErrorConstant sizes m M R wmin K := by
  sorry

theorem FiniteRootFamily.grouped_finite_adversary {k : ℕ} (sizes : Fin k → ℕ)
    (_hk : 0 < k) (hsizes : ∀ i, 0 < sizes i)
    {ε x m M R wmin K : ℝ} (D : FiniteRootFamily (groupedObservationCount sizes) ε x m M R wmin K)
    (hm : 0 < m) (hM : 0 < M) (hR : 0 < R) (hwmin : 0 < wmin) (hK : 0 ≤ K)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hhalf : R * ε ≤ 1 / 2)
    (A : GroupedAffineAlgorithm (EuclideanSpace ℝ (Fin (groupedObservationCount sizes + 1))) sizes) :
    ∃ u : EuclideanSpace ℝ (Fin (groupedObservationCount sizes + 1)), ‖u‖ ≤ 1 ∧
      groupedFiniteScaleErrorConstant sizes m M R wmin K * ε ^ groupedStageExponent sizes k ≤ |A.run u x - D.root u| ∧
      ∀ i : Fin k, ∀ slot : Fin (sizes i), ∀ z : ℝ,
        (A.actualObservations u x i slot).location = some z → D.root u ≠ z := by
  sorry

end KungTraub
