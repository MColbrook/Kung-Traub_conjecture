import appendix_b_reference.KungTraubAppendices.ComplexFiniteFamilyGeometry
import appendix_b_reference.KungTraubAppendices.ComplexFiniteStageConstants
import appendix_b_reference.KungTraubAppendices.ComplexAdaptiveForbiddenSets

/-!
# Finite-scale complex adaptive adversary

The induction follows `KungTraub.FiniteAdversary`, with complex kernels,
projected conjugate evaluation vectors, Appendix B's attained root discs and
its exact denominators. Uniform geometric containment is explicit family data
and must be established by the concrete polynomial stage construction.
-/
noncomputable section
namespace KungTraubAppendices
open KungTraub

def complexFiniteScaleContraction (n : ℕ) (m M K : ℝ) : ℝ :=
  complexRadiusFactor m M (1 + K / (2 * m)) (forbiddenWronskianCountBound n)

def complexFiniteScaleErrorConstant (n : ℕ) (m M R wmin K : ℝ) : ℝ :=
  let θ := complexFiniteScaleContraction n m M K
  complexFiniteStageRadius (complexInitialRadius M K) θ n *
    (complexFiniteStageState n (forbiddenWronskianCountBound n) M R wmin (complexInitialRadius M K) θ n).2 / (4 * M)

theorem complexFiniteScaleContraction_pos (n : ℕ) {m M K : ℝ}
    (hm : 0 < m) (hM : 0 < M) (hK : 0 ≤ K) : 0 < complexFiniteScaleContraction n m M K := by
  sorry

theorem complexFiniteScaleErrorConstant_pos (n : ℕ) {m M R wmin K : ℝ}
    (hm : 0 < m) (hM : 0 < M) (hR : 0 < R) (hwmin : 0 < wmin) (hK : 0 ≤ K) :
    0 < complexFiniteScaleErrorConstant n m M R wmin K := by
  sorry

theorem ComplexFiniteRootFamily.finite_adversary {n : ℕ} (_hn : 0 < n)
    {ε m M R wmin K : ℝ} {x : ℂ} (D : ComplexFiniteRootFamily n ε x m M R wmin K)
    (hm : 0 < m) (hM : 0 < M) (hR : 0 < R) (hwmin : 0 < wmin) (hK : 0 ≤ K)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hhalf : R * ε ≤ 1 / 2)
    (A : ComplexAffineAlgorithm (EuclideanSpace ℂ (Fin (n + 1))) n) :
    ∃ u : EuclideanSpace ℂ (Fin (n + 1)), ‖u‖ ≤ 1 ∧
      complexFiniteScaleErrorConstant n m M R wmin K * ε ^ orderBound n ≤ ‖A.run u x - D.root u‖ ∧
      ∀ i : Fin n, ∀ z : ℂ, (A.actualObservation u x i).location = some z → D.root u ≠ z := by
  sorry

end KungTraubAppendices
