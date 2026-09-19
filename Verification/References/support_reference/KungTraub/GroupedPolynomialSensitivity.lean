import support_reference.KungTraub.GenericRealPolynomialSensitivity
import support_reference.KungTraub.GroupedIndexing

/-!
# Real polynomial sensitivity after complete evaluation groups

The supplied real rows may be the flattened observations of a grouped algorithm.
The selected-rank exponent bound is discharged by the actual group indexing:
the conclusion has the exact product exponent after the first j groups.
-/

noncomputable section
namespace KungTraub

theorem grouped_real_kernel_projected_sensitivity_lower_bound {k j : ℕ}
    (sizes : Fin k → ℕ) (hsizes : ∀ i, 0 < sizes i) (hj : 0 < j) (hjk : j ≤ k)
    (L : ℕ → Polynomial ℝ →ₗ[ℝ] ℝ) (α x : ℝ)
    (γ : ℕ → ℝ) (hγ : ∀ i < groupedPrefixCount sizes j, 0 < γ i)
    {ε R wmin w : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 < R)
    (hwmin : 0 < wmin) (hw : wmin ≤ |w|)
    (ha : |α - x| ≤ R * ε) (hhalf : R * ε ≤ 1 / 2) (query : ℕ → Option ℂ)
    (havoid : ∀ i < groupedPrefixCount sizes j, ∀ z ∈ polynomialKernelForbiddenSet
      (complexifyPolynomialObservations L) (i + 1) (groupedObservationCount sizes)
        (x : ℂ) (query i),
      γ i * ε ^ groupedScalarExponent sizes i ≤ ‖(α : ℂ) - z‖) :
    (wmin * sensitivityPolynomialConstant (groupedObservationCount sizes) γ
      (groupedPrefixCount sizes j) / (2 * R + 2)) * ε ^ groupedStageExponent sizes j ≤
      ‖(scalarPrefixKernel
        (fun i => (L i).comp (realParameterPolynomialMap (groupedObservationCount sizes) ε))
        (groupedPrefixCount sizes j)).starProjection
        (realPolynomialEvaluationVector (groupedObservationCount sizes) ε w (α - x))‖ := by
  sorry

end KungTraub
