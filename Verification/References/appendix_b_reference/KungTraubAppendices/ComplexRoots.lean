import appendix_b_reference.KungTraubAppendices.ComplexDefinitions
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Tactic

/-!
# Roots of near-identity complex stage families

The roots in Appendix B can be obtained by contraction under the same value
and derivative bounds as the paper's Rouché argument. Mathlib's `ContractingWith`
supplies the fixed-point theorem; its convex mean-value theorem supplies the
segment estimate.
-/

noncomputable section

open scoped NNReal

namespace KungTraubAppendices

/-- A derivative bound for `f - id` controls the correction map on the full disc. -/
theorem identity_sub_lipschitz_on_unit_disc {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (c : ℝ≥0)
    (hderiv : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖deriv f z - 1‖ ≤ (c : ℝ)) :
    LipschitzOnWith c (fun z => z - f z) (Metric.closedBall (0 : ℂ) 1) := by
  sorry

/-- The same correction estimate gives both sides of the Lipschitz bounds. -/
theorem near_identity_bilipschitz_on_unit_disc {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (c : ℝ≥0)
    (hderiv : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖deriv f z - 1‖ ≤ (c : ℝ))
    {z t : ℂ} (hz : ‖z‖ ≤ 1) (ht : ‖t‖ ≤ 1) :
    (1 - (c : ℝ)) * ‖z - t‖ ≤ ‖f z - f t‖ ∧
      ‖f z - f t‖ ≤ (1 + (c : ℝ)) * ‖z - t‖ := by
  sorry

/-- The near-identity bounds produce a unique simple root in the entire
closed unit disc, with the exact stronger location bound used in the construction. -/
theorem exists_unique_simple_root_on_unit_disc {f : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (hvalue : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖f z - z‖ ≤ (1 / 16 : ℝ))
    (hderiv : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖deriv f z - 1‖ ≤ (1 / 16 : ℝ)) :
    ∃ α : ℂ, ‖α‖ ≤ (1 / 16 : ℝ) ∧ SimpleComplexRoot f α ∧
      ∀ z : ℂ, ‖z‖ ≤ 1 → f z = 0 → z = α := by
  sorry

end KungTraubAppendices
