import KungTraubAppendices.ComplexDefinitions
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
  apply Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (convex_closedBall (0 : ℂ) (1 : ℝ))
  · intro z _
    exact ((hasDerivAt_id z).sub (hf z).hasDerivAt).hasDerivWithinAt
  · intro z hz
    have hbound : ‖(1 : ℂ) - deriv f z‖ ≤ (c : ℝ) := by
      rw [norm_sub_rev]
      exact hderiv z (by simpa using hz)
    exact_mod_cast hbound

/-- The same correction estimate gives both sides of the Lipschitz bounds. -/
theorem near_identity_bilipschitz_on_unit_disc {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (c : ℝ≥0)
    (hderiv : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖deriv f z - 1‖ ≤ (c : ℝ))
    {z t : ℂ} (hz : ‖z‖ ≤ 1) (ht : ‖t‖ ≤ 1) :
    (1 - (c : ℝ)) * ‖z - t‖ ≤ ‖f z - f t‖ ∧
      ‖f z - f t‖ ≤ (1 + (c : ℝ)) * ‖z - t‖ := by
  have hcorrection : ‖(z - f z) - (t - f t)‖ ≤ (c : ℝ) * ‖z - t‖ := by
    simpa only [dist_eq_norm] using
      (identity_sub_lipschitz_on_unit_disc hf c hderiv).dist_le_mul
        z (by simpa using hz) t (by simpa using ht)
  have hsum : z - t = (f z - f t) + ((z - f z) - (t - f t)) := by ring
  have hsub : f z - f t = (z - t) - ((z - f z) - (t - f t)) := by ring
  constructor
  · have htriangle := norm_add_le (f z - f t) ((z - f z) - (t - f t))
    rw [← hsum] at htriangle
    nlinarith
  · have htriangle := norm_sub_le (z - t) ((z - f z) - (t - f t))
    rw [← hsub] at htriangle
    nlinarith

/-- The near-identity bounds produce a unique simple root in the entire
closed unit disc, with the exact stronger location bound used in the construction. -/
theorem exists_unique_simple_root_on_unit_disc {f : ℂ → ℂ}
    (hf : Differentiable ℂ f)
    (hvalue : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖f z - z‖ ≤ (1 / 16 : ℝ))
    (hderiv : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖deriv f z - 1‖ ≤ (1 / 16 : ℝ)) :
    ∃ α : ℂ, ‖α‖ ≤ (1 / 16 : ℝ) ∧ SimpleComplexRoot f α ∧
      ∀ z : ℂ, ‖z‖ ≤ 1 → f z = 0 → z = α := by
  let g : ℂ → ℂ := fun z => z - f z
  let D : Set ℂ := Metric.closedBall 0 1
  have hmaps : Set.MapsTo g D D := by
    intro z hz
    have hbound := hvalue z (by simpa [D] using hz)
    have hsmall : ‖z - f z‖ ≤ 1 := by
      rw [norm_sub_rev]
      exact hbound.trans (by norm_num)
    simpa [g, D] using hsmall
  have hlip : LipschitzOnWith (1 / 16 : ℝ≥0) g D := by
    exact identity_sub_lipschitz_on_unit_disc hf (1 / 16) (by simpa using hderiv)
  have hcontract : ContractingWith (1 / 16 : ℝ≥0) (hmaps.restrict g D D) := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul ?_⟩
    intro z t
    exact hlip.dist_le_mul z.val z.property t.val t.property
  obtain ⟨α, hα, hfixed, _⟩ := ContractingWith.exists_fixedPoint'
    Metric.isClosed_closedBall.isComplete hmaps hcontract (x := (0 : ℂ))
      (by simp [D]) (edist_ne_top _ _)
  have hαnorm : ‖α‖ ≤ 1 := by simpa [D] using hα
  have hzero : f α = 0 := by
    have heq : α - f α = α := hfixed
    exact sub_eq_self.mp heq
  have hαsmall : ‖α‖ ≤ (1 / 16 : ℝ) := by
    simpa [hzero] using hvalue α hαnorm
  have hsimple : SimpleComplexRoot f α := by
    refine ⟨hzero, ?_⟩
    intro hderiv_zero
    have hbound := hderiv α hαnorm
    rw [hderiv_zero] at hbound
    norm_num at hbound
  refine ⟨α, hαsmall, hsimple, ?_⟩
  intro z hz hz_zero
  have hdist := hlip.dist_le_mul z (by simpa [D] using hz) α hα
  simp only [g, hz_zero, hzero, sub_zero] at hdist
  have hnonnegative : 0 ≤ dist z α := dist_nonneg
  have hequal : dist z α = 0 := by
    norm_num at hdist
    linarith
  exact dist_eq_zero.mp hequal

end KungTraubAppendices
