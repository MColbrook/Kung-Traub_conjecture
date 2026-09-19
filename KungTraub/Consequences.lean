import KungTraub.Definitions
import Mathlib.Tactic

/-!
# Consequences of an entire counterexample

These supporting implications connect the full counterexample predicate to failure of the
universal local-order estimate in Theorem 1.1 of Matthew J. Colbrook's manuscript.
The limit and ordered-field arguments use Mathlib's neighbourhood filters and real powers.
-/

noncomputable section

open Filter
open scoped Topology

namespace KungTraub

theorem EntireWitnessData.simpleRealRoot {F : ℂ → ℂ} {α : ℝ} {starts : ℕ → ℝ}
    (h : EntireWitnessData F α starts) : SimpleRealRoot (realRestriction F) α := by
  refine ⟨h.2.2.1, ne_of_gt ?_⟩
  exact lt_of_lt_of_le (by norm_num) (h.2.1 α).1

theorem ErrorRatioDiverges.not_localOrderAt {T : RealUpdate} {F : ℂ → ℂ}
    {α p : ℝ} {starts : ℕ → ℝ} (hw : EntireWitnessData F α starts)
    (hd : ErrorRatioDiverges T F α starts p) :
    ¬ LocalOrderAt T (realRestriction F) α p := by
  intro hlocal
  rcases hlocal with ⟨C, _, δ, hδ, hestimate⟩
  have hnear : ∀ᶠ s in atTop, |starts s - α| < δ := by
    have hball := hw.2.2.2.2.1.eventually (Metric.ball_mem_nhds α hδ)
    simpa only [Metric.mem_ball, Real.dist_eq] using hball
  have hlarge : ∀ᶠ s in atTop, C < errorRatio T (realRestriction F) α p (starts s) :=
    hd.eventually (eventually_gt_atTop C)
  obtain ⟨s, hsnear, hslarge⟩ := (hnear.and hlarge).exists
  have hpositive : 0 < |starts s - α| :=
    abs_pos.mpr (sub_ne_zero.mpr (hw.2.2.2.2.2 s))
  have hdenominator : 0 < Real.rpow |starts s - α| p :=
    Real.rpow_pos_of_pos hpositive p
  have hsmall : errorRatio T (realRestriction F) α p (starts s) ≤ C := by
    exact (div_le_iff₀ hdenominator).2 (hestimate (starts s) hpositive hsnear)
  exact (not_lt_of_ge hsmall) hslarge

theorem EntireCounterexample.not_entireUniversalLocalOrder {T : RealUpdate} {p : ℝ}
    (h : EntireCounterexample T p) : ¬ EntireUniversalLocalOrder T p := by
  rcases h with ⟨F, α, starts, hw, hd⟩
  intro huniversal
  exact hd.not_localOrderAt hw (huniversal F hw.1 α hw.simpleRealRoot)

end KungTraub
