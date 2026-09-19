import KungTraubAppendices.ComplexDefinitions
import Mathlib.Tactic

/-!
# Local-order consequences of the complex witness

The argument follows `KungTraub.Consequences`, with complex norms and
holomorphic input functions on arbitrary open domains.
-/

noncomputable section

open Filter
open scoped Topology

namespace KungTraubAppendices

/-- The derivative bound on the disc makes its distinguished zero simple. -/
theorem ComplexWitnessData.simpleComplexRoot {f : ℂ → ℂ} {α : ℂ}
    {starts : ℕ → ℂ} (h : ComplexWitnessData f α starts) : SimpleComplexRoot f α := by
  refine ⟨h.2.2.1, ?_⟩
  intro hzero
  have hbound := h.2.1 α h.2.2.2.1.le
  rw [hzero] at hbound
  norm_num at hbound

/-- Divergence along nonroot starts contradicts a full punctured-neighbourhood bound. -/
theorem not_complexLocalOrderAt_of_divergence {T : (ℂ → ℂ) → ℂ → ℂ}
    {f : ℂ → ℂ} {α : ℂ} {p : ℝ} {starts : ℕ → ℂ}
    (hw : ComplexWitnessData f α starts)
    (hd : Tendsto (fun i => complexErrorRatio T f α p (starts i)) atTop atTop) :
    ¬ ComplexLocalOrderAt T f α p := by
  intro hlocal
  rcases hlocal with ⟨C, _, δ, hδ, hestimate⟩
  have hnear : ∀ᶠ i in atTop, ‖starts i - α‖ < δ := by
    have hball := hw.2.2.2.2.2.1.eventually (Metric.ball_mem_nhds α hδ)
    simpa only [Metric.mem_ball, dist_eq_norm] using hball
  have hlarge : ∀ᶠ i in atTop, C < complexErrorRatio T f α p (starts i) :=
    hd.eventually (eventually_gt_atTop C)
  obtain ⟨i, hi_near, hi_large⟩ := (hnear.and hlarge).exists
  have hpositive : 0 < ‖starts i - α‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (hw.2.2.2.2.2.2 i))
  have hdenominator : 0 < Real.rpow ‖starts i - α‖ p :=
    Real.rpow_pos_of_pos hpositive p
  have hsmall : complexErrorRatio T f α p (starts i) ≤ C :=
    (div_le_iff₀ hdenominator).2 (hestimate (starts i) hpositive hi_near)
  exact (not_lt_of_ge hsmall) hi_large

/-- An entire witness rules out universal order on all open holomorphic domains.
 -/
theorem ComplexEntireCounterexample.not_complexUniversalLocalOrder {n : ℕ}
    {A : ComplexAlgorithm n} {p : ℝ} (h : ComplexEntireCounterexample A.run p) :
    ¬ ComplexUniversalLocalOrder A p := by
  rcases h with ⟨f, α, starts, hw, hd⟩
  intro huniversal
  rcases huniversal Set.univ isOpen_univ f hw.1.differentiableOn α
      (Set.mem_univ α) hw.simpleComplexRoot with ⟨C, hC, δ, hδ, hestimate⟩
  apply not_complexLocalOrderAt_of_divergence hw hd
  exact ⟨C, hC, δ, hδ, fun x hx hnear => (hestimate x hx hnear).2.2⟩

end KungTraubAppendices
