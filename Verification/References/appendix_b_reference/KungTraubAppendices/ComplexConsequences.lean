import appendix_b_reference.KungTraubAppendices.ComplexDefinitions
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
  sorry

/-- Divergence along nonroot starts contradicts a full punctured-neighbourhood bound. -/
theorem not_complexLocalOrderAt_of_divergence {T : (ℂ → ℂ) → ℂ → ℂ}
    {f : ℂ → ℂ} {α : ℂ} {p : ℝ} {starts : ℕ → ℂ}
    (hw : ComplexWitnessData f α starts)
    (hd : Tendsto (fun i => complexErrorRatio T f α p (starts i)) atTop atTop) :
    ¬ ComplexLocalOrderAt T f α p := by
  sorry

/-- An entire witness rules out universal order on all open holomorphic domains.
 -/
theorem ComplexEntireCounterexample.not_complexUniversalLocalOrder {n : ℕ}
    {A : ComplexAlgorithm n} {p : ℝ} (h : ComplexEntireCounterexample A.run p) :
    ¬ ComplexUniversalLocalOrder A p := by
  sorry

end KungTraubAppendices
