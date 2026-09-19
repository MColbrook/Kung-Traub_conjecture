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
  sorry

theorem ErrorRatioDiverges.not_localOrderAt {T : RealUpdate} {F : ℂ → ℂ}
    {α p : ℝ} {starts : ℕ → ℝ} (hw : EntireWitnessData F α starts)
    (hd : ErrorRatioDiverges T F α starts p) :
    ¬ LocalOrderAt T (realRestriction F) α p := by
  sorry

theorem EntireCounterexample.not_entireUniversalLocalOrder {T : RealUpdate} {p : ℝ}
    (h : EntireCounterexample T p) : ¬ EntireUniversalLocalOrder T p := by
  sorry

end KungTraub
