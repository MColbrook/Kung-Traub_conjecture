import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Avoidance of finitely many points

The choice of the next answer in Section 3 requires a real point separated from
at most `H` complex points. An equally spaced finite grid proves the manuscript's
bound without a measure estimate. The conclusion retains the full real interval
and the exact factor `4 * (H + 1)`.
-/

open Set

namespace KungTraub

theorem exists_far_from_finite_of_separated {X : Type*} [MetricSpace X]
    {H : ℕ} (S : Finset X) (hcard : S.card ≤ H) (grid : Fin (H + 1) → X)
    {δ : ℝ} (hsep : ∀ i j, i ≠ j → 2 * δ ≤ dist (grid i) (grid j)) :
    ∃ i, ∀ z ∈ S, δ ≤ dist (grid i) z := by
  sorry

theorem exists_real_point_away_from_finite_complex_set
    {a b : ℝ} (hab : a < b) {H : ℕ} (S : Finset ℂ) (hcard : S.card ≤ H) :
    ∃ t ∈ Icc a b, ∀ z ∈ S, (b - a) / (4 * (H + 1 : ℝ)) ≤ ‖(t : ℂ) - z‖ := by
  sorry

theorem separation_retained_after_motion {X : Type*} [MetricSpace X]
    {center moved z : X} {δ : ℝ} (hsep : 2 * δ ≤ dist center z)
    (hmotion : dist moved center ≤ δ) : δ ≤ dist moved z := by
  sorry

end KungTraub
