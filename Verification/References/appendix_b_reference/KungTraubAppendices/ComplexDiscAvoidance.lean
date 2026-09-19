import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Tactic

/-!
# Avoidance of finitely many closed complex discs

The sum of the forbidden areas is strictly smaller than the area of the target
disc. Mathlib's `Complex.volume_closedBall` and finite measure subadditivity
therefore give a point outside every forbidden closed disc. No restriction is
placed on the forbidden centres. The final radius is the one used in Appendix B.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace KungTraubAppendices

/-- A finite collection whose total measure is smaller than that of a target
set leaves a point of the target outside every member of the collection. -/
theorem exists_mem_avoiding_of_sum_measure_lt {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (A : Set α) (S : Finset ι) (B : ι → Set α)
    (hmeasure : (∑ i ∈ S, μ (B i)) < μ A) :
    ∃ t ∈ A, ∀ i ∈ S, t ∉ B i := by
  sorry

/-- The exact area criterion permits arbitrary nonnegative forbidden radii
and includes closed boundaries in both the target and forbidden discs. -/
theorem exists_mem_closedBall_avoiding_of_sum_sq_lt (c : ℂ) {R : ℝ} (hR : 0 < R)
    (S : Finset ℂ) (ρ : ℂ → ℝ) (hρ : ∀ z ∈ S, 0 ≤ ρ z)
    (harea : (∑ z ∈ S, (ρ z) ^ 2) < R ^ 2) :
    ∃ t ∈ Metric.closedBall c R, ∀ z ∈ S, ρ z < ‖t - z‖ := by
  sorry

/-- The forbidden area factor is strictly below one for every natural bound,
including zero. -/
theorem finiteDiscArea_lt {R : ℝ} (hR : 0 < R) (H : ℕ) :
    (H : ℝ) * (R / (2 * ((H : ℝ) + 1))) ^ 2 < R ^ 2 := by
  sorry

/-- At most `H` closed discs of radius `R/(2*(H+1))` cannot cover the closed
disc of radius `R`. Their centres may be anywhere in the complex plane. -/
theorem exists_mem_closedBall_avoiding_finset (c : ℂ) {R : ℝ} (hR : 0 < R)
    (S : Finset ℂ) (H : ℕ) (hcard : S.card ≤ H) :
    ∃ t ∈ Metric.closedBall c R,
      ∀ z ∈ S, R / (2 * ((H : ℝ) + 1)) < ‖t - z‖ := by
  sorry

end KungTraubAppendices
