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
  classical
  have hnot : ¬ A ⊆ ⋃ i ∈ S, B i := by
    intro hcover
    exact not_lt_of_ge ((measure_mono hcover).trans (measure_biUnion_finset_le S B)) hmeasure
  obtain ⟨t, ht, houtside⟩ := Set.not_subset.mp hnot
  refine ⟨t, ht, ?_⟩
  intro i hi hti
  exact houtside (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hti⟩⟩)

/-- The exact area criterion permits arbitrary nonnegative forbidden radii
and includes closed boundaries in both the target and forbidden discs. -/
theorem exists_mem_closedBall_avoiding_of_sum_sq_lt (c : ℂ) {R : ℝ} (hR : 0 < R)
    (S : Finset ℂ) (ρ : ℂ → ℝ) (hρ : ∀ z ∈ S, 0 ≤ ρ z)
    (harea : (∑ z ∈ S, (ρ z) ^ 2) < R ^ 2) :
    ∃ t ∈ Metric.closedBall c R, ∀ z ∈ S, ρ z < ‖t - z‖ := by
  have hvolume (z : ℂ) (r : ℝ) (hr : 0 ≤ r) :
      volume (Metric.closedBall z r) = ENNReal.ofReal (r ^ 2 * Real.pi) := by
    rw [Complex.volume_closedBall, ENNReal.ofReal_mul (sq_nonneg r),
      ENNReal.ofReal_pow hr, ← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
  have hmeasure : (∑ z ∈ S, volume (Metric.closedBall z (ρ z))) <
      volume (Metric.closedBall c R) := by
    calc
      _ = ∑ z ∈ S, ENNReal.ofReal ((ρ z) ^ 2 * Real.pi) := by
        apply Finset.sum_congr rfl
        intro z hz
        exact hvolume z (ρ z) (hρ z hz)
      _ = ENNReal.ofReal ((∑ z ∈ S, (ρ z) ^ 2) * Real.pi) := by
        rw [Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg]
        intro z _
        positivity
      _ < ENNReal.ofReal (R ^ 2 * Real.pi) :=
        (ENNReal.ofReal_lt_ofReal_iff (mul_pos (sq_pos_of_pos hR) Real.pi_pos)).mpr
          (mul_lt_mul_of_pos_right harea Real.pi_pos)
      _ = _ := (hvolume c R hR.le).symm
  obtain ⟨t, ht, havoid⟩ := exists_mem_avoiding_of_sum_measure_lt volume
    (Metric.closedBall c R) S (fun z => Metric.closedBall z (ρ z)) hmeasure
  refine ⟨t, ht, ?_⟩
  intro z hz
  simpa only [Metric.mem_closedBall, dist_eq_norm, not_le] using havoid z hz

/-- The forbidden area factor is strictly below one for every natural bound,
including zero. -/
theorem finiteDiscArea_lt {R : ℝ} (hR : 0 < R) (H : ℕ) :
    (H : ℝ) * (R / (2 * ((H : ℝ) + 1))) ^ 2 < R ^ 2 := by
  have hden : 0 < 2 * ((H : ℝ) + 1) := by positivity
  have hfactor : (H : ℝ) < (2 * ((H : ℝ) + 1)) ^ 2 := by
    nlinarith [sq_nonneg (H : ℝ), Nat.cast_nonneg (α := ℝ) H]
  rw [div_pow, ← mul_div_assoc]
  apply (div_lt_iff₀ (sq_pos_of_pos hden)).mpr
  simpa only [mul_comm] using mul_lt_mul_of_pos_left hfactor (sq_pos_of_pos hR)

/-- At most `H` closed discs of radius `R/(2*(H+1))` cannot cover the closed
disc of radius `R`. Their centres may be anywhere in the complex plane. -/
theorem exists_mem_closedBall_avoiding_finset (c : ℂ) {R : ℝ} (hR : 0 < R)
    (S : Finset ℂ) (H : ℕ) (hcard : S.card ≤ H) :
    ∃ t ∈ Metric.closedBall c R,
      ∀ z ∈ S, R / (2 * ((H : ℝ) + 1)) < ‖t - z‖ := by
  apply exists_mem_closedBall_avoiding_of_sum_sq_lt c hR S
    (fun _ => R / (2 * ((H : ℝ) + 1)))
  · intro z _
    positivity
  · calc
      _ = (S.card : ℝ) * (R / (2 * ((H : ℝ) + 1))) ^ 2 := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (H : ℝ) * (R / (2 * ((H : ℝ) + 1))) ^ 2 :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (sq_nonneg _)
      _ < R ^ 2 := finiteDiscArea_lt hR H

end KungTraubAppendices
