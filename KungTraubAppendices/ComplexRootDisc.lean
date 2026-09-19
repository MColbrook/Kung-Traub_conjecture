import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# A disc attained by the roots of a complex pencil

For the pencil `F(t) + ξ*q(t)`, the parameter `ξ = -F(t)/q(t)` realizes each
point of the closed disc of radius `r*a/(4*M)`. The norm and variation bounds
give denominator bound `a/2` and parameter bound `r/2`. The family hypotheses
specify domain containment and the existence and uniqueness of selected roots.
-/

noncomputable section

open Set

namespace KungTraubAppendices

/-- The complete closed target disc gives both scalar estimates needed for
the denominator and numerator bounds. -/
theorem complexRootDisc_target_bounds {α t : ℂ} {a M K r : ℝ}
    (ha : 0 ≤ a) (hM : 0 < M) (hK : 0 ≤ K) (hKr : K * r ≤ 2 * M)
    (ht : t ∈ Metric.closedBall α (r * a / (4 * M))) :
    K * ‖t - α‖ ≤ a / 2 ∧ M * ‖t - α‖ ≤ r * a / 4 := by
  have hdist : ‖t - α‖ ≤ r * a / (4 * M) := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using ht
  constructor
  · calc
      K * ‖t - α‖ ≤ K * (r * a / (4 * M)) := mul_le_mul_of_nonneg_left hdist hK
      _ = (K * r) * a / (4 * M) := by ring
      _ ≤ (2 * M) * a / (4 * M) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hKr ha) (by positivity)
      _ = a / 2 := by
        field_simp [ne_of_gt hM]
        ring
  · calc
      M * ‖t - α‖ ≤ M * (r * a / (4 * M)) := mul_le_mul_of_nonneg_left hdist hM.le
      _ = r * a / 4 := by field_simp [ne_of_gt hM]

/-- Every target in the full closed disc has a nonzero denominator and an
explicit parameter of norm at most `r/2` at which it is a root of the pencil. -/
theorem complexPencil_parameter_at_target {F q : ℂ → ℂ} {α t : ℂ} {a M K r : ℝ}
    (ha : 0 < a) (hM : 0 < M) (hK : 0 ≤ K) (hr : 0 < r) (hKr : K * r ≤ 2 * M)
    (hqa : ‖q α‖ = a) (ht : t ∈ Metric.closedBall α (r * a / (4 * M)))
    (hF : ‖F t‖ ≤ M * ‖t - α‖) (hq : ‖q t - q α‖ ≤ K * ‖t - α‖) :
    a / 2 ≤ ‖q t‖ ∧ ‖-F t / q t‖ ≤ r / 2 ∧ F t + (-F t / q t) * q t = 0 := by
  obtain ⟨hvariation, hnumerator⟩ := complexRootDisc_target_bounds ha.le hM hK hKr ht
  have hreverse := norm_sub_norm_le (q α) (q t)
  rw [hqa, norm_sub_rev] at hreverse
  have hdenominator : a / 2 ≤ ‖q t‖ := by linarith
  have hdenpos : 0 < ‖q t‖ := (half_pos ha).trans_le hdenominator
  have hdenne : q t ≠ 0 := norm_pos_iff.mp hdenpos
  refine ⟨hdenominator, ?_, ?_⟩
  · rw [norm_div, norm_neg]
    apply (div_le_iff₀ hdenpos).mpr
    calc
      ‖F t‖ ≤ r * a / 4 := hF.trans hnumerator
      _ ≤ (r / 2) * ‖q t‖ := by
        nlinarith [mul_le_mul_of_nonneg_left hdenominator (half_pos hr).le]
  · rw [div_mul_cancel₀ _ hdenne]
    ring

/-- Under the stated family hypotheses, the selected roots attain every point
of the closed target disc. Containment in the root domain is required explicitly. -/
theorem complexPencil_attained_closedBall {F q root : ℂ → ℂ} {α : ℂ} {a M K r : ℝ}
    {J : Set ℂ} (ha : 0 < a) (hM : 0 < M) (hK : 0 ≤ K) (hr : 0 < r)
    (hKr : K * r ≤ 2 * M) (hzero : F α = 0) (hqa : ‖q α‖ = a)
    (hcontain : Metric.closedBall α (r * a / (4 * M)) ⊆ J)
    (hF : ∀ t ∈ J, ‖F t - F α‖ ≤ M * ‖t - α‖)
    (hq : ∀ t ∈ J, ‖q t - q α‖ ≤ K * ‖t - α‖)
    (hselected : ∀ ξ : ℂ, ‖ξ‖ ≤ r / 2 → root ξ ∈ J ∧
      F (root ξ) + ξ * q (root ξ) = 0 ∧
      ∀ t ∈ J, F t + ξ * q t = 0 → t = root ξ) :
    Metric.closedBall α (r * a / (4 * M)) ⊆
      root '' Metric.closedBall (0 : ℂ) (r / 2) := by
  intro t ht
  have htJ := hcontain ht
  have hFt : ‖F t‖ ≤ M * ‖t - α‖ := by simpa only [hzero, sub_zero] using hF t htJ
  obtain ⟨_, hparameter, hroot⟩ :=
    complexPencil_parameter_at_target ha hM hK hr hKr hqa ht hFt (hq t htJ)
  refine ⟨-F t / q t, ?_, ?_⟩
  · simpa only [Metric.mem_closedBall, dist_zero_right] using hparameter
  · exact ((hselected _ hparameter).2.2 t htJ hroot).symm

end KungTraubAppendices
