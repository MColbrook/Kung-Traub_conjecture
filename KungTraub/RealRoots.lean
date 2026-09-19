import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
# Real zeros and perturbation bounds

Sections 3 and 4 of Matthew J. Colbrook's manuscript use a positive lower bound on
the real derivative to control zeros of perturbed functions. These lemmas prove the
existence, uniqueness and displacement facts needed there. The mean-value inequality
and intermediate-value theorem are supplied by the pinned Mathlib modules above.
-/

namespace KungTraub

theorem strictMono_of_uniform_derivative_lower_bound {f : ℝ → ℝ} {m : ℝ}
    (hm : 0 < m) (hderiv : ∀ x, m ≤ deriv f x) : StrictMono f :=
  strictMono_of_deriv_pos fun x => lt_of_lt_of_le hm (hderiv x)

theorem distance_mul_le_image_distance {f : ℝ → ℝ} {m : ℝ}
    (hf : Differentiable ℝ f) (hm : 0 < m) (hderiv : ∀ x, m ≤ deriv f x)
    (x y : ℝ) : m * |x - y| ≤ |f x - f y| := by
  have hmono := (strictMono_of_uniform_derivative_lower_bound hm hderiv).monotone
  rcases le_total x y with hxy | hyx
  · have h := mul_sub_le_image_sub_of_le_deriv hf hderiv hxy
    rw [abs_of_nonpos (sub_nonpos.mpr hxy),
      abs_of_nonpos (sub_nonpos.mpr (hmono hxy))]
    nlinarith
  · have h := mul_sub_le_image_sub_of_le_deriv hf hderiv hyx
    rw [abs_of_nonneg (sub_nonneg.mpr hyx),
      abs_of_nonneg (sub_nonneg.mpr (hmono hyx))]
    exact h

theorem existsUnique_zero_of_bounded_identity_perturbation {f : ℝ → ℝ} {m B : ℝ}
    (hf : Differentiable ℝ f) (hm : 0 < m) (hderiv : ∀ x, m ≤ deriv f x)
    (hbound : ∀ x, |f x - x| ≤ B) : ∃! α : ℝ, f α = 0 := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hbound 0)
  have hleft : f (-B - 1) ≤ 0 := by
    have h := (abs_le.mp (hbound (-B - 1))).2
    linarith
  have hright : 0 ≤ f (B + 1) := by
    have h := (abs_le.mp (hbound (B + 1))).1
    linarith
  obtain ⟨α, _, hα⟩ := intermediate_value_Icc (by linarith : -B - 1 ≤ B + 1)
    hf.continuous.continuousOn ⟨hleft, hright⟩
  refine ⟨α, hα, ?_⟩
  intro β hβ
  exact (strictMono_of_uniform_derivative_lower_bound hm hderiv).injective
    (hβ.trans hα.symm)

theorem abs_zero_le_perturbation_bound {f : ℝ → ℝ} {B α : ℝ}
    (hbound : ∀ x, |f x - x| ≤ B) (hα : f α = 0) : |α| ≤ B := by
  simpa [hα] using hbound α

theorem distance_to_zero_le_value_div {f : ℝ → ℝ} {m α : ℝ}
    (hf : Differentiable ℝ f) (hm : 0 < m) (hderiv : ∀ x, m ≤ deriv f x)
    (hα : f α = 0) (x : ℝ) : |x - α| ≤ |f x| / m := by
  apply (le_div_iff₀ hm).2
  have h := distance_mul_le_image_distance hf hm hderiv x α
  simpa [hα, mul_comm] using h

theorem zero_displacement_le_perturbation_div {f g : ℝ → ℝ} {m α β δ : ℝ}
    (hf : Differentiable ℝ f) (hm : 0 < m) (hderiv : ∀ x, m ≤ deriv f x)
    (hα : f α = 0) (hβ : g β = 0) (hperturb : |f β - g β| ≤ δ) :
    |β - α| ≤ δ / m := by
  have hvalue : |f β| ≤ δ := by simpa [hβ] using hperturb
  exact (distance_to_zero_le_value_div hf hm hderiv hα β).trans
    (div_le_div_of_nonneg_right hvalue hm.le)

end KungTraub
