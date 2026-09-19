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
    (hm : 0 < m) (hderiv : ∀ x, m ≤ deriv f x) : StrictMono f := by
  sorry

theorem distance_mul_le_image_distance {f : ℝ → ℝ} {m : ℝ}
    (hf : Differentiable ℝ f) (hm : 0 < m) (hderiv : ∀ x, m ≤ deriv f x)
    (x y : ℝ) : m * |x - y| ≤ |f x - f y| := by
  sorry

theorem existsUnique_zero_of_bounded_identity_perturbation {f : ℝ → ℝ} {m B : ℝ}
    (hf : Differentiable ℝ f) (hm : 0 < m) (hderiv : ∀ x, m ≤ deriv f x)
    (hbound : ∀ x, |f x - x| ≤ B) : ∃! α : ℝ, f α = 0 := by
  sorry

theorem abs_zero_le_perturbation_bound {f : ℝ → ℝ} {B α : ℝ}
    (hbound : ∀ x, |f x - x| ≤ B) (hα : f α = 0) : |α| ≤ B := by
  sorry

theorem distance_to_zero_le_value_div {f : ℝ → ℝ} {m α : ℝ}
    (hf : Differentiable ℝ f) (hm : 0 < m) (hderiv : ∀ x, m ≤ deriv f x)
    (hα : f α = 0) (x : ℝ) : |x - α| ≤ |f x| / m := by
  sorry

theorem zero_displacement_le_perturbation_div {f g : ℝ → ℝ} {m α β δ : ℝ}
    (hf : Differentiable ℝ f) (hm : 0 < m) (hderiv : ∀ x, m ≤ deriv f x)
    (hα : f α = 0) (hβ : g β = 0) (hperturb : |f β - g β| ≤ δ) :
    |β - α| ≤ δ / m := by
  sorry

end KungTraub
