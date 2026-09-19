import appendix_b_reference.KungTraub.FiniteRootMotion
import appendix_b_reference.KungTraub.FiniteAvoidance

/-!
# Intervals attained by varying a parameter

For the one-dimensional parameter segment in Section 3, evaluation at the centre
root is `t * a`. The derivative upper bound therefore forces the endpoint roots
to enclose the claimed interval of length `r * a / M`. Continuity of the root
on this segment follows from the parameter dependence.
-/

open Set

namespace KungTraub

theorem root_le_reference_sub_value_div {J : Set ℝ} (hJ : Convex ℝ J)
    {f : ℝ → ℝ} {m M α x : ℝ} (hf : ContinuousOn f J)
    (hf' : DifferentiableOn ℝ f (interior J)) (hm : 0 < m) (hM : 0 < M)
    (hlower : ∀ t ∈ interior J, m ≤ deriv f t)
    (hupper : ∀ t ∈ interior J, deriv f t ≤ M)
    (hroot : f α = 0) (hαJ : α ∈ J) (hxJ : x ∈ J) (hx : 0 ≤ f x) :
    α ≤ x - f x / M := by
  sorry

theorem reference_sub_value_div_le_root {J : Set ℝ} (hJ : Convex ℝ J)
    {f : ℝ → ℝ} {m M α x : ℝ} (hf : ContinuousOn f J)
    (hf' : DifferentiableOn ℝ f (interior J)) (hm : 0 < m) (hM : 0 < M)
    (hlower : ∀ t ∈ interior J, m ≤ deriv f t)
    (hupper : ∀ t ∈ interior J, deriv f t ≤ M)
    (hroot : f α = 0) (hαJ : α ∈ J) (hxJ : x ∈ J) (hx : f x ≤ 0) :
    x - f x / M ≤ α := by
  sorry

theorem continuousOn_roots_of_uniform_derivative_lower_bound
    {P : Type*} [TopologicalSpace P] {U : Set P} {J : Set ℝ} (hJ : Convex ℝ J)
    {F : P → ℝ → ℝ} {α : P → ℝ} {m : ℝ} (hm : 0 < m)
    (hF : ∀ u ∈ U, ContinuousOn (F u) J)
    (hF' : ∀ u ∈ U, DifferentiableOn ℝ (F u) (interior J))
    (hderiv : ∀ u ∈ U, ∀ t ∈ interior J, m ≤ deriv (F u) t)
    (hroot : ∀ u ∈ U, F u (α u) = 0) (hmem : ∀ u ∈ U, α u ∈ J)
    (hparam : ∀ t ∈ J, ContinuousOn (fun u => F u t) U) : ContinuousOn α U := by
  sorry

theorem root_segment_image_contains_interval {J : Set ℝ} (hJ : Convex ℝ J)
    {F : ℝ → ℝ → ℝ} {α : ℝ → ℝ} {center r a m M : ℝ}
    (hr : 0 < r) (ha : 0 < a) (hm : 0 < m) (hM : 0 < M) (hcenter : center ∈ J)
    (hF : ∀ t ∈ Icc (-r / 2) (r / 2), ContinuousOn (F t) J)
    (hF' : ∀ t ∈ Icc (-r / 2) (r / 2), DifferentiableOn ℝ (F t) (interior J))
    (hlower : ∀ t ∈ Icc (-r / 2) (r / 2), ∀ x ∈ interior J, m ≤ deriv (F t) x)
    (hupper : ∀ t ∈ Icc (-r / 2) (r / 2), ∀ x ∈ interior J, deriv (F t) x ≤ M)
    (hroot : ∀ t ∈ Icc (-r / 2) (r / 2), F t (α t) = 0)
    (hmem : ∀ t ∈ Icc (-r / 2) (r / 2), α t ∈ J)
    (hparam : ∀ x ∈ J, ContinuousOn (fun t => F t x) (Icc (-r / 2) (r / 2)))
    (hvalue : ∀ t ∈ Icc (-r / 2) (r / 2), F t center = t * a) :
    Icc (center - r * a / (2 * M)) (center + r * a / (2 * M)) ⊆
      α '' Icc (-r / 2) (r / 2) := by
  sorry

theorem exists_parameter_avoiding_finite_set_of_root_interval
    {U : Set ℝ} {α : ℝ → ℝ} {center r a M : ℝ} {H : ℕ}
    (hr : 0 < r) (ha : 0 < a) (hM : 0 < M)
    (hcover : Icc (center - r * a / (2 * M)) (center + r * a / (2 * M)) ⊆ α '' U)
    (S : Finset ℂ) (hcard : S.card ≤ H) :
    ∃ t ∈ U, ∀ z ∈ S, r * a / (4 * M * (H + 1 : ℝ)) ≤ ‖(α t : ℂ) - z‖ := by
  sorry

end KungTraub
