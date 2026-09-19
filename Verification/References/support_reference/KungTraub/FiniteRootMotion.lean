import support_reference.KungTraub.RealRoots

/-!
# Root motion on an interval

Section 3 of Matthew J. Colbrook's manuscript uses derivative bounds only on a
fixed interval. These mean-value estimates preserve that domain, and continuity
of a parametrized root follows from a uniform positive derivative lower bound.
The interval mean-value inequalities and the squeeze theorem are from Mathlib.
-/

open Set Filter Topology

namespace KungTraub

theorem distance_mul_le_image_distance_on {J : Set ℝ} (hJ : Convex ℝ J)
    {f : ℝ → ℝ} {m : ℝ} (hf : ContinuousOn f J)
    (hf' : DifferentiableOn ℝ f (interior J)) (hm : 0 < m)
    (hderiv : ∀ x ∈ interior J, m ≤ deriv f x)
    {x y : ℝ} (hx : x ∈ J) (hy : y ∈ J) :
    m * |x - y| ≤ |f x - f y| := by
  sorry

theorem image_distance_le_distance_mul_on {J : Set ℝ} (hJ : Convex ℝ J)
    {f : ℝ → ℝ} {m M : ℝ} (hf : ContinuousOn f J)
    (hf' : DifferentiableOn ℝ f (interior J)) (hm : 0 < m)
    (hlower : ∀ x ∈ interior J, m ≤ deriv f x)
    (hupper : ∀ x ∈ interior J, deriv f x ≤ M)
    {x y : ℝ} (hx : x ∈ J) (hy : y ∈ J) :
    |f x - f y| ≤ M * |x - y| := by
  sorry

theorem distance_to_zero_le_value_div_on {J : Set ℝ} (hJ : Convex ℝ J)
    {f : ℝ → ℝ} {m α x : ℝ} (hf : ContinuousOn f J)
    (hf' : DifferentiableOn ℝ f (interior J)) (hm : 0 < m)
    (hderiv : ∀ t ∈ interior J, m ≤ deriv f t)
    (hα : f α = 0) (hαJ : α ∈ J) (hxJ : x ∈ J) :
    |x - α| ≤ |f x| / m := by
  sorry

theorem value_div_le_distance_to_zero_on {J : Set ℝ} (hJ : Convex ℝ J)
    {f : ℝ → ℝ} {m M α x : ℝ} (hf : ContinuousOn f J)
    (hf' : DifferentiableOn ℝ f (interior J)) (hm : 0 < m) (hM : 0 < M)
    (hlower : ∀ t ∈ interior J, m ≤ deriv f t)
    (hupper : ∀ t ∈ interior J, deriv f t ≤ M)
    (hα : f α = 0) (hαJ : α ∈ J) (hxJ : x ∈ J) :
    |f x| / M ≤ |x - α| := by
  sorry

/-- Pointwise continuity in the parameter at a fixed root suffices; no continuity
of the root map is assumed. The functions are only controlled on `J`. -/
theorem continuous_roots_of_uniform_derivative_lower_bound
    {P : Type*} [TopologicalSpace P] {J : Set ℝ} (hJ : Convex ℝ J)
    {F : P → ℝ → ℝ} {α : P → ℝ} {m : ℝ} (hm : 0 < m)
    (hF : ∀ u, ContinuousOn (F u) J)
    (hF' : ∀ u, DifferentiableOn ℝ (F u) (interior J))
    (hderiv : ∀ u t, t ∈ interior J → m ≤ deriv (F u) t)
    (hroot : ∀ u, F u (α u) = 0) (hmem : ∀ u, α u ∈ J)
    (hparam : ∀ t ∈ J, Continuous fun u => F u t) : Continuous α := by
  sorry

/-- The last step of the information lower bound: one of two indistinguishable
inputs has output error at least half the separation of their roots. -/
theorem max_output_error_ge_half_root_separation (output α β : ℝ) :
    |α - β| / 2 ≤ max |output - α| |output - β| := by
  sorry

end KungTraub
