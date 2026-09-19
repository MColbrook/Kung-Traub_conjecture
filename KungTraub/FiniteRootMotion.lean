import KungTraub.RealRoots

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
  have hmono := (strictMonoOn_of_deriv_pos hJ hf
    (fun x hx => lt_of_lt_of_le hm (hderiv x hx))).monotoneOn
  rcases le_total x y with hxy | hyx
  · have h := hJ.mul_sub_le_image_sub_of_le_deriv hf hf' hderiv x hx y hy hxy
    rw [abs_of_nonpos (sub_nonpos.mpr hxy),
      abs_of_nonpos (sub_nonpos.mpr (hmono hx hy hxy))]
    linarith
  · have h := hJ.mul_sub_le_image_sub_of_le_deriv hf hf' hderiv y hy x hx hyx
    rw [abs_of_nonneg (sub_nonneg.mpr hyx),
      abs_of_nonneg (sub_nonneg.mpr (hmono hy hx hyx))]
    exact h

theorem image_distance_le_distance_mul_on {J : Set ℝ} (hJ : Convex ℝ J)
    {f : ℝ → ℝ} {m M : ℝ} (hf : ContinuousOn f J)
    (hf' : DifferentiableOn ℝ f (interior J)) (hm : 0 < m)
    (hlower : ∀ x ∈ interior J, m ≤ deriv f x)
    (hupper : ∀ x ∈ interior J, deriv f x ≤ M)
    {x y : ℝ} (hx : x ∈ J) (hy : y ∈ J) :
    |f x - f y| ≤ M * |x - y| := by
  have hmono := (strictMonoOn_of_deriv_pos hJ hf
    (fun x hx => lt_of_lt_of_le hm (hlower x hx))).monotoneOn
  rcases le_total x y with hxy | hyx
  · have h := hJ.image_sub_le_mul_sub_of_deriv_le hf hf' hupper x hx y hy hxy
    rw [abs_of_nonpos (sub_nonpos.mpr hxy),
      abs_of_nonpos (sub_nonpos.mpr (hmono hx hy hxy))]
    linarith
  · have h := hJ.image_sub_le_mul_sub_of_deriv_le hf hf' hupper y hy x hx hyx
    rw [abs_of_nonneg (sub_nonneg.mpr hyx),
      abs_of_nonneg (sub_nonneg.mpr (hmono hy hx hyx))]
    exact h

theorem distance_to_zero_le_value_div_on {J : Set ℝ} (hJ : Convex ℝ J)
    {f : ℝ → ℝ} {m α x : ℝ} (hf : ContinuousOn f J)
    (hf' : DifferentiableOn ℝ f (interior J)) (hm : 0 < m)
    (hderiv : ∀ t ∈ interior J, m ≤ deriv f t)
    (hα : f α = 0) (hαJ : α ∈ J) (hxJ : x ∈ J) :
    |x - α| ≤ |f x| / m := by
  apply (le_div_iff₀ hm).2
  simpa [hα, mul_comm] using
    distance_mul_le_image_distance_on hJ hf hf' hm hderiv hxJ hαJ

theorem value_div_le_distance_to_zero_on {J : Set ℝ} (hJ : Convex ℝ J)
    {f : ℝ → ℝ} {m M α x : ℝ} (hf : ContinuousOn f J)
    (hf' : DifferentiableOn ℝ f (interior J)) (hm : 0 < m) (hM : 0 < M)
    (hlower : ∀ t ∈ interior J, m ≤ deriv f t)
    (hupper : ∀ t ∈ interior J, deriv f t ≤ M)
    (hα : f α = 0) (hαJ : α ∈ J) (hxJ : x ∈ J) :
    |f x| / M ≤ |x - α| := by
  apply (div_le_iff₀ hM).2
  simpa [hα, mul_comm] using
    image_distance_le_distance_mul_on hJ hf hf' hm hlower hupper hxJ hαJ

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
  apply continuous_iff_continuousAt.mpr
  intro u
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hlimit : Tendsto (fun v => |F v (α u)| / m) (𝓝 u) (𝓝 0) := by
    have hpoint : Tendsto (fun v => F v (α u)) (𝓝 u) (𝓝 (F u (α u))) :=
      (hparam (α u) (hmem u)).continuousAt
    simpa [hroot u] using hpoint.abs.div_const m
  apply squeeze_zero (fun v => dist_nonneg) (fun v => ?_) hlimit
  rw [Real.dist_eq, abs_sub_comm]
  exact distance_to_zero_le_value_div_on hJ (hF v) (hF' v) hm
    (hderiv v) (hroot v) (hmem v) (hmem u)

/-- The last step of the information lower bound: one of two indistinguishable
inputs has output error at least half the separation of their roots. -/
theorem max_output_error_ge_half_root_separation (output α β : ℝ) :
    |α - β| / 2 ≤ max |output - α| |output - β| := by
  have htriangle : |α - β| ≤ |output - α| + |output - β| := by
    simpa [abs_sub_comm] using abs_sub_le α output β
  have hleft := le_max_left |output - α| |output - β|
  have hright := le_max_right |output - α| |output - β|
  linarith

end KungTraub
