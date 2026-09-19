import KungTraub.FiniteRootMotion
import KungTraub.FiniteAvoidance

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
  have hmono := strictMonoOn_of_deriv_pos hJ hf
    (fun t ht => lt_of_lt_of_le hm (hlower t ht))
  have horder : α ≤ x := by
    by_contra h
    have hlt := hmono hxJ hαJ (lt_of_not_ge h)
    linarith
  have hbound := hJ.image_sub_le_mul_sub_of_deriv_le hf hf' hupper α hαJ x hxJ horder
  have hdiv : f x / M ≤ x - α := (div_le_iff₀ hM).mpr (by nlinarith)
  linarith

theorem reference_sub_value_div_le_root {J : Set ℝ} (hJ : Convex ℝ J)
    {f : ℝ → ℝ} {m M α x : ℝ} (hf : ContinuousOn f J)
    (hf' : DifferentiableOn ℝ f (interior J)) (hm : 0 < m) (hM : 0 < M)
    (hlower : ∀ t ∈ interior J, m ≤ deriv f t)
    (hupper : ∀ t ∈ interior J, deriv f t ≤ M)
    (hroot : f α = 0) (hαJ : α ∈ J) (hxJ : x ∈ J) (hx : f x ≤ 0) :
    x - f x / M ≤ α := by
  have hmono := strictMonoOn_of_deriv_pos hJ hf
    (fun t ht => lt_of_lt_of_le hm (hlower t ht))
  have horder : x ≤ α := by
    by_contra h
    have hlt := hmono hαJ hxJ (lt_of_not_ge h)
    linarith
  have hbound := hJ.image_sub_le_mul_sub_of_deriv_le hf hf' hupper x hxJ α hαJ horder
  have hdiv : -f x / M ≤ α - x := (div_le_iff₀ hM).mpr (by nlinarith)
  rw [neg_div] at hdiv
  linarith

theorem continuousOn_roots_of_uniform_derivative_lower_bound
    {P : Type*} [TopologicalSpace P] {U : Set P} {J : Set ℝ} (hJ : Convex ℝ J)
    {F : P → ℝ → ℝ} {α : P → ℝ} {m : ℝ} (hm : 0 < m)
    (hF : ∀ u ∈ U, ContinuousOn (F u) J)
    (hF' : ∀ u ∈ U, DifferentiableOn ℝ (F u) (interior J))
    (hderiv : ∀ u ∈ U, ∀ t ∈ interior J, m ≤ deriv (F u) t)
    (hroot : ∀ u ∈ U, F u (α u) = 0) (hmem : ∀ u ∈ U, α u ∈ J)
    (hparam : ∀ t ∈ J, ContinuousOn (fun u => F u t) U) : ContinuousOn α U := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  exact continuous_roots_of_uniform_derivative_lower_bound hJ hm
    (fun u : U => hF u u.property) (fun u : U => hF' u u.property)
    (fun u : U => hderiv u u.property) (fun u : U => hroot u u.property)
    (fun u : U => hmem u u.property) (fun t ht => (hparam t ht).domRestrict)

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
  have hab : -r / 2 ≤ r / 2 := by linarith
  have hleft : -r / 2 ∈ Icc (-r / 2) (r / 2) := left_mem_Icc.mpr hab
  have hright : r / 2 ∈ Icc (-r / 2) (r / 2) := right_mem_Icc.mpr hab
  have hcontinuity := continuousOn_roots_of_uniform_derivative_lower_bound hJ hm
    hF hF' hlower hroot hmem hparam
  have hlow := root_le_reference_sub_value_div hJ (hF _ hright) (hF' _ hright)
    hm hM (hlower _ hright) (hupper _ hright) (hroot _ hright) (hmem _ hright)
    hcenter (by rw [hvalue _ hright]; positivity)
  have hhigh := reference_sub_value_div_le_root hJ (hF _ hleft) (hF' _ hleft)
    hm hM (hlower _ hleft) (hupper _ hleft) (hroot _ hleft) (hmem _ hleft)
    hcenter (by rw [hvalue _ hleft]; nlinarith)
  rw [hvalue _ hright] at hlow
  rw [hvalue _ hleft] at hhigh
  have hpositive : (r / 2 * a) / M = r * a / (2 * M) := by ring
  have hnegative : (-r / 2 * a) / M = -(r * a / (2 * M)) := by ring
  rw [hpositive] at hlow
  rw [hnegative, sub_neg_eq_add] at hhigh
  intro y hy
  exact intermediate_value_Icc' hab hcontinuity ⟨hlow.trans hy.1, hy.2.trans hhigh⟩

theorem exists_parameter_avoiding_finite_set_of_root_interval
    {U : Set ℝ} {α : ℝ → ℝ} {center r a M : ℝ} {H : ℕ}
    (hr : 0 < r) (ha : 0 < a) (hM : 0 < M)
    (hcover : Icc (center - r * a / (2 * M)) (center + r * a / (2 * M)) ⊆ α '' U)
    (S : Finset ℂ) (hcard : S.card ≤ H) :
    ∃ t ∈ U, ∀ z ∈ S, r * a / (4 * M * (H + 1 : ℝ)) ≤ ‖(α t : ℂ) - z‖ := by
  have hrad : 0 < r * a / (2 * M) := by positivity
  obtain ⟨y, hy, haway⟩ := exists_real_point_away_from_finite_complex_set
    (show center - r * a / (2 * M) < center + r * a / (2 * M) by linarith) S hcard
  obtain ⟨t, ht, heq⟩ := hcover hy
  refine ⟨t, ht, ?_⟩
  intro z hz
  have hconstant : ((center + r * a / (2 * M)) - (center - r * a / (2 * M))) /
      (4 * (H + 1 : ℝ)) = r * a / (4 * M * (H + 1 : ℝ)) := by
    have hH : (H + 1 : ℝ) ≠ 0 := by positivity
    field_simp [hM.ne', hH]
    ring
  rw [heq]
  simpa only [hconstant] using haway z hz

end KungTraub
