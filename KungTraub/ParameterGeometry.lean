import KungTraub.FiniteRootMotion
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Projection estimates for the parameter ball

Section 3 measures root sensitivity by the norm of evaluation projected onto the
remaining parameter directions. These lemmas establish the projection identities,
the maximizing unit direction, root displacement and sensitivity comparison.
The orthogonal-projection and Cauchy–Schwarz facts are supplied by Mathlib.
All spatial root estimates retain the fixed interval domain.
-/

open Set
open scoped InnerProductSpace

namespace KungTraub

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem inner_eq_inner_projected (V : Submodule ℝ E) [V.HasOrthogonalProjection]
    {h : E} (hh : h ∈ V) (v : E) : ⟪h, v⟫_ℝ = ⟪h, V.starProjection v⟫_ℝ := by
  simpa only [Submodule.starProjection_eq_self_iff.mpr hh] using
    V.inner_starProjection_left_eq_right h v

theorem abs_inner_le_projected_norm_mul (V : Submodule ℝ E) [V.HasOrthogonalProjection]
    {h : E} (hh : h ∈ V) (v : E) : |⟪h, v⟫_ℝ| ≤ ‖V.starProjection v‖ * ‖h‖ := by
  rw [inner_eq_inner_projected V hh v]
  simpa only [mul_comm] using abs_real_inner_le_norm h (V.starProjection v)

theorem exists_unit_direction_attaining_projected_norm
    (V : Submodule ℝ E) [V.HasOrthogonalProjection] (v : E)
    (ha : 0 < ‖V.starProjection v‖) :
    ∃ e ∈ V, ‖e‖ = 1 ∧ ⟪e, v⟫_ℝ = ‖V.starProjection v‖ := by
  let e : E := ‖V.starProjection v‖⁻¹ • V.starProjection v
  have he : e ∈ V := V.smul_mem _ (V.starProjection_apply_mem v)
  refine ⟨e, he, ?_, ?_⟩
  · simp only [e, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)]
    exact inv_mul_cancel₀ ha.ne'
  · have hin : ⟪V.starProjection v, v⟫_ℝ = ‖V.starProjection v‖ ^ 2 := by
      rw [inner_eq_inner_projected V (V.starProjection_apply_mem v) v]
      exact real_inner_self_eq_norm_sq _
    simp only [e, real_inner_smul_left, hin]
    field_simp

theorem projected_norm_mono_subspace {U V : Submodule ℝ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (hUV : U ≤ V) (v : E) :
    ‖U.starProjection v‖ ≤ ‖V.starProjection v‖ := by
  have heq : U.starProjection (V.starProjection v) = U.starProjection v := by
    exact congrArg (fun f : E →L[ℝ] E => f v)
      (Submodule.starProjection_comp_starProjection_of_le hUV)
  simpa only [heq] using U.norm_starProjection_apply_le (V.starProjection v)

theorem root_displacement_le_projected_sensitivity
    (V : Submodule ℝ E) [V.HasOrthogonalProjection] {J : Set ℝ} (hJ : Convex ℝ J)
    {g : ℝ → ℝ} {m α β : ℝ} {h v : E} (hh : h ∈ V)
    (hg : ContinuousOn g J) (hg' : DifferentiableOn ℝ g (interior J)) (hm : 0 < m)
    (hderiv : ∀ t ∈ interior J, m ≤ deriv g t)
    (hroot : g β = 0) (hα : α ∈ J) (hβ : β ∈ J) (hvalue : g α = ⟪h, v⟫_ℝ) :
    |β - α| ≤ (‖V.starProjection v‖ / m) * ‖h‖ := by
  have hdist := distance_to_zero_le_value_div_on hJ hg hg' hm hderiv hroot hβ hα
  rw [hvalue, abs_sub_comm α β] at hdist
  have hbound := div_le_div_of_nonneg_right (abs_inner_le_projected_norm_mul V hh v) hm.le
  calc
    |β - α| ≤ |⟪h, v⟫_ℝ| / m := hdist
    _ ≤ (‖V.starProjection v‖ * ‖h‖) / m := hbound
    _ = (‖V.starProjection v‖ / m) * ‖h‖ := by ring

theorem projected_sensitivity_comparison (V : Submodule ℝ E) [V.HasOrthogonalProjection]
    {v : ℝ → E} {α β a K r m : ℝ} (hK : 0 ≤ K) (hr1 : r ≤ 1)
    (hm : 0 < m) (ha : a = ‖V.starProjection (v α)‖)
    (hroot : |β - α| ≤ a * r / (2 * m))
    (hv : ‖v β - v α‖ ≤ K * |β - α|) :
    ‖V.starProjection (v β)‖ ≤ (1 + K / (2 * m)) * a := by
  have ha0 : 0 ≤ a := ha.symm ▸ norm_nonneg _
  have hproj : ‖V.starProjection (v β) - V.starProjection (v α)‖ ≤ ‖v β - v α‖ := by
    simpa only [map_sub] using V.norm_starProjection_apply_le (v β - v α)
  have htriangle := norm_add_le (V.starProjection (v β) - V.starProjection (v α))
    (V.starProjection (v α))
  rw [sub_add_cancel, ← ha] at htriangle
  have hscale : a * r / (2 * m) ≤ a / (2 * m) :=
    div_le_div_of_nonneg_right (mul_le_of_le_one_right ha0 hr1) (by positivity)
  have hmotion := mul_le_mul_of_nonneg_left (hroot.trans hscale) hK
  calc
    ‖V.starProjection (v β)‖ ≤ ‖v β - v α‖ + a := by linarith
    _ ≤ K * (a / (2 * m)) + a := by linarith
    _ = (1 + K / (2 * m)) * a := by ring

end KungTraub
