import appendix_b_reference.KungTraub.FiniteRootMotion
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
  sorry

theorem abs_inner_le_projected_norm_mul (V : Submodule ℝ E) [V.HasOrthogonalProjection]
    {h : E} (hh : h ∈ V) (v : E) : |⟪h, v⟫_ℝ| ≤ ‖V.starProjection v‖ * ‖h‖ := by
  sorry

theorem exists_unit_direction_attaining_projected_norm
    (V : Submodule ℝ E) [V.HasOrthogonalProjection] (v : E)
    (ha : 0 < ‖V.starProjection v‖) :
    ∃ e ∈ V, ‖e‖ = 1 ∧ ⟪e, v⟫_ℝ = ‖V.starProjection v‖ := by
  sorry

theorem projected_norm_mono_subspace {U V : Submodule ℝ E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (hUV : U ≤ V) (v : E) :
    ‖U.starProjection v‖ ≤ ‖V.starProjection v‖ := by
  sorry

theorem root_displacement_le_projected_sensitivity
    (V : Submodule ℝ E) [V.HasOrthogonalProjection] {J : Set ℝ} (hJ : Convex ℝ J)
    {g : ℝ → ℝ} {m α β : ℝ} {h v : E} (hh : h ∈ V)
    (hg : ContinuousOn g J) (hg' : DifferentiableOn ℝ g (interior J)) (hm : 0 < m)
    (hderiv : ∀ t ∈ interior J, m ≤ deriv g t)
    (hroot : g β = 0) (hα : α ∈ J) (hβ : β ∈ J) (hvalue : g α = ⟪h, v⟫_ℝ) :
    |β - α| ≤ (‖V.starProjection v‖ / m) * ‖h‖ := by
  sorry

theorem projected_sensitivity_comparison (V : Submodule ℝ E) [V.HasOrthogonalProjection]
    {v : ℝ → E} {α β a K r m : ℝ} (hK : 0 ≤ K) (hr1 : r ≤ 1)
    (hm : 0 < m) (ha : a = ‖V.starProjection (v α)‖)
    (hroot : |β - α| ≤ a * r / (2 * m))
    (hv : ‖v β - v α‖ ≤ K * |β - α|) :
    ‖V.starProjection (v β)‖ ≤ (1 + K / (2 * m)) * a := by
  sorry

end KungTraub
