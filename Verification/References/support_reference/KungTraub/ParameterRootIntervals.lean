import support_reference.KungTraub.ParameterBalls
import support_reference.KungTraub.RootIntervals

/-!
# Root intervals inside a parameter ball

The direction attaining projected sensitivity produces a segment of roots of
the required length. Its continuity follows from the derivative lower bound
and the affine dependence on parameters.
-/

open Set
open scoped InnerProductSpace

namespace KungTraub

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem root_motion_inside_parameterBall
    (V : Submodule ℝ E) [V.HasOrthogonalProjection]
    {F : E → ℝ → ℝ} {α : E → ℝ} {v : ℝ → E} {center next u : E}
    {J : Set ℝ} {r m : ℝ} (hJ : Convex ℝ J) (hm : 0 < m)
    (hnext : next ∈ parameterBall center V r) (hu : u ∈ parameterBall center V r)
    (hF : ContinuousOn (F u) J) (hF' : DifferentiableOn ℝ (F u) (interior J))
    (hlower : ∀ y ∈ interior J, m ≤ deriv (F u) y)
    (hroot : F u (α u) = 0) (hnextroot : F next (α next) = 0)
    (hmem : α u ∈ J) (hnextmem : α next ∈ J)
    (haffine : ∀ w ∈ parameterBall center V r, ∀ y ∈ J,
      F w y = F center y + ⟪w - center, v y⟫_ℝ) :
    |α u - α next| ≤ (‖V.starProjection (v (α next))‖ / m) * ‖u - next‖ := by
  sorry

theorem sensitivity_inside_half_parameterBall
    (V : Submodule ℝ E) [V.HasOrthogonalProjection]
    {F : E → ℝ → ℝ} {α : E → ℝ} {v : ℝ → E} {center next : E}
    {J : Set ℝ} {r a m K : ℝ} (hJ : Convex ℝ J)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hm : 0 < m) (hK : 0 ≤ K)
    (hasens : a = ‖V.starProjection (v (α center))‖)
    (hnext : next ∈ parameterBall center V (r / 2))
    (hF : ContinuousOn (F next) J) (hF' : DifferentiableOn ℝ (F next) (interior J))
    (hlower : ∀ y ∈ interior J, m ≤ deriv (F next) y)
    (hroot : F next (α next) = 0) (hcenterroot : F center (α center) = 0)
    (hmem : α next ∈ J) (hcentermem : α center ∈ J)
    (haffine : ∀ w ∈ parameterBall center V r, ∀ y ∈ J,
      F w y = F center y + ⟪w - center, v y⟫_ℝ)
    (hv : ‖v (α next) - v (α center)‖ ≤ K * |α next - α center|) :
    ‖V.starProjection (v (α next))‖ ≤ (1 + K / (2 * m)) * a := by
  sorry

theorem root_parameterBall_image_contains_interval
    (V : Submodule ℝ E) [V.HasOrthogonalProjection]
    {F : E → ℝ → ℝ} {α : E → ℝ} {v : ℝ → E} {center : E}
    {J : Set ℝ} {r a m M : ℝ} (hJ : Convex ℝ J)
    (hr : 0 < r) (ha : 0 < a) (hm : 0 < m) (hM : 0 < M)
    (hasens : a = ‖V.starProjection (v (α center))‖)
    (hF : ∀ u ∈ parameterBall center V r, ContinuousOn (F u) J)
    (hF' : ∀ u ∈ parameterBall center V r, DifferentiableOn ℝ (F u) (interior J))
    (hlower : ∀ u ∈ parameterBall center V r, ∀ y ∈ interior J, m ≤ deriv (F u) y)
    (hupper : ∀ u ∈ parameterBall center V r, ∀ y ∈ interior J, deriv (F u) y ≤ M)
    (hroot : ∀ u ∈ parameterBall center V r, F u (α u) = 0)
    (hmem : ∀ u ∈ parameterBall center V r, α u ∈ J)
    (haffine : ∀ u ∈ parameterBall center V r, ∀ y ∈ J,
      F u y = F center y + ⟪u - center, v y⟫_ℝ) :
    Icc (α center - r * a / (2 * M)) (α center + r * a / (2 * M)) ⊆
      α '' parameterBall center V (r / 2) := by
  sorry

theorem exists_parameterBall_center_avoiding_finite_set
    {α : E → ℝ} {center : E} {V : Submodule ℝ E} {r a M : ℝ} {H : ℕ}
    (hr : 0 < r) (ha : 0 < a) (hM : 0 < M)
    (hcover : Icc (α center - r * a / (2 * M)) (α center + r * a / (2 * M)) ⊆
      α '' parameterBall center V (r / 2)) (S : Finset ℂ) (hcard : S.card ≤ H) :
    ∃ next ∈ parameterBall center V (r / 2),
      ∀ z ∈ S, r * a / (4 * M * (H + 1 : ℝ)) ≤ ‖(α next : ℂ) - z‖ := by
  sorry

theorem AffineAlgorithm.exists_large_error_of_root_interval {n : ℕ}
    (A : AffineAlgorithm E n) {α : E → ℝ} {center : E} {x r a M : ℝ}
    (hr : 0 < r) (ha : 0 < a) (hM : 0 < M)
    (hcover : Icc (α center - r * a / (2 * M)) (α center + r * a / (2 * M)) ⊆
      α '' parameterBall center (A.direction center x n) (r / 2)) :
    ∃ u ∈ parameterBall center (A.direction center x n) r,
      r * a / (2 * M) ≤ |A.run u x - α u| := by
  sorry

end KungTraub
