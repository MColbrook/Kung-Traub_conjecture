import KungTraub.ParameterBalls
import KungTraub.RootIntervals

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
  have hdiff : u - next = (u - center) - (next - center) := by abel
  have hdir : u - next ∈ V := by rw [hdiff]; exact V.sub_mem hu.1 hnext.1
  apply root_displacement_le_projected_sensitivity V hJ hdir hF hF' hm hlower
    hroot hnextmem hmem
  have hn := haffine next hnext (α next) hnextmem
  have hv := haffine u hu (α next) hnextmem
  rw [hnextroot] at hn
  rw [hdiff, inner_sub_left]
  linarith

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
  have hn := parameterBall_mono_radius (by linarith : r / 2 ≤ r) hnext
  have hmove := root_motion_inside_parameterBall V hJ hm (parameterBall_center center V hr)
    hn hF hF' hlower hroot hcenterroot hmem hcentermem haffine
  rw [← hasens] at hmove
  have ha0 : 0 ≤ a := hasens.symm ▸ norm_nonneg _
  have hscale := mul_le_mul_of_nonneg_left hnext.2 (div_nonneg ha0 hm.le)
  have hmove' : |α next - α center| ≤ a * r / (2 * m) := by
    calc
      |α next - α center| ≤ (a / m) * ‖next - center‖ := hmove
      _ ≤ (a / m) * (r / 2) := hscale
      _ = a * r / (2 * m) := by ring
  exact projected_sensitivity_comparison V hK hr1 hm hasens hmove' hv

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
  have hc := parameterBall_center center V hr.le
  obtain ⟨e, he, hnorm, heval⟩ := exists_unit_direction_attaining_projected_norm
    V (v (α center)) (hasens ▸ ha)
  have hs (t : ℝ) (ht : t ∈ Icc (-r / 2) (r / 2)) :
      center + t • e ∈ parameterBall center V (r / 2) := by
    apply parameterBall_unit_segment he hnorm
    exact abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  have hb (t : ℝ) (ht : t ∈ Icc (-r / 2) (r / 2)) :
      center + t • e ∈ parameterBall center V r :=
    parameterBall_mono_radius (by linarith : r / 2 ≤ r) (hs t ht)
  have hval (t : ℝ) (ht : t ∈ Icc (-r / 2) (r / 2)) (y : ℝ) (hy : y ∈ J) :
      F (center + t • e) y = F center y + t * ⟪e, v y⟫_ℝ := by
    simpa only [add_sub_cancel_left, real_inner_smul_left] using haffine _ (hb t ht) y hy
  have hparam (y : ℝ) (hy : y ∈ J) :
      ContinuousOn (fun t => F (center + t • e) y) (Icc (-r / 2) (r / 2)) := by
    apply (continuous_const.add (continuous_id.mul continuous_const)).continuousOn.congr
    intro t ht
    exact hval t ht y hy
  have hcover := root_segment_image_contains_interval hJ hr ha hm hM (hmem center hc)
    (fun t ht => hF _ (hb t ht)) (fun t ht => hF' _ (hb t ht))
    (fun t ht => hlower _ (hb t ht)) (fun t ht => hupper _ (hb t ht))
    (fun t ht => hroot _ (hb t ht)) (fun t ht => hmem _ (hb t ht)) hparam
    (fun t ht => by rw [hval t ht _ (hmem center hc), hroot center hc, heval, ← hasens,
      zero_add])
  intro y hy
  obtain ⟨t, ht, heq⟩ := hcover hy
  exact ⟨center + t • e, hs t ht, heq⟩

theorem exists_parameterBall_center_avoiding_finite_set
    {α : E → ℝ} {center : E} {V : Submodule ℝ E} {r a M : ℝ} {H : ℕ}
    (hr : 0 < r) (ha : 0 < a) (hM : 0 < M)
    (hcover : Icc (α center - r * a / (2 * M)) (α center + r * a / (2 * M)) ⊆
      α '' parameterBall center V (r / 2)) (S : Finset ℂ) (hcard : S.card ≤ H) :
    ∃ next ∈ parameterBall center V (r / 2),
      ∀ z ∈ S, r * a / (4 * M * (H + 1 : ℝ)) ≤ ‖(α next : ℂ) - z‖ := by
  have hrad : 0 < r * a / (2 * M) := by positivity
  obtain ⟨y, hy, haway⟩ := exists_real_point_away_from_finite_complex_set
    (show α center - r * a / (2 * M) < α center + r * a / (2 * M) by linarith) S hcard
  obtain ⟨next, hnext, heq⟩ := hcover hy
  refine ⟨next, hnext, ?_⟩
  intro z hz
  have hconstant : ((α center + r * a / (2 * M)) - (α center - r * a / (2 * M))) /
      (4 * (H + 1 : ℝ)) = r * a / (4 * M * (H + 1 : ℝ)) := by
    have hH : (H + 1 : ℝ) ≠ 0 := by positivity
    field_simp [hM.ne', hH]
    ring
  rw [heq]
  simpa only [hconstant] using haway z hz

theorem AffineAlgorithm.exists_large_error_of_root_interval {n : ℕ}
    (A : AffineAlgorithm E n) {α : E → ℝ} {center : E} {x r a M : ℝ}
    (hr : 0 < r) (ha : 0 < a) (hM : 0 < M)
    (hcover : Icc (α center - r * a / (2 * M)) (α center + r * a / (2 * M)) ⊆
      α '' parameterBall center (A.direction center x n) (r / 2)) :
    ∃ u ∈ parameterBall center (A.direction center x n) r,
      r * a / (2 * M) ≤ |A.run u x - α u| := by
  have hrad : 0 < r * a / (2 * M) := by positivity
  obtain ⟨u, hu, hαu⟩ := hcover (show α center - r * a / (2 * M) ∈
    Icc (α center - r * a / (2 * M)) (α center + r * a / (2 * M)) from ⟨le_rfl, by linarith⟩)
  obtain ⟨w, hw, hαw⟩ := hcover (show α center + r * a / (2 * M) ∈
    Icc (α center - r * a / (2 * M)) (α center + r * a / (2 * M)) from ⟨by linarith, le_rfl⟩)
  have hu' := parameterBall_mono_radius (by linarith : r / 2 ≤ r) hu
  have hw' := parameterBall_mono_radius (by linarith : r / 2 ≤ r) hw
  have hsep := max_output_error_ge_half_root_separation (A.run center x) (α u) (α w)
  have hdiff : |α u - α w| = 2 * (r * a / (2 * M)) := by
    rw [hαu, hαw, abs_of_nonpos (by linarith)]
    ring
  rw [hdiff] at hsep
  have hmax : r * a / (2 * M) ≤ max |A.run center x - α u| |A.run center x - α w| := by
    linarith
  rcases le_max_iff.mp hmax with huerr | hwerr
  · refine ⟨u, hu', ?_⟩
    simpa only [A.run_eq_on_parameterBall hu] using huerr
  · refine ⟨w, hw', ?_⟩
    simpa only [A.run_eq_on_parameterBall hw] using hwerr

end KungTraub
