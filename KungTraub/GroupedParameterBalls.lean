import KungTraub.GroupedAffineTranscripts
import KungTraub.ParameterRootIntervals

/-!
# Parameter balls for complete grouped transcripts

These are the grouped analogues of the lemmas in ParameterBalls
and ParameterRootIntervals. The abstract ball and root-interval geometry is reused.
One transition intersects all rows in the next group and contracts the radius once.
-/

noncomputable section
namespace KungTraub
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem GroupedAffineAlgorithm.prefix_eq_on_parameterBall {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm E sizes) {center u : E} {x r : ℝ} {j : ℕ} (hj : j ≤ k)
    (hu : u ∈ parameterBall center (A.direction center x j) r) :
    A.prefix u x j hj = A.prefix center x j hj :=
  (A.prefix_eq_iff_sub_mem_direction center u x j hj).mpr hu.1

theorem GroupedAffineAlgorithm.run_eq_on_parameterBall {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm E sizes) {center u : E} {x r : ℝ}
    (hu : u ∈ parameterBall center (A.direction center x k) r) :
    A.run u x = A.run center x :=
  congrArg (A.output x) (A.prefix_eq_on_parameterBall le_rfl hu)

theorem GroupedAffineAlgorithm.parameterBall_next_subset {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm E sizes) {center next : E} {x r s : ℝ} {j : ℕ} (hj : j < k)
    (hnext : next ∈ parameterBall center (A.direction center x j) (r / 2))
    (hs : s ≤ r / 2) :
    parameterBall next (A.direction next x (j + 1)) s ⊆
      parameterBall center (A.direction center x j) r := by
  have hp := A.prefix_eq_on_parameterBall hj.le hnext
  apply parameterBall_nested_half hnext _ hs
  rw [A.direction_succ_of_prefix_eq hj hp]
  exact inf_le_left

theorem GroupedAffineAlgorithm.queries_eq_on_parameterBall {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm E sizes) {center u : E} {x r : ℝ} (j : Fin k)
    (hu : u ∈ parameterBall center (A.direction center x j.val) r) :
    A.actualObservations u x j = A.actualObservations center x j :=
  A.actualObservations_eq_of_prefix_eq j (A.prefix_eq_on_parameterBall j.isLt.le hu)

/-- At the full grouped transcript, interval endpoints force the same half-length
error as in the scalar geometry. -/
theorem GroupedAffineAlgorithm.exists_large_error_of_root_interval {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm E sizes) {α : E → ℝ} {center : E} {x r a M : ℝ}
    (hr : 0 < r) (ha : 0 < a) (hM : 0 < M)
    (hcover : Set.Icc (α center - r * a / (2 * M)) (α center + r * a / (2 * M)) ⊆
      α '' parameterBall center (A.direction center x k) (r / 2)) :
    ∃ u ∈ parameterBall center (A.direction center x k) r,
      r * a / (2 * M) ≤ |A.run u x - α u| := by
  have hrad : 0 < r * a / (2 * M) := by positivity
  obtain ⟨u, hu, hαu⟩ := hcover (show α center - r * a / (2 * M) ∈
    Set.Icc (α center - r * a / (2 * M)) (α center + r * a / (2 * M)) from ⟨le_rfl, by linarith⟩)
  obtain ⟨w, hw, hαw⟩ := hcover (show α center + r * a / (2 * M) ∈
    Set.Icc (α center - r * a / (2 * M)) (α center + r * a / (2 * M)) from ⟨by linarith, le_rfl⟩)
  have hu' := parameterBall_mono_radius (by linarith : r / 2 ≤ r) hu
  have hw' := parameterBall_mono_radius (by linarith : r / 2 ≤ r) hw
  have hsep := max_output_error_ge_half_root_separation (A.run center x) (α u) (α w)
  have hdiff : |α u - α w| = 2 * (r * a / (2 * M)) := by
    rw [hαu, hαw, abs_of_nonpos (by linarith)]
    ring
  rw [hdiff] at hsep
  have hmax : r * a / (2 * M) ≤ max |A.run center x - α u| |A.run center x - α w| := by linarith
  rcases le_max_iff.mp hmax with huerr | hwerr
  · refine ⟨u, hu', ?_⟩
    simpa only [A.run_eq_on_parameterBall hu] using huerr
  · refine ⟨w, hw', ?_⟩
    simpa only [A.run_eq_on_parameterBall hw] using hwerr

end KungTraub
