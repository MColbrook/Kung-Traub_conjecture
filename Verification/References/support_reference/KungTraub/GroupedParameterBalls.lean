import support_reference.KungTraub.GroupedAffineTranscripts
import support_reference.KungTraub.ParameterRootIntervals

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
    A.prefix u x j hj = A.prefix center x j hj := by
  sorry

theorem GroupedAffineAlgorithm.run_eq_on_parameterBall {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm E sizes) {center u : E} {x r : ℝ}
    (hu : u ∈ parameterBall center (A.direction center x k) r) :
    A.run u x = A.run center x := by
  sorry

theorem GroupedAffineAlgorithm.parameterBall_next_subset {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm E sizes) {center next : E} {x r s : ℝ} {j : ℕ} (hj : j < k)
    (hnext : next ∈ parameterBall center (A.direction center x j) (r / 2))
    (hs : s ≤ r / 2) :
    parameterBall next (A.direction next x (j + 1)) s ⊆
      parameterBall center (A.direction center x j) r := by
  sorry

theorem GroupedAffineAlgorithm.queries_eq_on_parameterBall {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm E sizes) {center u : E} {x r : ℝ} (j : Fin k)
    (hu : u ∈ parameterBall center (A.direction center x j.val) r) :
    A.actualObservations u x j = A.actualObservations center x j := by
  sorry

/-- At the full grouped transcript, interval endpoints force the same half-length
error as in the scalar geometry. -/
theorem GroupedAffineAlgorithm.exists_large_error_of_root_interval {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm E sizes) {α : E → ℝ} {center : E} {x r a M : ℝ}
    (hr : 0 < r) (ha : 0 < a) (hM : 0 < M)
    (hcover : Set.Icc (α center - r * a / (2 * M)) (α center + r * a / (2 * M)) ⊆
      α '' parameterBall center (A.direction center x k) (r / 2)) :
    ∃ u ∈ parameterBall center (A.direction center x k) r,
      r * a / (2 * M) ≤ |A.run u x - α u| := by
  sorry

end KungTraub
