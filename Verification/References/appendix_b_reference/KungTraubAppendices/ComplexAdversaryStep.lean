import appendix_b_reference.KungTraubAppendices.ComplexFamilyRootMotion
import appendix_b_reference.KungTraubAppendices.ComplexParameterBalls
import appendix_b_reference.KungTraubAppendices.ComplexDiscAvoidance
import appendix_b_reference.KungTraubAppendices.ComplexStageRadii

/-!
# A complex geometric selection step

The attained root disc and the area estimate select a center away from a finite
forbidden set. The complex radius factor preserves half that separation on
the successor transcript ball.

The argument follows `KungTraub.AdversaryStep`, using the root-disc and motion
bounds for the complex family, with denominators eight and sixteen.
-/

noncomputable section

namespace KungTraubAppendices

variable {d n : ℕ}
local notation "E" => EuclideanSpace ℂ (Fin d)

/-- The complex family and the actual adaptive fibre yield a next
ball with a constant successor prefix and the uniform separation. -/
theorem ComplexAffineAlgorithm.exists_next_ball_avoiding_finite_set
    (A : ComplexAffineAlgorithm E n)
    {P : Set E} {J : Set ℂ} {F : E → ℂ → ℂ} {root : E → ℂ}
    {vector : ℂ → E} {center : E} {x : ℂ} {m M K r a : ℝ} {j H : ℕ}
    (hj : j < n) (hm : 0 < m) (hM : 0 < M) (hK : 0 ≤ K)
    (hr : 0 < r) (hrone : r ≤ 1) (hKr : K * r ≤ 2 * M)
    (hroot : ∀ u ∈ P, root u ∈ J ∧ F u (root u) = 0)
    (hlower : ∀ u ∈ P, ∀ z ∈ J, ∀ t ∈ J,
      m * ‖z - t‖ ≤ ‖F u z - F u t‖)
    (haffine : ∀ u ∈ P, ∀ v ∈ P, ∀ t ∈ J,
      F u t = F v t + complexBilinearDot (u - v) (vector t))
    (hvector : ∀ z ∈ J, ∀ t ∈ J, ‖vector z - vector t‖ ≤ K * ‖z - t‖)
    (hball : complexParameterBall center (A.direction center x j) r ⊆ P)
    (hupper : ∀ t ∈ J, ‖F center t - F center (root center)‖ ≤ M * ‖t - root center‖)
    (ha : 0 < a)
    (haeq : a = ‖(A.direction center x j).starProjection
      (complexConjVector (vector (root center)))‖)
    (hcontain : Metric.closedBall (root center) (r * a / (4 * M)) ⊆ J)
    (S : Finset ℂ) (hcard : S.card ≤ H) :
    let Q := 1 + K / (2 * m)
    ∃ next ∈ complexParameterBall center (A.direction center x j) (r / 2),
      complexParameterBall next (A.direction next x (j + 1))
          (complexRadiusFactor m M Q H * r) ⊆
        complexParameterBall center (A.direction center x j) r ∧
      ∀ u ∈ complexParameterBall next (A.direction next x (j + 1))
          (complexRadiusFactor m M Q H * r),
        A.prefix u x (j + 1) (Nat.succ_le_of_lt hj) =
            A.prefix next x (j + 1) (Nat.succ_le_of_lt hj) ∧
        ∀ z ∈ S, r * a / (16 * M * ((H : ℝ) + 1)) ≤ ‖root u - z‖ := by
  sorry

/-- Opposite points of an attained root disc force an error at least its
radius for one parameter with the same complete transcript. -/
theorem ComplexAffineAlgorithm.exists_error_ge_of_root_disc
    (A : ComplexAffineAlgorithm E n) {root : E → ℂ} {center : E}
    {x α : ℂ} {r R : ℝ} (hR : 0 < R)
    (hcover : Metric.closedBall α R ⊆
      root '' complexParameterBall center (A.direction center x n) r) :
    ∃ u ∈ complexParameterBall center (A.direction center x n) r,
      R ≤ ‖A.run u x - root u‖ := by
  sorry

end KungTraubAppendices
