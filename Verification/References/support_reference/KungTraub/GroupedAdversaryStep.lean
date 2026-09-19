import support_reference.KungTraub.GroupedParameterBalls
import support_reference.KungTraub.FiniteFamilyGeometry

/-!
# One adversarial step for a complete group

The finite set is supplied before any answer in the next group. Its cardinality
can be the full union bound n*H_n. The retained separation and contraction follow
from the same abstract geometry as AdversaryStep, but the new direction intersects
every row of the group at once. Exponents are not fixed by this geometric lemma;
the grouped induction can therefore use the exact C_j.
-/

noncomputable section
namespace KungTraub
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem GroupedAffineAlgorithm.exists_next_ball_avoiding_finite_set {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm E sizes) {α : E → ℝ} {center : E}
    {x r a m M Q : ℝ} {j H : ℕ} (hj : j < k)
    (hr : 0 < r) (ha : 0 < a) (hm : 0 < m) (hM : 0 < M) (hQ : 0 < Q)
    (hcover : Set.Icc (α center - r * a / (2 * M)) (α center + r * a / (2 * M)) ⊆
      α '' parameterBall center (A.direction center x j) (r / 2))
    (hmotion : ∀ next ∈ parameterBall center (A.direction center x j) (r / 2),
      ∀ u ∈ parameterBall center (A.direction center x j) r,
        |α u - α next| ≤ (Q * a / m) * ‖u - next‖)
    (S : Finset ℂ) (hcard : S.card ≤ H) :
    ∃ next ∈ parameterBall center (A.direction center x j) (r / 2),
      parameterBall next (A.direction next x (j + 1)) (adversaryRadiusFactor m M Q H * r) ⊆
        parameterBall center (A.direction center x j) r ∧
      ∀ u ∈ parameterBall next (A.direction next x (j + 1)) (adversaryRadiusFactor m M Q H * r),
        A.prefix u x (j + 1) (Nat.succ_le_of_lt hj) =
            A.prefix next x (j + 1) (Nat.succ_le_of_lt hj) ∧
        ∀ z ∈ S, r * a / (8 * M * (H + 1 : ℝ)) ≤ ‖(α u : ℂ) - z‖ := by
  sorry

theorem FiniteRootFamily.grouped_initial_sensitivity_at {k : ℕ} {sizes : Fin k → ℕ}
    {ε x m M R wmin K : ℝ}
    (D : FiniteRootFamily (groupedObservationCount sizes) ε x m M R wmin K)
    (A : GroupedAffineAlgorithm (EuclideanSpace ℝ (Fin (groupedObservationCount sizes + 1))) sizes)
    (u : EuclideanSpace ℝ (Fin (groupedObservationCount sizes + 1))) (hu : ‖u‖ ≤ 1)
    (hε : 0 ≤ ε) :
    wmin * ε ≤ ‖(A.direction u x 0).starProjection (D.vector (D.root u))‖ := by
  sorry

/-- The analytic family discharges every geometric hypothesis of the grouped step. -/
theorem FiniteRootFamily.next_group_ball {k : ℕ} {sizes : Fin k → ℕ}
    {ε x m M R wmin K : ℝ}
    (D : FiniteRootFamily (groupedObservationCount sizes) ε x m M R wmin K)
    (A : GroupedAffineAlgorithm (EuclideanSpace ℝ (Fin (groupedObservationCount sizes + 1))) sizes)
    {center : EuclideanSpace ℝ (Fin (groupedObservationCount sizes + 1))} {r a : ℝ} {j H : ℕ}
    (hj : j < k) (hr : 0 < r) (hr1 : r ≤ 1) (ha : 0 < a)
    (hm : 0 < m) (hM : 0 < M) (hK : 0 ≤ K)
    (hball : ∀ u ∈ parameterBall center (A.direction center x j) r, ‖u‖ ≤ 1)
    (hasens : a = ‖(A.direction center x j).starProjection (D.vector (D.root center))‖)
    (S : Finset ℂ) (hcard : S.card ≤ H) :
    ∃ next ∈ parameterBall center (A.direction center x j) (r / 2),
      parameterBall next (A.direction next x (j + 1))
          (adversaryRadiusFactor m M (1 + K / (2 * m)) H * r) ⊆
        parameterBall center (A.direction center x j) r ∧
      ∀ u ∈ parameterBall next (A.direction next x (j + 1))
          (adversaryRadiusFactor m M (1 + K / (2 * m)) H * r),
        A.prefix u x (j + 1) (Nat.succ_le_of_lt hj) =
            A.prefix next x (j + 1) (Nat.succ_le_of_lt hj) ∧
        ∀ z ∈ S, r * a / (8 * M * (H + 1 : ℝ)) ≤ ‖(D.root u : ℂ) - z‖ := by
  sorry

end KungTraub
