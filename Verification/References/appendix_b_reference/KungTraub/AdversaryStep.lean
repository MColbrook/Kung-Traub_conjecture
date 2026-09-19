import appendix_b_reference.KungTraub.ParameterRootIntervals

/-!
# A nested-ball step with a uniform separation margin

The forbidden set is fixed before the next answer is chosen. A centre avoiding
it exists by the attained root interval. The exact radius factor from the paper
keeps every root in the next ball away from the same set, while the next answer
is constant throughout that ball.
-/

noncomputable section

namespace KungTraub

def adversaryRadiusFactor (m M Q : ℝ) (H : ℕ) : ℝ :=
  min (1 / 2) (m / (8 * Q * M * (H + 1 : ℝ)))

theorem adversaryRadiusFactor_pos {m M Q : ℝ} {H : ℕ}
    (hm : 0 < m) (hM : 0 < M) (hQ : 0 < Q) : 0 < adversaryRadiusFactor m M Q H := by
  sorry

theorem adversaryRadiusFactor_le_half (m M Q : ℝ) (H : ℕ) :
    adversaryRadiusFactor m M Q H ≤ 1 / 2 := by
  sorry

theorem adversaryRadiusFactor_motion_bound {m M Q a r : ℝ} {H : ℕ}
    (hm : 0 < m) (hM : 0 < M) (hQ : 0 < Q) (ha : 0 ≤ a) (hr : 0 ≤ r) :
    (Q * a / m) * (adversaryRadiusFactor m M Q H * r) ≤
      r * a / (8 * M * (H + 1 : ℝ)) := by
  sorry


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem AffineAlgorithm.exists_next_ball_avoiding_finite_set {n : ℕ}
    (A : AffineAlgorithm E n) {α : E → ℝ} {center : E}
    {x r a m M Q : ℝ} {j H : ℕ} (hj : j < n)
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
      ∀ u ∈ parameterBall next (A.direction next x (j + 1))
          (adversaryRadiusFactor m M Q H * r),
        A.prefix u x (j + 1) (Nat.succ_le_of_lt hj) =
            A.prefix next x (j + 1) (Nat.succ_le_of_lt hj) ∧
        ∀ z ∈ S, r * a / (8 * M * (H + 1 : ℝ)) ≤ ‖(α u : ℂ) - z‖ := by
  sorry

end KungTraub
