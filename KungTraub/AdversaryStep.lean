import KungTraub.ParameterRootIntervals

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
  unfold adversaryRadiusFactor
  positivity

theorem adversaryRadiusFactor_le_half (m M Q : ℝ) (H : ℕ) :
    adversaryRadiusFactor m M Q H ≤ 1 / 2 := min_le_left _ _

theorem adversaryRadiusFactor_motion_bound {m M Q a r : ℝ} {H : ℕ}
    (hm : 0 < m) (hM : 0 < M) (hQ : 0 < Q) (ha : 0 ≤ a) (hr : 0 ≤ r) :
    (Q * a / m) * (adversaryRadiusFactor m M Q H * r) ≤
      r * a / (8 * M * (H + 1 : ℝ)) := by
  have hθ : adversaryRadiusFactor m M Q H ≤ m / (8 * Q * M * (H + 1 : ℝ)) :=
    min_le_right _ _
  calc
    (Q * a / m) * (adversaryRadiusFactor m M Q H * r) ≤
        (Q * a / m) * ((m / (8 * Q * M * (H + 1 : ℝ))) * r) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hθ hr) (by positivity)
    _ = r * a / (8 * M * (H + 1 : ℝ)) := by
      field_simp


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
  obtain ⟨next, hnext, hsep⟩ :=
    exists_parameterBall_center_avoiding_finite_set hr ha hM hcover S hcard
  have hsmall : adversaryRadiusFactor m M Q H * r ≤ r / 2 := by
    have h := mul_le_mul_of_nonneg_right (adversaryRadiusFactor_le_half m M Q H) hr.le
    linarith
  have hsubset := A.parameterBall_next_subset hj hnext hsmall
  refine ⟨next, hnext, hsubset, ?_⟩
  intro u hu
  refine ⟨A.prefix_eq_on_parameterBall (Nat.succ_le_of_lt hj) hu, ?_⟩
  have hmove : |α u - α next| ≤ r * a / (8 * M * (H + 1 : ℝ)) := calc
    |α u - α next| ≤ (Q * a / m) * ‖u - next‖ := hmotion next hnext u (hsubset hu)
    _ ≤ (Q * a / m) * (adversaryRadiusFactor m M Q H * r) :=
      mul_le_mul_of_nonneg_left hu.2 (by positivity)
    _ ≤ r * a / (8 * M * (H + 1 : ℝ)) :=
      adversaryRadiusFactor_motion_bound hm hM hQ ha.le hr.le
  intro z hz
  rw [← dist_eq_norm]
  apply separation_retained_after_motion (center := (α next : ℂ)) (moved := (α u : ℂ))
  · rw [dist_eq_norm]
    have heq : 2 * (r * a / (8 * M * (H + 1 : ℝ))) =
        r * a / (4 * M * (H + 1 : ℝ)) := by field_simp; ring
    rw [heq]
    exact hsep z hz
  · simpa only [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hmove

end KungTraub
