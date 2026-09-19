import KungTraub.GroupedParameterBalls
import KungTraub.FiniteFamilyGeometry

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

theorem FiniteRootFamily.grouped_initial_sensitivity_at {k : ℕ} {sizes : Fin k → ℕ}
    {ε x m M R wmin K : ℝ}
    (D : FiniteRootFamily (groupedObservationCount sizes) ε x m M R wmin K)
    (A : GroupedAffineAlgorithm (EuclideanSpace ℝ (Fin (groupedObservationCount sizes + 1))) sizes)
    (u : EuclideanSpace ℝ (Fin (groupedObservationCount sizes + 1))) (hu : ‖u‖ ≤ 1)
    (hε : 0 ≤ ε) :
    wmin * ε ≤ ‖(A.direction u x 0).starProjection (D.vector (D.root u))‖ := by
  have hw := D.weight_lower u hu
  have hcoord := PiLp.norm_apply_le (D.vector (D.root u)) (0 : Fin (groupedObservationCount sizes + 1))
  have heval : ‖D.vector (D.root u) (0 : Fin (groupedObservationCount sizes + 1))‖ =
      |D.weight (D.root u)| * ε := by
    simp [FiniteRootFamily.vector, realPolynomialEvaluationVector, abs_of_nonneg hε]
  rw [heval] at hcoord
  rw [A.direction_zero, Submodule.starProjection_eq_self_iff.mpr
    (show D.vector (D.root u) ∈
      (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin (groupedObservationCount sizes + 1)))) by trivial)]
  exact (mul_le_mul_of_nonneg_right hw hε).trans hcoord

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
  have hQ : 0 < 1 + K / (2 * m) := by positivity
  exact A.exists_next_ball_avoiding_finite_set hj hr ha hm hM hQ
    (D.root_interval _ hr ha hm hM hball hasens)
    (fun next hnext u hu => D.uniform_root_motion _ hr.le hr1 hm hK hball hasens hnext hu) S hcard

end KungTraub
