import support_reference.KungTraub.AffinePolynomialInformation
import support_reference.KungTraub.AdversaryStep

/-!
# The fixed-scale family and its geometric step

The local analytic hypotheses for the finite-dimensional argument include
uniform derivative bounds, affine dependence on parameters, and bounds on
the selected roots and evaluation vectors. The Gaussian correction family
satisfies these hypotheses.
-/

noncomputable section
open Set
open scoped InnerProductSpace

namespace KungTraub

structure FiniteRootFamily (n : ℕ) (ε x m M R wmin K : ℝ) where
  function : EuclideanSpace ℝ (Fin (n + 1)) → ℝ → ℝ
  root : EuclideanSpace ℝ (Fin (n + 1)) → ℝ
  weight : ℝ → ℝ
  interval : Set ℝ
  convex : Convex ℝ interval
  continuous : ∀ u, ‖u‖ ≤ 1 → ContinuousOn (function u) interval
  differentiable : ∀ u, ‖u‖ ≤ 1 → DifferentiableOn ℝ (function u) (interior interval)
  lower : ∀ u, ‖u‖ ≤ 1 → ∀ t ∈ interior interval, m ≤ deriv (function u) t
  upper : ∀ u, ‖u‖ ≤ 1 → ∀ t ∈ interior interval, deriv (function u) t ≤ M
  is_root : ∀ u, ‖u‖ ≤ 1 → function u (root u) = 0
  root_mem : ∀ u, ‖u‖ ≤ 1 → root u ∈ interval
  affine : ∀ u, ‖u‖ ≤ 1 → ∀ t ∈ interval,
    function u t = function 0 t + ⟪u, realPolynomialEvaluationVector n ε (weight t) (t - x)⟫_ℝ
  root_distance : ∀ u, ‖u‖ ≤ 1 → |root u - x| ≤ R * ε
  weight_lower : ∀ u, ‖u‖ ≤ 1 → wmin ≤ |weight (root u)|
  vector_lipschitz : ∀ s ∈ interval, ∀ t ∈ interval,
    ‖realPolynomialEvaluationVector n ε (weight s) (s - x) -
      realPolynomialEvaluationVector n ε (weight t) (t - x)‖ ≤ K * |s - t|

variable {n : ℕ} {ε x m M R wmin K : ℝ}

def FiniteRootFamily.vector (D : FiniteRootFamily n ε x m M R wmin K) (t : ℝ) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  realPolynomialEvaluationVector n ε (D.weight t) (t - x)

theorem FiniteRootFamily.affine_difference (D : FiniteRootFamily n ε x m M R wmin K)
    {u center : EuclideanSpace ℝ (Fin (n + 1))} (hu : ‖u‖ ≤ 1) (hc : ‖center‖ ≤ 1)
    {t : ℝ} (ht : t ∈ D.interval) :
    D.function u t = D.function center t + ⟪u - center, D.vector t⟫_ℝ := by
  sorry

theorem FiniteRootFamily.root_interval (D : FiniteRootFamily n ε x m M R wmin K)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin (n + 1))))
    {center : EuclideanSpace ℝ (Fin (n + 1))} {r a : ℝ}
    (hr : 0 < r) (ha : 0 < a) (hm : 0 < m) (hM : 0 < M)
    (hball : ∀ u ∈ parameterBall center V r, ‖u‖ ≤ 1)
    (hasens : a = ‖V.starProjection (D.vector (D.root center))‖) :
    Icc (D.root center - r * a / (2 * M)) (D.root center + r * a / (2 * M)) ⊆
      D.root '' parameterBall center V (r / 2) := by
  sorry

theorem FiniteRootFamily.uniform_root_motion (D : FiniteRootFamily n ε x m M R wmin K)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin (n + 1))))
    {center next u : EuclideanSpace ℝ (Fin (n + 1))} {r a : ℝ}
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hm : 0 < m) (hK : 0 ≤ K)
    (hball : ∀ u ∈ parameterBall center V r, ‖u‖ ≤ 1)
    (hasens : a = ‖V.starProjection (D.vector (D.root center))‖)
    (hnext : next ∈ parameterBall center V (r / 2)) (hu : u ∈ parameterBall center V r) :
    |D.root u - D.root next| ≤ ((1 + K / (2 * m)) * a / m) * ‖u - next‖ := by
  sorry

theorem FiniteRootFamily.initial_sensitivity (D : FiniteRootFamily n ε x m M R wmin K)
    (A : AffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) n) (hε : 0 ≤ ε) :
    wmin * ε ≤ ‖(A.direction 0 x 0).starProjection (D.vector (D.root 0))‖ := by
  sorry

theorem FiniteRootFamily.next_ball (D : FiniteRootFamily n ε x m M R wmin K)
    (A : AffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) n)
    {center : EuclideanSpace ℝ (Fin (n + 1))} {r a : ℝ} {j H : ℕ}
    (hj : j < n) (hr : 0 < r) (hr1 : r ≤ 1) (ha : 0 < a)
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
