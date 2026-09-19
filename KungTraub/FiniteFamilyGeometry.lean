import KungTraub.AffinePolynomialInformation
import KungTraub.AdversaryStep

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
  rw [D.affine u hu t ht, D.affine center hc t ht, inner_sub_left]
  unfold vector
  ring

theorem FiniteRootFamily.root_interval (D : FiniteRootFamily n ε x m M R wmin K)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin (n + 1))))
    {center : EuclideanSpace ℝ (Fin (n + 1))} {r a : ℝ}
    (hr : 0 < r) (ha : 0 < a) (hm : 0 < m) (hM : 0 < M)
    (hball : ∀ u ∈ parameterBall center V r, ‖u‖ ≤ 1)
    (hasens : a = ‖V.starProjection (D.vector (D.root center))‖) :
    Icc (D.root center - r * a / (2 * M)) (D.root center + r * a / (2 * M)) ⊆
      D.root '' parameterBall center V (r / 2) := by
  have hc := hball center (parameterBall_center center V hr.le)
  exact root_parameterBall_image_contains_interval V D.convex hr ha hm hM hasens
    (fun u hu => D.continuous u (hball u hu))
    (fun u hu => D.differentiable u (hball u hu))
    (fun u hu => D.lower u (hball u hu)) (fun u hu => D.upper u (hball u hu))
    (fun u hu => D.is_root u (hball u hu)) (fun u hu => D.root_mem u (hball u hu))
    (fun u hu _ ht => D.affine_difference (hball u hu) hc ht)

theorem FiniteRootFamily.uniform_root_motion (D : FiniteRootFamily n ε x m M R wmin K)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin (n + 1))))
    {center next u : EuclideanSpace ℝ (Fin (n + 1))} {r a : ℝ}
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (hm : 0 < m) (hK : 0 ≤ K)
    (hball : ∀ u ∈ parameterBall center V r, ‖u‖ ≤ 1)
    (hasens : a = ‖V.starProjection (D.vector (D.root center))‖)
    (hnext : next ∈ parameterBall center V (r / 2)) (hu : u ∈ parameterBall center V r) :
    |D.root u - D.root next| ≤ ((1 + K / (2 * m)) * a / m) * ‖u - next‖ := by
  have hnext' := parameterBall_mono_radius (by linarith : r / 2 ≤ r) hnext
  have hn := hball next hnext'
  have hc := hball center (parameterBall_center center V hr)
  have hunit := hball u hu
  have haffine : ∀ w ∈ parameterBall center V r, ∀ y ∈ D.interval,
      D.function w y = D.function center y + ⟪w - center, D.vector y⟫_ℝ :=
    fun w hw _ hy => D.affine_difference (hball w hw) hc hy
  have hsens := sensitivity_inside_half_parameterBall V D.convex hr hr1 hm hK hasens hnext
    (D.continuous next hn) (D.differentiable next hn) (D.lower next hn)
    (D.is_root next hn) (D.is_root center hc) (D.root_mem next hn) (D.root_mem center hc)
    haffine (D.vector_lipschitz _ (D.root_mem next hn) _ (D.root_mem center hc))
  have hmove := root_motion_inside_parameterBall V D.convex hm hnext' hu
    (D.continuous u hunit) (D.differentiable u hunit) (D.lower u hunit)
    (D.is_root u hunit) (D.is_root next hn) (D.root_mem u hunit) (D.root_mem next hn) haffine
  exact hmove.trans (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hsens hm.le) (norm_nonneg _))

theorem FiniteRootFamily.initial_sensitivity (D : FiniteRootFamily n ε x m M R wmin K)
    (A : AffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) n) (hε : 0 ≤ ε) :
    wmin * ε ≤ ‖(A.direction 0 x 0).starProjection (D.vector (D.root 0))‖ := by
  have hw := D.weight_lower 0 (by simp)
  have hcoord := PiLp.norm_apply_le (D.vector (D.root 0)) (0 : Fin (n + 1))
  have heval : ‖D.vector (D.root 0) (0 : Fin (n + 1))‖ = |D.weight (D.root 0)| * ε := by
    simp [vector, realPolynomialEvaluationVector, abs_of_nonneg hε]
  rw [heval] at hcoord
  have hbound := (mul_le_mul_of_nonneg_right hw hε).trans hcoord
  have hdir : A.direction 0 x 0 = ⊤ := scalarPrefixKernel_zero _
  rw [hdir, Submodule.starProjection_eq_self_iff.mpr (show D.vector (D.root 0) ∈ (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin (n + 1)))) by trivial)]
  exact hbound

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
  have hQ : 0 < 1 + K / (2 * m) := by positivity
  exact A.exists_next_ball_avoiding_finite_set hj hr ha hm hM hQ
    (D.root_interval _ hr ha hm hM hball hasens)
    (fun next hnext u hu => D.uniform_root_motion _ hr.le hr1 hm hK hball hasens hnext hu) S hcard

end KungTraub
