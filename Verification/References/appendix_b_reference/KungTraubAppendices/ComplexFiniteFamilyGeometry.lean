import appendix_b_reference.KungTraubAppendices.ComplexPolynomialSensitivity
import appendix_b_reference.KungTraubAppendices.ComplexAdversaryStep

/-!
# Complex finite families and their geometric step

The family consists of functions and selected roots satisfying the spatial
bounds and affine polynomial dependence of Appendix B. The domain margin
ensures that the discs used in the spatial estimates remain in the domain.

The argument follows `KungTraub.FiniteFamilyGeometry` for complex Euclidean
parameters, with the bilinear/Hermitian convention and Appendix B's constants.
-/

noncomputable section

open Set

namespace KungTraubAppendices

/-- Fixed-scale complex family hypotheses, before the adversarial induction.
All bounds apply on the stated domain and the complete closed unit parameter ball. -/
structure ComplexFiniteRootFamily (n : ℕ) (ε : ℝ) (x : ℂ) (m M R wmin K : ℝ) where
  function : EuclideanSpace ℂ (Fin (n + 1)) → ℂ → ℂ
  root : EuclideanSpace ℂ (Fin (n + 1)) → ℂ
  weight : ℂ → ℂ
  domain : Set ℂ
  lower : ∀ u, ‖u‖ ≤ 1 → ∀ z ∈ domain, ∀ t ∈ domain,
    m * ‖z - t‖ ≤ ‖function u z - function u t‖
  upper : ∀ u, ‖u‖ ≤ 1 → ∀ z ∈ domain, ∀ t ∈ domain,
    ‖function u z - function u t‖ ≤ M * ‖z - t‖
  is_root : ∀ u, ‖u‖ ≤ 1 → function u (root u) = 0
  root_mem : ∀ u, ‖u‖ ≤ 1 → root u ∈ domain
  affine : ∀ u, ‖u‖ ≤ 1 → ∀ t ∈ domain,
    function u t = function 0 t +
      complexBilinearDot u (complexPolynomialEvaluationVector n ε (weight t) (t - x))
  root_distance : ∀ u, ‖u‖ ≤ 1 → ‖root u - x‖ ≤ R * ε
  weight_lower : ∀ u, ‖u‖ ≤ 1 → wmin ≤ ‖weight (root u)‖
  vector_lipschitz : ∀ z ∈ domain, ∀ t ∈ domain,
    ‖complexPolynomialEvaluationVector n ε (weight z) (z - x) -
      complexPolynomialEvaluationVector n ε (weight t) (t - x)‖ ≤ K * ‖z - t‖
  geometric_containment : ∀ u, ‖u‖ ≤ 1 →
    Metric.closedBall (root u)
      (complexInitialRadius M K *
        ‖complexPolynomialEvaluationVector n ε (weight (root u)) (root u - x)‖ / (4 * M)) ⊆
      domain

variable {n : ℕ} {ε : ℝ} {x : ℂ} {m M R wmin K : ℝ}

/-- The actual vector of bilinear evaluations for this scaled family. -/
def ComplexFiniteRootFamily.vector (D : ComplexFiniteRootFamily n ε x m M R wmin K)
    (t : ℂ) : EuclideanSpace ℂ (Fin (n + 1)) :=
  complexPolynomialEvaluationVector n ε (D.weight t) (t - x)

/-- Subtraction of the actual affine family identities gives the exact
bilinear parameter difference used by the root-motion estimates. -/
theorem ComplexFiniteRootFamily.affine_difference
    (D : ComplexFiniteRootFamily n ε x m M R wmin K)
    {u center : EuclideanSpace ℂ (Fin (n + 1))}
    (hu : ‖u‖ ≤ 1) (hc : ‖center‖ ≤ 1) {t : ℂ} (ht : t ∈ D.domain) :
    D.function u t = D.function center t + complexBilinearDot (u - center) (D.vector t) := by
  sorry

/-- Projection and radius monotonicity derive every required projected-disc
containment from the explicit unprojected uniform domain margin. -/
theorem ComplexFiniteRootFamily.projected_root_disc_contained
    (D : ComplexFiniteRootFamily n ε x m M R wmin K)
    (V : Submodule ℂ (EuclideanSpace ℂ (Fin (n + 1))))
    {u : EuclideanSpace ℂ (Fin (n + 1))} {r : ℝ}
    (hu : ‖u‖ ≤ 1) (hr : 0 ≤ r) (hr₀ : r ≤ complexInitialRadius M K) (hM : 0 < M) :
    Metric.closedBall (D.root u)
      (r * ‖V.starProjection (complexConjVector (D.vector (D.root u)))‖ / (4 * M)) ⊆
      D.domain := by
  sorry

/-- The actual roots attain the complete projected disc, with its containment
derived first from the family domain margin. -/
theorem ComplexFiniteRootFamily.root_disc
    (D : ComplexFiniteRootFamily n ε x m M R wmin K)
    (V : Submodule ℂ (EuclideanSpace ℂ (Fin (n + 1))))
    {center : EuclideanSpace ℂ (Fin (n + 1))} {r a : ℝ}
    (hr : 0 < r) (hr₀ : r ≤ complexInitialRadius M K) (ha : 0 < a)
    (hm : 0 < m) (hM : 0 < M) (hK : 0 ≤ K)
    (hball : ∀ u ∈ complexParameterBall center V r, ‖u‖ ≤ 1)
    (hasens : a = ‖V.starProjection (complexConjVector (D.vector (D.root center)))‖) :
    Metric.closedBall (D.root center) (r * a / (4 * M)) ⊆
      D.root '' complexParameterBall center V (r / 2) := by
  sorry

/-- Coordinate zero yields the initial sensitivity at every unit parameter;
the empty-prefix direction is the full complex parameter space. -/
theorem ComplexFiniteRootFamily.initial_sensitivity
    (D : ComplexFiniteRootFamily n ε x m M R wmin K)
    (A : ComplexAffineAlgorithm (EuclideanSpace ℂ (Fin (n + 1))) n)
    (u : EuclideanSpace ℂ (Fin (n + 1))) (hu : ‖u‖ ≤ 1) (hε : 0 ≤ ε) :
    wmin * ε ≤ ‖(A.direction u x 0).starProjection (complexConjVector (D.vector (D.root u)))‖ := by
  sorry

/-- The fixed-scale family supplies every geometric hypothesis of the actual
next-ball step, with the complex retained separation denominator sixteen. -/
theorem ComplexFiniteRootFamily.next_ball
    (D : ComplexFiniteRootFamily n ε x m M R wmin K)
    (A : ComplexAffineAlgorithm (EuclideanSpace ℂ (Fin (n + 1))) n)
    {center : EuclideanSpace ℂ (Fin (n + 1))} {r a : ℝ} {j H : ℕ}
    (hj : j < n) (hr : 0 < r) (hr₀ : r ≤ complexInitialRadius M K) (ha : 0 < a)
    (hm : 0 < m) (hM : 0 < M) (hK : 0 ≤ K)
    (hball : ∀ u ∈ complexParameterBall center (A.direction center x j) r, ‖u‖ ≤ 1)
    (hasens : a = ‖(A.direction center x j).starProjection
      (complexConjVector (D.vector (D.root center)))‖)
    (S : Finset ℂ) (hcard : S.card ≤ H) :
    ∃ next ∈ complexParameterBall center (A.direction center x j) (r / 2),
      complexParameterBall next (A.direction next x (j + 1))
          (complexRadiusFactor m M (1 + K / (2 * m)) H * r) ⊆
        complexParameterBall center (A.direction center x j) r ∧
      ∀ u ∈ complexParameterBall next (A.direction next x (j + 1))
          (complexRadiusFactor m M (1 + K / (2 * m)) H * r),
        A.prefix u x (j + 1) (Nat.succ_le_of_lt hj) =
            A.prefix next x (j + 1) (Nat.succ_le_of_lt hj) ∧
        ∀ z ∈ S, r * a / (16 * M * ((H : ℝ) + 1)) ≤ ‖D.root u - z‖ := by
  sorry

/-- At the final transcript, the attained disc yields the exact complex
error radius r*a/(4M), without an extra query at the output. -/
theorem ComplexFiniteRootFamily.exists_large_error
    (D : ComplexFiniteRootFamily n ε x m M R wmin K)
    (A : ComplexAffineAlgorithm (EuclideanSpace ℂ (Fin (n + 1))) n)
    {center : EuclideanSpace ℂ (Fin (n + 1))} {r a : ℝ}
    (hr : 0 < r) (hr₀ : r ≤ complexInitialRadius M K) (ha : 0 < a)
    (hm : 0 < m) (hM : 0 < M) (hK : 0 ≤ K)
    (hball : ∀ u ∈ complexParameterBall center (A.direction center x n) r, ‖u‖ ≤ 1)
    (hasens : a = ‖(A.direction center x n).starProjection
      (complexConjVector (D.vector (D.root center)))‖) :
    ∃ u ∈ complexParameterBall center (A.direction center x n) r,
      r * a / (4 * M) ≤ ‖A.run u x - D.root u‖ := by
  sorry

end KungTraubAppendices
