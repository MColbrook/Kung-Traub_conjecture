import support_reference.KungTraub.EntireWitnessAssembly
import support_reference.KungTraub.GaussianFiniteFamily
import support_reference.KungTraub.FiniteAdversary

/-!
# Constructing the discrete entire stages

The discrete construction in Section 4 of Matthew J. Colbrook's manuscript.
The next Gaussian correction is selected using the proved finite adversary.
Its analytic bounds, actual output error, new-query avoidance and exact old
observations follow from the finite-stage estimates.
-/

noncomputable section
open scoped BigOperators ContDiff

namespace KungTraub

def gaussianUpdatedFunction (P : Polynomial ℝ) (lam : ℝ) (Q : Polynomial ℝ) (t : ℝ) : ℝ :=
  t + gaussianPolynomial P t + lam * gaussianPolynomial Q t

theorem gaussianPolynomial_C_mul (lam : ℝ) (Q : Polynomial ℝ) (t : ℝ) :
    gaussianPolynomial (Polynomial.C lam * Q) t = lam * gaussianPolynomial Q t := by
  sorry

theorem complexGaussianPolynomial_C_mul (lam : ℝ) (Q : Polynomial ℝ) (z : ℂ) :
    complexGaussianPolynomial (Polynomial.C lam * Q) z =
      (lam : ℂ) * complexGaussianPolynomial Q z := by
  sorry

theorem gaussianUpdatedFunction_eq_base (P : Polynomial ℝ) (lam : ℝ) (Q : Polynomial ℝ) :
    gaussianUpdatedFunction P lam Q =
      fun t => t + gaussianPolynomial (P + Polynomial.C lam * Q) t := by
  sorry

/-- The data and invariants of one correction. The exponent B is a parameter
for both scalar and grouped observations. -/
structure GaussianStageChoice {n : ℕ} (A : RealAlgorithm n) (P : Polynomial ℝ)
    (Z : Finset ℝ) (orders : ℝ → ℕ) (a b R B p : ℝ) (s : ℕ) where
  polynomial : Polynomial ℝ
  multiplier : ℝ
  epsilon : ℝ
  root : ℝ
  coefficient : ℝ
  multiplier_pos : 0 < multiplier
  epsilon_pos : 0 < epsilon
  epsilon_cap : epsilon < 1 / ((s : ℝ) + 1)
  epsilon_quarter : epsilon < 1 / 4
  coefficient_pos : 0 < coefficient
  value_bound : ∀ t, |multiplier * gaussianPolynomial polynomial t| ≤ b
  deriv_bound : ∀ t, |deriv (fun y => multiplier * gaussianPolynomial polynomial y) t| ≤ b
  disc_bound : ∀ z : ℂ, ‖z‖ ≤ R → ‖(multiplier : ℂ) * complexGaussianPolynomial polynomial z‖ ≤ b
  is_root : gaussianUpdatedFunction P multiplier polynomial root = 0
  start_lower : (3 / 4 : ℝ) * epsilon ≤ a + epsilon - root
  start_upper : a + epsilon - root ≤ (5 / 4 : ℝ) * epsilon
  error_bound : coefficient * epsilon ^ B ≤
    |A.run (gaussianUpdatedFunction P multiplier polynomial) (a + epsilon) - root|
  amplification : ((s : ℝ) + 1) * (2 * epsilon) ^ p ≤ (coefficient / 2) * epsilon ^ B
  old_jets : ∀ z ∈ Z, ∀ k : ℕ, k ≤ orders z →
    iteratedDeriv k (gaussianUpdatedFunction P multiplier polynomial) z =
      iteratedDeriv k (fun t => t + gaussianPolynomial P t) z
  old_values : ∀ z ∈ Z, gaussianUpdatedFunction P multiplier polynomial z ≠ 0
  new_values : ∀ (j : Fin n) z k,
    A.actualQuery (gaussianUpdatedFunction P multiplier polynomial) (a + epsilon) j =
      .derivative z k → gaussianUpdatedFunction P multiplier polynomial z ≠ 0

theorem GaussianStageChoice.error_pos {n : ℕ} {A : RealAlgorithm n} {P : Polynomial ℝ}
    {Z : Finset ℝ} {orders : ℝ → ℕ} {a b R B p : ℝ} {s : ℕ}
    (D : GaussianStageChoice A P Z orders a b R B p s) :
    0 < |A.run (gaussianUpdatedFunction P D.multiplier D.polynomial) (a + D.epsilon) - D.root| := by
  sorry

theorem GaussianStageChoice.exists_next_budget {n : ℕ} {A : RealAlgorithm n}
    {P : Polynomial ℝ} {Z : Finset ℝ} {orders : ℝ → ℕ} {a b R B p : ℝ} {s : ℕ}
    (D : GaussianStageChoice A P Z orders a b R B p s) (hb : 0 < b) :
    ∃ next : ℝ, 0 < next ∧ next ≤ b / 2 ∧
      next ≤ |A.run (gaussianUpdatedFunction P D.multiplier D.polynomial)
        (a + D.epsilon) - D.root| / 32 ∧ next ≤ D.epsilon / 32 := by
  sorry

/-- The finite adversary supplies a next stage for every finite Gaussian
history satisfying the analytic bounds and having nonzero values at its old nodes.
The multiplier, root-family threshold and positive error coefficient precede epsilon. -/
theorem exists_gaussianStageChoice {n : ℕ} (A : RealAlgorithm n) (hn : 0 < n)
    (P : Polynomial ℝ) (Z : Finset ℝ) (orders : ℝ → ℕ) {a b R p : ℝ}
    (hbase : ∀ t : ℝ, |(t + gaussianPolynomial P t) - t| ≤ 1 / 16 ∧
      (15 : ℝ) / 16 ≤ deriv (fun y => y + gaussianPolynomial P y) t ∧
      deriv (fun y => y + gaussianPolynomial P y) t ≤ 17 / 16)
    (ha : |a| ≤ 1 / 4) (hroot : a + gaussianPolynomial P a = 0)
    (hold : ∀ z ∈ Z, z + gaussianPolynomial P z ≠ 0)
    (hb : 0 < b) (hbsmall : b ≤ 1 / 16) (hR : 0 ≤ R)
    (hp : (orderBound n : ℝ) < p) (s : ℕ) :
    Nonempty (GaussianStageChoice A P Z orders a b R (orderBound n : ℝ) p s) := by
  sorry

end KungTraub
