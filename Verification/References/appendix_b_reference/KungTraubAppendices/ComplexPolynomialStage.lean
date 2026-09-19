import appendix_b_reference.KungTraubAppendices.ComplexCorrectionGeometry
import appendix_b_reference.KungTraubAppendices.ComplexPolynomialFamilyRoots
import appendix_b_reference.KungTraubAppendices.ComplexCorrectionObservations
import appendix_b_reference.KungTraubAppendices.ComplexPreservingFactor
import appendix_b_reference.KungTraubAppendices.ComplexFiniteAdversary
import appendix_b_reference.KungTraub.DiagonalEstimates

/-!
# Complex polynomial families and one adversarial stage

Near-identity polynomial bounds, the preserving factor and the finite adversary
give one stage. The multiplier, common family threshold and positive error
constant are chosen before epsilon. Estimates hold on the closed unit spatial
disc and the complex Euclidean unit parameter ball.

The construction follows `KungTraub.GaussianFiniteFamily` and
`KungTraub.EntireStageConstruction`, using their real scale-selection lemma.
Root existence follows from the contraction argument in `ComplexRoots`.
-/

noncomputable section

open Polynomial Set KungTraub
open scoped BigOperators

namespace KungTraubAppendices

/-- A fixed nonzero continuous complex weight is uniformly bounded away from
zero in one neighbourhood, independently of the eventual family parameter. -/
theorem exists_complex_weight_lower_bound {w : ℂ → ℂ} {a : ℂ}
    (hw : ContinuousAt w a) (hwa : w a ≠ 0) :
    ∃ δ > 0, ∀ t : ℂ, ‖t - a‖ < δ → ‖w a‖ / 2 ≤ ‖w t‖ := by
  sorry

/-- The actual polynomial family has a common scale threshold, with
constants fixed before epsilon. -/
theorem complexPolynomialCorrection_exists_finiteRootFamily
    {f p : Polynomial ℂ} {n : ℕ} {lam b B : ℝ} {a : ℂ}
    (hf : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖f.eval z - z‖ ≤ B ∧ ‖f.derivative.eval z - 1‖ ≤ B)
    (hsmall : ComplexCorrectionSmall p n lam b) (hb : 0 ≤ b) (hbsmall : b ≤ 1 / 32)
    (hbudget : B + b ≤ 1 / 16) (ha : ‖a‖ ≤ 1 / 16) (hfa : f.eval a = 0)
    (hwa : (lam : ℂ) * p.eval a ≠ 0) :
    ∃ η > 0, ∀ ε : ℝ, 0 < ε → ε < η →
      ∃ D : ComplexFiniteRootFamily n ε (a + (ε : ℂ)) (1 / 2) (3 / 2) (5 / 4)
          (‖(lam : ℂ) * p.eval a‖ / 2) b,
        (∀ u z, D.function u z =
          (f + C (lam : ℂ) * complexCorrectionPolynomial p n ε (a + (ε : ℂ)) u).eval z) ∧
        D.weight = (fun z => (lam : ℂ) * p.eval z) ∧
        D.domain = Metric.closedBall (0 : ℂ) 1 ∧
        ∀ u, ‖u‖ ≤ 1 →
          ‖D.root u‖ ≤ (1 / 16 : ℝ) ∧
          SimpleComplexRoot (D.function u) (D.root u) ∧
          (∀ z : ℂ, ‖z‖ ≤ 1 → D.function u z = 0 → z = D.root u) ∧
          ‖D.root u - a‖ ≤ 4 * b * ε ∧
          (3 / 4 : ℝ) * ε ≤ ‖a + (ε : ℂ) - D.root u‖ := by
  sorry

/-- The selected correction absorbs the positive real multiplier into one
polynomial. Saved derivative jets are preserved at all complex locations;
nonzero values are required and retained only inside the closed unit disc. -/
structure ComplexPolynomialStageChoice {n : ℕ} (A : ComplexAlgorithm n)
    (f : Polynomial ℂ) (Q : Finset ComplexQuery) (a : ℂ) (b R B p : ℝ) (s : ℕ) where
  correction : Polynomial ℂ
  epsilon : ℝ
  root : ℂ
  coefficient : ℝ
  epsilon_pos : 0 < epsilon
  epsilon_cap : epsilon < 1 / ((s : ℝ) + 1)
  epsilon_quarter : epsilon < 1 / 4
  coefficient_pos : 0 < coefficient
  preserving_factor : complexPreservingFactor Q ∣ correction
  disc_bound : ComplexPolynomialDiscBound correction R (b / 2)
  sup_sum_bound :
    sSup ((fun z : ℂ => ‖correction.eval z‖) '' Metric.closedBall (0 : ℂ) R) +
      sSup ((fun z : ℂ => ‖deriv (fun t => correction.eval t) z‖) '' Metric.closedBall (0 : ℂ) 1) ≤ b
  root_bound : ‖root‖ ≤ (1 / 16 : ℝ)
  simple_root : SimpleComplexRoot (fun z => (f + correction).eval z) root
  unique_root : ∀ z : ℂ, ‖z‖ ≤ 1 → (f + correction).eval z = 0 → z = root
  root_shift : ‖root - a‖ ≤ 4 * b * epsilon
  start_lower : (3 / 4 : ℝ) * epsilon ≤ ‖a + (epsilon : ℂ) - root‖
  start_upper : ‖a + (epsilon : ℂ) - root‖ ≤ (5 / 4 : ℝ) * epsilon
  error_bound : coefficient * epsilon ^ B ≤
    ‖A.run (fun z => (f + correction).eval z) (a + (epsilon : ℂ)) - root‖
  amplification : ((s : ℝ) + 1) * (2 * epsilon) ^ p ≤ (coefficient / 2) * epsilon ^ B
  old_jets : ∀ z k, ComplexQuery.derivative z k ∈ Q →
    iteratedDeriv k (fun t => (f + correction).eval t) z = iteratedDeriv k (fun t => f.eval t) z
  old_values : ∀ z ∈ complexQueryNodes Q, ‖z‖ ≤ 1 → (f + correction).eval z ≠ 0
  new_root_avoidance : ∀ (j : Fin n) z k,
    A.actualQuery (fun t => (f + correction).eval t) (a + (epsilon : ℂ)) j =
      .derivative z k → root ≠ z
  new_values : ∀ (j : Fin n) z k,
    A.actualQuery (fun t => (f + correction).eval t) (a + (epsilon : ℂ)) j =
      .derivative z k → ‖z‖ ≤ 1 → (f + correction).eval z ≠ 0

/-- Every actual finite polynomial history with the budget margin extends
by a stage. The common threshold and error constant do not depend on epsilon. -/
theorem exists_complexPolynomialStageChoice {n : ℕ} (A : ComplexAlgorithm n) (hn : 0 < n)
    (f : Polynomial ℂ) (Q : Finset ComplexQuery) {a : ℂ} {b R B p : ℝ}
    (hf : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖f.eval z - z‖ ≤ B ∧ ‖f.derivative.eval z - 1‖ ≤ B)
    (ha : ‖a‖ ≤ 1 / 16) (hroot : f.eval a = 0)
    (hold : ∀ z ∈ complexQueryNodes Q, ‖z‖ ≤ 1 → f.eval z ≠ 0)
    (hb : 0 < b) (hbsmall : b ≤ 1 / 32) (hbudget : B + b ≤ 1 / 16)
    (hR : 1 ≤ R) (hp : (orderBound n : ℝ) < p) (s : ℕ) :
    Nonempty (ComplexPolynomialStageChoice A f Q a b R (orderBound n : ℝ) p s) := by
  sorry

/-- The stage error is strictly positive, so the next geometric budget can also
satisfy the exact positive error and scale caps. -/
theorem ComplexPolynomialStageChoice.error_pos {n : ℕ} {A : ComplexAlgorithm n}
    {f : Polynomial ℂ} {Q : Finset ComplexQuery} {a : ℂ} {b R B p : ℝ} {s : ℕ}
    (D : ComplexPolynomialStageChoice A f Q a b R B p s) :
    0 < ‖A.run (fun z => (f + D.correction).eval z) (a + (D.epsilon : ℂ)) - D.root‖ := by
  sorry

/-- The exact budget extension follows from the derived stage error. -/
theorem ComplexPolynomialStageChoice.exists_next_budget {n : ℕ} {A : ComplexAlgorithm n}
    {f : Polynomial ℂ} {Q : Finset ComplexQuery} {a : ℂ} {b R B p : ℝ} {s : ℕ}
    (D : ComplexPolynomialStageChoice A f Q a b R B p s) (hb : 0 < b) :
    ∃ next : ℝ, 0 < next ∧ next ≤ b / 2 ∧
      next ≤ ‖A.run (fun z => (f + D.correction).eval z) (a + (D.epsilon : ℂ)) - D.root‖ / 32 ∧
      next ≤ D.epsilon / 32 := by
  sorry

end KungTraubAppendices
