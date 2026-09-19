import appendix_reference.KungTraub.LocalAndStoppingAlgorithms
import appendix_reference.KungTraubAppendices.HermiteInterpolation
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The observation method in Appendix A

The construction uses the `BoundedRealTree` stopping oracle. Interpolation
receives observed function values, earlier query locations and the reciprocal
of the single observed derivative.

The rules are defined on all transcripts. A zero derivative on a nonzero-value
branch returns the initial point; this branch is absent near a simple root.
The computed final output requires no further query.
-/

noncomputable section

open scoped BigOperators

namespace KungTraubAppendices

local instance instDecidableEqReal : DecidableEq ℝ := Classical.decEq ℝ

/-- The remaining value observations after the initial value and derivative.
`functionValues` are inverse-interpolation nodes; `points` are their ordinates.
The distinguished node `0` always denotes the initial observation. -/
def inverseHermiteTail : (remaining j : ℕ) →
    (Fin (j + 1) → ℝ) → (Fin (j + 1) → ℝ) → ℝ → ℝ →
      KungTraub.BoundedRealTree remaining
  | 0, _, _, _, _, next => .stop next
  | remaining + 1, j, functionValues, points, reciprocalDerivative, next =>
      .observe (.derivative next 0) fun value =>
        if value = 0 then .stop next else
          let extendedValues := Fin.snoc functionValues value
          let extendedPoints := Fin.snoc points next
          let H := hermiteWithDerivative Finset.univ extendedValues extendedPoints
            (0 : Fin (j + 2)) reciprocalDerivative
          inverseHermiteTail remaining (j + 1) extendedValues extendedPoints
            reciprocalDerivative (H.eval 0)

/-- The full bounded observation tree. Budgets below two are arbitrary total
extensions; all Appendix A results require `n ≥ 2`. -/
def inverseHermiteTree : (n : ℕ) → ℝ → KungTraub.BoundedRealTree n
  | 0, x => .stop x
  | 1, x => .stop x
  | remaining + 2, x =>
      .observe (.derivative x 0) fun value =>
        if value = 0 then .stop x else
          .observe (.derivative x 1) fun derivative =>
            if derivative = 0 then .stop x else
              inverseHermiteTail remaining 0 (fun _ => value) (fun _ => x)
                derivative⁻¹ (x - value / derivative)

/-- The stationary method chooses its bounded tree from the starting point alone. -/
def inverseHermiteMethod (n : ℕ) : KungTraub.StoppingRealAlgorithm n :=
  inverseHermiteTree n

/-- The same actual method in the fixed-slot oracle model, with idle padding. -/
def inverseHermiteAlgorithm (n : ℕ) : KungTraub.RealAlgorithm n :=
  (inverseHermiteMethod n).padded

/-- Every actual derivative-query location belongs to the real input domain. -/
def realExecutionIn {n : ℕ} (A : KungTraub.RealAlgorithm n)
    (f : ℝ → ℝ) (x : ℝ) (U : Set ℝ) : Prop :=
  ∀ j : Fin n,
    match A.query j x (A.prefix f x j.val j.isLt.le) with
    | .derivative z _ => z ∈ U
    | .idle => True

/-- The full interval-local attainment property, including query admissibility.
The input domain and its analytic function precede the local constants. -/
def RealIntervalUniversalLocalOrder {n : ℕ} (A : KungTraub.RealAlgorithm n)
    (p : ℝ) : Prop :=
  ∀ U : Set ℝ, IsOpen U → Set.OrdConnected U →
    ∀ f : ℝ → ℝ, (∀ t ∈ U, AnalyticAt ℝ f t) →
      ∀ α : ℝ, α ∈ U → KungTraub.SimpleRealRoot f α →
        ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧
          ∀ x : ℝ, 0 < |x - α| → |x - α| < δ →
            x ∈ U ∧ realExecutionIn A f x U ∧
              |A.run f x - α| ≤ C * Real.rpow |x - α| p

/-- The leading coefficients on `exp(x)-1`. Index zero is a harmless initial
convention; the empty product gives exactly `κ₁=1/2`. -/
def sharpnessCoefficient : ℕ → ℝ
  | 0 => 1
  | j + 1 => (∏ i : Fin j, sharpnessCoefficient (i.val + 1)) / ((j : ℝ) + 2)
termination_by j => j
decreasing_by omega

end KungTraubAppendices
