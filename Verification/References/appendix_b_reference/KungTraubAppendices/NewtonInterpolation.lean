import appendix_b_reference.KungTraubAppendices.HermiteCalculus
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Newton interpolation with repeated nodes

Mathlib's `dslope` uses the derivative at a repeated node. Successive applications
therefore give the usual recursive Newton construction with all coincidences
allowed. These polynomials describe the interpolation error of the inverse Hermite method.

The analytic extension at a repeated node reuses Mathlib's power-series theorem
`HasFPowerSeriesAt.has_fpower_series_dslope_fslope`.
-/

noncomputable section

open Polynomial Set

namespace KungTraubAppendices

/-- The derivative-valued extension of a slope preserves local analyticity,
at the distinguished node and at every other point. -/
theorem analyticAt_dslope {f : ℝ → ℝ} {b : ℝ} (hf : AnalyticAt ℝ f b) (a : ℝ) :
    AnalyticAt ℝ (dslope f a) b := by
  sorry

/-- Successive slopes, including all derivative-valued diagonal extensions. -/
def newtonRemainderFunction (f : ℝ → ℝ) : List ℝ → ℝ → ℝ
  | [] => f
  | a :: xs => newtonRemainderFunction (dslope f a) xs

/-- The actual Newton interpolation polynomial for a list with repetitions. -/
def newtonPolynomial (f : ℝ → ℝ) : List ℝ → ℝ[X]
  | [] => 0
  | a :: xs => C (f a) + (X - C a) * newtonPolynomial (dslope f a) xs

theorem newtonRemainderFunction_analyticAt {f : ℝ → ℝ} {b : ℝ}
    (hf : AnalyticAt ℝ f b) (xs : List ℝ) :
    AnalyticAt ℝ (newtonRemainderFunction f xs) b := by
  sorry

/-- Newton's exact algebraic remainder identity, without distinctness or
analytic hypotheses. Analyticity supplies the derivative meaning afterwards. -/
theorem newtonPolynomial_remainder (f : ℝ → ℝ) (xs : List ℝ) (t : ℝ) :
    f t - (newtonPolynomial f xs).eval t =
      (xs.map (fun a => t - a)).prod * newtonRemainderFunction f xs t := by
  sorry

/-- The construction has the full Hermite degree bound even with repetitions. -/
theorem newtonPolynomial_natDegree_le (f : ℝ → ℝ) (xs : List ℝ) :
    (newtonPolynomial f xs).natDegree ≤ xs.length - 1 := by
  sorry

end KungTraubAppendices
