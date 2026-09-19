import appendix_reference.KungTraubAppendices.NewtonInterpolation
import Mathlib.Analysis.Analytic.Order

/-!
# All interpolation jets, including arbitrary coincidences

The exact Newton remainder has one linear factor for every list entry. Mathlib's
analytic-order product theorem and derivative characterization turn these factors
into all required derivative conditions, with no assumption of distinct nodes.
-/

noncomputable section

open Polynomial

namespace KungTraubAppendices

local instance instDecidableEqRealForJets : DecidableEq ℝ := Classical.decEq ℝ

theorem analyticAt_nodeProduct (xs : List ℝ) (b : ℝ) :
    AnalyticAt ℝ (fun t => (xs.map (fun a => t - a)).prod) b := by
  sorry

/-- Every occurrence of a node contributes one to the analytic order of the
product, regardless of zeros of the remaining analytic factor. -/
theorem count_le_analyticOrderAt_nodeProduct_mul (xs : List ℝ) {R : ℝ → ℝ} {b : ℝ}
    (hR : AnalyticAt ℝ R b) :
    (xs.count b : ℕ∞) ≤
      analyticOrderAt (fun t => (xs.map (fun a => t - a)).prod * R t) b := by
  sorry

/-- The Newton error vanishes to at least the full listed multiplicity. -/
theorem newtonPolynomial_error_jet_zero (xs : List ℝ) {f : ℝ → ℝ} {b : ℝ}
    (hf : AnalyticAt ℝ f b) {k : ℕ} (hk : k < xs.count b) :
    iteratedDeriv k (fun t => f t - (newtonPolynomial f xs).eval t) b = 0 := by
  sorry

/-- Every prescribed derivative of the analytic function equals that of the
constructed polynomial, through one less than the node's multiplicity. -/
theorem newtonPolynomial_jet_eq (xs : List ℝ) {f : ℝ → ℝ} {b : ℝ}
    (hf : AnalyticAt ℝ f b) {k : ℕ} (hk : k < xs.count b) :
    iteratedDeriv k (fun t => (newtonPolynomial f xs).eval t) b = iteratedDeriv k f b := by
  sorry

end KungTraubAppendices
