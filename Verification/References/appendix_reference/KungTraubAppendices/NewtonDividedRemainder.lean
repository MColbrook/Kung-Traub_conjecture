import appendix_reference.KungTraubAppendices.ConfluentPermutation

/-! The Newton remainder coefficient is the canonical divided difference. -/

noncomputable section

open Polynomial Set

namespace KungTraubAppendices

/-- Appending the evaluation node exposes precisely the next Newton
coefficient, even if some or all of the nodes coincide. -/
theorem newtonPolynomial_append_coeff (f : ℝ → ℝ) (xs : List ℝ) (t : ℝ) :
    (newtonPolynomial f (xs ++ [t])).coeff xs.length = newtonRemainderFunction f xs t := by
  sorry

/-- The successive-slope remainder is the canonical divided difference with
the evaluation point as one further node. -/
theorem newtonRemainderFunction_eq_dividedDifference {f : ℝ → ℝ}
    (xs : List ℝ) (t : ℝ) (hf : ∀ z ∈ t :: xs, AnalyticAt ℝ f z) :
    newtonRemainderFunction f xs t = confluentDividedDifference f (t :: xs) := by
  sorry

/-- The exact remainder uses this same divided difference, with repetitions
retained, including coincident nodes. -/
theorem newtonPolynomial_dividedDifference_remainder {f : ℝ → ℝ}
    (xs : List ℝ) (t : ℝ) (hf : ∀ z ∈ t :: xs, AnalyticAt ℝ f z) :
    f t - (newtonPolynomial f xs).eval t =
      confluentDividedDifference f (t :: xs) * (xs.map (fun a => t - a)).prod := by
  sorry

end KungTraubAppendices
