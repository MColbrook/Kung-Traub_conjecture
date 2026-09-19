import appendix_reference.KungTraubAppendices.ConfluentUniqueness
import appendix_reference.KungTraubAppendices.DividedDifferences

/-! The constructed Newton interpolant is independent of node ordering. -/

noncomputable section

open Polynomial Set

namespace KungTraubAppendices

/-- Uniqueness expressed on an arbitrary nonempty list, retaining every
prescribed derivative through its actual occurrence count. -/
theorem newtonPolynomial_unique_sorted_list {n : ℕ} {f : ℝ → ℝ}
    (xs : List ℝ) (hlen : xs.length = n + 1)
    (hf : ∀ z ∈ xs, AnalyticAt ℝ f z) {P : ℝ[X]}
    (hdegree : P.degree ≤ (n : WithBot ℕ))
    (hdata : ∀ z ∈ xs, ∀ k : ℕ, k < xs.count z →
      iteratedDeriv k (fun t => P.eval t) z = iteratedDeriv k f z) :
    P = newtonPolynomial f (xs.mergeSort (· ≤ ·)) := by
  sorry

/-- Sorting changes no interpolation condition and hence no polynomial. -/
theorem newtonPolynomial_eq_mergeSort {f : ℝ → ℝ} (xs : List ℝ)
    (hf : ∀ z ∈ xs, AnalyticAt ℝ f z) :
    newtonPolynomial f xs = newtonPolynomial f (xs.mergeSort (· ≤ ·)) := by
  sorry

/-- The canonical divided difference is the coefficient in any ordering. -/
theorem confluentDividedDifference_eq_coeff {f : ℝ → ℝ} (xs : List ℝ)
    (hf : ∀ z ∈ xs, AnalyticAt ℝ f z) :
    confluentDividedDifference f xs = (newtonPolynomial f xs).coeff (xs.length - 1) := by
  sorry

/-- The canonical definition retains only the node multiset, including all
multiplicities. This identity itself requires no regularity assumption. -/
theorem confluentDividedDifference_perm (f : ℝ → ℝ) {xs ys : List ℝ}
    (h : xs.Perm ys) : confluentDividedDifference f xs = confluentDividedDifference f ys := by
  sorry

end KungTraubAppendices
