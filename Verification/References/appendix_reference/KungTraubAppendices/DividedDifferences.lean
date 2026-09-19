import appendix_reference.KungTraubAppendices.ConfluentInterpolation
import Mathlib.Data.List.Sort

/-!
# Confluent divided differences on arbitrary lists

The divided difference is the top coefficient of the Newton interpolation
polynomial, with the nodes sorted and their multiplicities retained. The empty
list receives an arbitrary total value; every mathematical assertion below
specifies a nonempty list. Nodes may coincide.
-/

noncomputable section

open Polynomial Set

namespace KungTraubAppendices

def confluentDividedDifference (f : ℝ → ℝ) (xs : List ℝ) : ℝ :=
  (newtonPolynomial f (xs.mergeSort (· ≤ ·))).coeff (xs.length - 1)

/-- Sorting preserves every node and its multiplicity, so the full confluent
mean-value formula holds without a prescribed ordering or distinctness. -/
theorem confluentDividedDifference_mean_value {n : ℕ} {f : ℝ → ℝ} {a b : ℝ}
    (hf : AnalyticOnNhd ℝ f (Icc a b)) (xs : List ℝ) (hlen : xs.length = n + 1)
    (hxin : ∀ z ∈ xs, z ∈ Icc a b) :
    ∃ c ∈ Icc a b, confluentDividedDifference f xs =
      iteratedDeriv n f c / (n.factorial : ℝ) := by
  sorry

/-- The factorial-normalized uniform bound includes arbitrary coincident nodes. -/
theorem confluentDividedDifference_abs_le {n : ℕ} {f : ℝ → ℝ} {a b D : ℝ}
    (hf : AnalyticOnNhd ℝ f (Icc a b)) (xs : List ℝ) (hlen : xs.length = n + 1)
    (hxin : ∀ z ∈ xs, z ∈ Icc a b)
    (hbound : ∀ c ∈ Icc a b, |iteratedDeriv n f c| / (n.factorial : ℝ) ≤ D) :
    |confluentDividedDifference f xs| ≤ D := by
  sorry

/-- On the full diagonal the definition gives the exact derivative convention. -/
theorem confluentDividedDifference_replicate (n : ℕ) {f : ℝ → ℝ} {a : ℝ}
    (hf : AnalyticAt ℝ f a) :
    confluentDividedDifference f (List.replicate (n + 1) a) =
      iteratedDeriv n f a / (n.factorial : ℝ) := by
  sorry

end KungTraubAppendices
