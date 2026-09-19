import appendix_reference.KungTraubAppendices.NewtonDividedRemainder
import appendix_reference.KungTraubAppendices.HermiteUniqueness
import appendix_reference.KungTraubAppendices.HermiteBounds

/-!
# The divided difference in the actual inverse Hermite remainder

The Newton polynomial on the repeated initial node and the full list of value
nodes satisfies exactly the observed Hermite conditions. Uniqueness identifies
it with the separately constructed polynomial used by the observation method.
-/

noncomputable section

open Polynomial Set

namespace KungTraubAppendices

/-- The analytical Newton construction is the actual one-derivative Hermite
interpolant whenever the value nodes are distinct. -/
theorem newtonPolynomial_eq_hermiteWithDerivative {n : ℕ} {g : ℝ → ℝ}
    (nodes : Fin (n + 1) → ℝ) (hnodes : Function.Injective nodes)
    (hg : ∀ i, AnalyticAt ℝ g (nodes i)) :
    newtonPolynomial g (nodes 0 :: List.ofFn nodes) =
      hermiteWithDerivative Finset.univ nodes (fun i => g (nodes i)) 0
        (deriv g (nodes 0)) := by
  sorry

/-- The Hermite remainder coefficient is the canonical divided difference
on the evaluation point and all value nodes, with the initial node repeated. -/
theorem hermiteWithDerivative_dividedDifference_remainder {n : ℕ} {g : ℝ → ℝ}
    (nodes : Fin (n + 1) → ℝ) (hnodes : Function.Injective nodes)
    (hg : ∀ i, AnalyticAt ℝ g (nodes i)) (t : ℝ) (hgt : AnalyticAt ℝ g t) :
    g t - (hermiteWithDerivative Finset.univ nodes (fun i => g (nodes i)) 0
        (deriv g (nodes 0))).eval t =
      confluentDividedDifference g (t :: nodes 0 :: List.ofFn nodes) *
        (doubleNodal Finset.univ nodes 0).eval t := by
  sorry

/-- At zero this is the signed coefficient formula of Appendix A, with
order `n+2`, exactly `n+3` nodes, and the distinguished square. -/
theorem hermiteWithDerivative_dividedDifference_remainder_zero {n : ℕ} {g : ℝ → ℝ}
    (nodes : Fin (n + 1) → ℝ) (hnodes : Function.Injective nodes)
    (hg : ∀ i, AnalyticAt ℝ g (nodes i)) (hgzero : AnalyticAt ℝ g 0) :
    (hermiteWithDerivative Finset.univ nodes (fun i => g (nodes i)) 0
        (deriv g (nodes 0))).eval 0 - g 0 =
      (-1 : ℝ) ^ (n + 1) *
        confluentDividedDifference g (0 :: nodes 0 :: List.ofFn nodes) *
        (nodes 0) ^ 2 * ∏ i ∈ (Finset.univ : Finset (Fin (n + 1))).erase 0, nodes i := by
  sorry

end KungTraubAppendices
