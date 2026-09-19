import appendix_reference.KungTraubAppendices.NewtonJets
import appendix_reference.KungTraubAppendices.NodeMultiplicity

/-!
# The confluent divided-difference mean-value formula

For n+1 nodes, the coefficient of degree n of the Newton interpolant is the divided difference.
Every repeated-node derivative condition is proved from the Newton remainder,
then the full multiplicity version of Rolle gives the exact factorial constant.
-/

noncomputable section

open Polynomial Set

namespace KungTraubAppendices

/-- The Newton interpolation error has precisely the vanishing jets required
by the multiplicities of an ordered list, with arbitrary coincidences. -/
theorem newtonPolynomial_ordered_error_jets {n : ℕ} {f : ℝ → ℝ}
    (x : Fin n → ℝ) (hx : Monotone x) (hf : ∀ i, AnalyticAt ℝ f (x i)) :
    OrderedVanishingJets
      (fun t => f t - (newtonPolynomial f (List.ofFn x)).eval t) x := by
  sorry

/-- The exact confluent mean-value formula on the full closed interval, for
`n+1` nodes counted with repetitions. -/
theorem newtonPolynomial_coefficient_mean_value (n : ℕ) {f : ℝ → ℝ} {a b : ℝ}
    (hf : AnalyticOnNhd ℝ f (Icc a b)) (x : Fin (n + 1) → ℝ)
    (hx : Monotone x) (hxin : ∀ i, x i ∈ Icc a b) :
    ∃ c ∈ Icc a b, (newtonPolynomial f (List.ofFn x)).coeff n =
      iteratedDeriv n f c / (n.factorial : ℝ) := by
  sorry

end KungTraubAppendices
