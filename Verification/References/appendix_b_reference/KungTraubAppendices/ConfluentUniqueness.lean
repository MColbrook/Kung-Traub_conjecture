import appendix_b_reference.KungTraubAppendices.ConfluentInterpolation

/-! Polynomial determination by arbitrary confluent interpolation conditions. -/

noncomputable section

open Polynomial Set

namespace KungTraubAppendices

/-- A polynomial of degree at most `n` with `n+1` prescribed zeros counted
with multiplicity has vanishing coefficient of degree `n`. -/
theorem polynomial_top_coeff_zero_of_ordered_jets (n : ℕ)
    (x : Fin (n + 1) → ℝ) (hx : Monotone x) {P : ℝ[X]}
    (hdegree : P.degree ≤ (n : WithBot ℕ))
    (hjets : OrderedVanishingJets (fun t => P.eval t) x) : P.coeff n = 0 := by
  sorry

/-- All coefficients vanish: the complete confluent interpolation conditions
determine a polynomial of degree at most `n` uniquely. -/
theorem polynomial_eq_zero_of_ordered_jets (n : ℕ)
    (x : Fin (n + 1) → ℝ) (hx : Monotone x) {P : ℝ[X]}
    (hdegree : P.degree ≤ (n : WithBot ℕ))
    (hjets : OrderedVanishingJets (fun t => P.eval t) x) : P = 0 := by
  sorry

/-- The Newton polynomial is the unique polynomial satisfying all prescribed
derivatives at all nodes, including arbitrarily repeated nodes. -/
theorem newtonPolynomial_unique (n : ℕ) {f : ℝ → ℝ}
    (x : Fin (n + 1) → ℝ) (hx : Monotone x) (hf : ∀ i, AnalyticAt ℝ f (x i))
    {P : ℝ[X]} (hdegree : P.degree ≤ (n : WithBot ℕ))
    (hdata : ∀ i (k : ℕ), k < (List.ofFn x).count (x i) →
      iteratedDeriv k (fun t => P.eval t) (x i) = iteratedDeriv k f (x i)) :
    P = newtonPolynomial f (List.ofFn x) := by
  sorry

end KungTraubAppendices
