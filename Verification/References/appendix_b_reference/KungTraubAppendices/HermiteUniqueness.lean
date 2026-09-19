import appendix_b_reference.KungTraubAppendices.HermiteInterpolation

/-!
# Uniqueness of the inverse Hermite interpolant

After one linear factor is removed, the derivative condition supplies the
missing value condition. Mathlib's indexed polynomial determination theorem
then applies. This argument works over every field.
-/

noncomputable section

open Polynomial

namespace KungTraubAppendices

variable {𝕜 ι : Type*} [Field 𝕜] [DecidableEq ι]

/-- A polynomial with these values and derivative cannot have degree at most
the number of distinct nodes unless it vanishes identically. -/
theorem eq_zero_of_values_and_derivative_zero {s : Finset ι} {nodes : ι → 𝕜}
    (hnodes : Set.InjOn nodes s) {i : ι} (hi : i ∈ s) {P : 𝕜[X]}
    (hdegree : P.degree ≤ (s.card : WithBot ℕ))
    (hvalues : ∀ j ∈ s, P.eval (nodes j) = 0)
    (hderivative : P.derivative.eval (nodes i) = 0) : P = 0 := by
  sorry

/-- The explicit inverse Hermite interpolant is uniquely determined by its
degree, all supplied values, and the single supplied derivative. -/
theorem hermiteWithDerivative_unique {s : Finset ι} {nodes : ι → 𝕜}
    (values : ι → 𝕜) (d : 𝕜) (hnodes : Set.InjOn nodes s)
    {i : ι} (hi : i ∈ s) {P : 𝕜[X]}
    (hdegree : P.degree ≤ (s.card : WithBot ℕ))
    (hvalues : ∀ j ∈ s, P.eval (nodes j) = values j)
    (hderivative : P.derivative.eval (nodes i) = d) :
    P = hermiteWithDerivative s nodes values i d := by
  sorry

/-- Existence and uniqueness include the same full degree bound as the paper. -/
theorem existsUnique_hermiteWithDerivative {s : Finset ι} {nodes : ι → 𝕜}
    (values : ι → 𝕜) (d : 𝕜) (hnodes : Set.InjOn nodes s)
    {i : ι} (hi : i ∈ s) :
    ∃! P : 𝕜[X], P.degree ≤ (s.card : WithBot ℕ) ∧
      (∀ j ∈ s, P.eval (nodes j) = values j) ∧
      P.derivative.eval (nodes i) = d := by
  sorry

end KungTraubAppendices
