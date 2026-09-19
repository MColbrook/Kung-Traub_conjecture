import support_reference.KungTraub.PolynomialFrames
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

/-!
# Normalizing polynomial spaces in coefficient norm

These lemmas construct the required orthonormal coefficient frame from every
independent bounded-degree family, and normalize any nonzero member without changing
its roots. Gram--Schmidt and its span theorem are reused from Mathlib's implementation
by Jiale Miao, Kevin Buzzard and Alexander Bentkamp.
-/

noncomputable section

open Polynomial InnerProductSpace
open scoped BigOperators

namespace KungTraub

/-- Bounded-degree coefficient extraction preserves linear independence. -/
theorem polynomial_coefficientVector_linearIndependent {m d : ℕ}
    (p : Fin m → Polynomial ℂ) (hp : LinearIndependent ℂ p)
    (hdeg : ∀ i, (p i).natDegree ≤ d) :
    LinearIndependent ℂ (fun i => coefficientVector d (p i)) := by
  sorry

/-- Every independent bounded-degree polynomial family admits a coefficient-orthonormal
family of the same size and with exactly the same span. -/
theorem exists_polynomial_coefficient_orthonormal_frame {m d : ℕ}
    (p : Fin m → Polynomial ℂ) (hp : LinearIndependent ℂ p)
    (hdeg : ∀ i, (p i).natDegree ≤ d) :
    ∃ q : Fin m → Polynomial ℂ, (∀ i, (q i).natDegree ≤ d) ∧
      Orthonormal ℂ (fun i => coefficientVector d (q i)) ∧
      LinearIndependent ℂ q ∧
      Submodule.span ℂ (Set.range q) = Submodule.span ℂ (Set.range p) := by
  sorry

/-- A nonzero bounded-degree polynomial has a nonzero coefficient vector. -/
theorem coefficientVector_ne_zero_of_natDegree_le {d : ℕ} (q : Polynomial ℂ)
    (hq : q ≠ 0) (hdeg : q.natDegree ≤ d) : coefficientVector d q ≠ 0 := by
  sorry

/-- Scalar normalization preserves the degree bound and complete root multiset. -/
theorem exists_polynomial_unit_coefficient_norm {d : ℕ} (q : Polynomial ℂ)
    (hq : q ≠ 0) (hdeg : q.natDegree ≤ d) :
    ∃ (c : ℂ) (r : Polynomial ℂ), c ≠ 0 ∧ r = c • q ∧
      r.natDegree ≤ d ∧ ‖coefficientVector d r‖ = 1 ∧ r.roots = q.roots := by
  sorry

/-- A member of the span of degree-bounded polynomials obeys the same bound. -/
theorem polynomial_natDegree_le_of_mem_span {m d : ℕ}
    (p : Fin m → Polynomial ℂ) (hdeg : ∀ i, (p i).natDegree ≤ d)
    {q : Polynomial ℂ} (hq : q ∈ Submodule.span ℂ (Set.range p)) : q.natDegree ≤ d := by
  sorry

end KungTraub
