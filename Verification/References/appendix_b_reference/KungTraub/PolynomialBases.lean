import appendix_b_reference.KungTraub.PolynomialWronskians
import Mathlib.RingTheory.Polynomial.DegreeLT

/-!
# Degree-adapted polynomial families

The degree reduction follows the manuscript's cancellation of equal leading degrees.
The elementary column operations, finite-set ordering and dimension APIs are from mathlib.
-/

noncomputable section
namespace KungTraub
open scoped BigOperators

/-- An independent finite family admits another family with the same span and Wronskian,
pairwise distinct degrees, and no increase in any labelled degree. -/
theorem exists_polynomial_family_distinct_degrees {m : ℕ}
    (p : Fin m → Polynomial ℂ) (hp : LinearIndependent ℂ p) :
    ∃ q : Fin m → Polynomial ℂ, LinearIndependent ℂ q ∧
      Function.Injective (fun i => (q i).natDegree) ∧
      Submodule.span ℂ (Set.range q) = Submodule.span ℂ (Set.range p) ∧
      polynomialWronskian q = polynomialWronskian p ∧
      (∀ i, (q i).natDegree ≤ (p i).natDegree) := by
  sorry


/-- Among `m` distinct natural numbers the minimum sum is `0 + ... + (m-1)`;
equality forces all numbers to be less than `m`. -/
theorem injective_nat_sum_minimum {m : ℕ} (d : Fin m → ℕ)
    (hd : Function.Injective d) :
    (∑ i : Fin m, i.val) ≤ ∑ i, d i ∧
      ((∑ i, d i) = ∑ i : Fin m, i.val → ∀ i, d i < m) := by
  sorry

/-- The sharp upper bound for the degree of a nonempty polynomial Wronskian. -/
theorem polynomialWronskian_natDegree_le {m D : ℕ} (hm : 0 < m) (hmD : m ≤ D + 1)
    (p : Fin m → Polynomial ℂ) (hp : LinearIndependent ℂ p)
    (hD : ∀ i, (p i).natDegree ≤ D) :
    (polynomialWronskian p).natDegree ≤ m * (D + 1 - m) := by
  sorry

/-- A constant Wronskian characterizes the full space of polynomials of degree less than `m`. -/
theorem polynomialWronskian_natDegree_eq_zero_iff_span {m : ℕ}
    (p : Fin m → Polynomial ℂ) (hp : LinearIndependent ℂ p) :
    (polynomialWronskian p).natDegree = 0 ↔
      Submodule.span ℂ (Set.range p) = Polynomial.degreeLT ℂ m := by
  sorry

/-- The constant Wronskian in the characterization is nonzero. -/
theorem polynomialWronskian_eq_nonzero_constant_iff_span {m : ℕ}
    (p : Fin m → Polynomial ℂ) (hp : LinearIndependent ℂ p) :
    (∃ c : ℂ, c ≠ 0 ∧ polynomialWronskian p = Polynomial.C c) ↔
      Submodule.span ℂ (Set.range p) = Polynomial.degreeLT ℂ m := by
  sorry

/-- A basis can be chosen with pairwise distinct polynomial degrees. -/
theorem exists_polynomial_basis_distinct_degrees {m : ℕ}
    (V : Submodule ℂ (Polynomial ℂ)) (b : Module.Basis (Fin m) ℂ V) :
    ∃ b' : Module.Basis (Fin m) ℂ V,
      Function.Injective (fun i => (b' i : Polynomial ℂ).natDegree) := by
  sorry

/-- Outside the full space of degree less than `m`, an independent family's Wronskian has a root. -/
theorem polynomialWronskian_has_root_iff_span_ne_degreeLT {m : ℕ}
    (p : Fin m → Polynomial ℂ) (hp : LinearIndependent ℂ p) :
    (∃ a : ℂ, (polynomialWronskian p).eval a = 0) ↔
      Submodule.span ℂ (Set.range p) ≠ Polynomial.degreeLT ℂ m := by
  sorry

end KungTraub

