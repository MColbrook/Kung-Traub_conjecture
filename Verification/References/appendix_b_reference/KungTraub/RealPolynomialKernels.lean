import appendix_b_reference.KungTraub.RealComplexInformation
import Mathlib.Algebra.Polynomial.Basis

/-!
# Real kernel polynomials and complexification

The real and imaginary coefficient parts reduce a nonzero complex kernel element
to a nonzero real kernel element of no larger degree. This proves the minimum-degree
compatibility needed to use complex Wronskians with real parameter directions.
Complexification is an actual linear map constructed on the monomial basis.
-/

noncomputable section
namespace KungTraub
open scoped BigOperators

def realPartPolynomial (p : Polynomial ℂ) : Polynomial ℝ :=
  Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff
    (Finsupp.mapRange Complex.re (by simp) p.toFinsupp.coeff))

def imagPartPolynomial (p : Polynomial ℂ) : Polynomial ℝ :=
  Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff
    (Finsupp.mapRange Complex.im (by simp) p.toFinsupp.coeff))

@[simp] theorem realPartPolynomial_coeff (p : Polynomial ℂ) (k : ℕ) :
    (realPartPolynomial p).coeff k = (p.coeff k).re := by
  sorry

@[simp] theorem imagPartPolynomial_coeff (p : Polynomial ℂ) (k : ℕ) :
    (imagPartPolynomial p).coeff k = (p.coeff k).im := by
  sorry

theorem realPartPolynomial_natDegree_le (p : Polynomial ℂ) :
    (realPartPolynomial p).natDegree ≤ p.natDegree := by
  sorry

theorem imagPartPolynomial_natDegree_le (p : Polynomial ℂ) :
    (imagPartPolynomial p).natDegree ≤ p.natDegree := by
  sorry

theorem polynomial_real_im_decomposition (p : Polynomial ℂ) :
    p = (realPartPolynomial p).map (algebraMap ℝ ℂ) +
      Complex.I • (imagPartPolynomial p).map (algebraMap ℝ ℂ) := by
  sorry

theorem polynomial_real_or_im_nonzero (p : Polynomial ℂ) (hp : p ≠ 0) :
    realPartPolynomial p ≠ 0 ∨ imagPartPolynomial p ≠ 0 := by
  sorry

/-- The complex-linear extension determined by the real functional's monomial values. -/
def complexifyPolynomialFunctional (L : Polynomial ℝ →ₗ[ℝ] ℝ) : Polynomial ℂ →ₗ[ℂ] ℂ :=
  (Polynomial.basisMonomials ℂ).constr ℂ
    (fun k => (L (Polynomial.monomial k 1) : ℂ))

theorem complexifyPolynomialFunctional_monomial_one (L : Polynomial ℝ →ₗ[ℝ] ℝ) (k : ℕ) :
    complexifyPolynomialFunctional L (Polynomial.monomial k 1) =
      (L (Polynomial.monomial k 1) : ℂ) := by
  sorry

theorem complexifyPolynomialFunctional_map_real (L : Polynomial ℝ →ₗ[ℝ] ℝ) (p : Polynomial ℝ) :
    complexifyPolynomialFunctional L (p.map (algebraMap ℝ ℂ)) = (L p : ℂ) := by
  sorry

def complexifyPolynomialObservations (L : ℕ → Polynomial ℝ →ₗ[ℝ] ℝ) :
    ℕ → Polynomial ℂ →ₗ[ℂ] ℂ := fun i => complexifyPolynomialFunctional (L i)

theorem complexifyPolynomialFunctional_re (L : Polynomial ℝ →ₗ[ℝ] ℝ) (p : Polynomial ℂ) :
    (complexifyPolynomialFunctional L p).re = L (realPartPolynomial p) := by
  sorry

theorem complexifyPolynomialFunctional_im (L : Polynomial ℝ →ₗ[ℝ] ℝ) (p : Polynomial ℂ) :
    (complexifyPolynomialFunctional L p).im = L (imagPartPolynomial p) := by
  sorry

theorem realPartPolynomial_annihilated
    (L : ℕ → Polynomial ℝ →ₗ[ℝ] ℝ) (j : ℕ) (p : Polynomial ℂ)
    (hp : ∀ i < j, complexifyPolynomialObservations L i p = 0) :
    ∀ i < j, L i (realPartPolynomial p) = 0 := by
  sorry

theorem imagPartPolynomial_annihilated
    (L : ℕ → Polynomial ℝ →ₗ[ℝ] ℝ) (j : ℕ) (p : Polynomial ℂ)
    (hp : ∀ i < j, complexifyPolynomialObservations L i p = 0) :
    ∀ i < j, L i (imagPartPolynomial p) = 0 := by
  sorry

/-- A nonzero complex kernel polynomial has a nonzero real coefficient part
in the real kernel, of no larger degree. -/
theorem exists_real_kernel_polynomial_of_complex
    (L : ℕ → Polynomial ℝ →ₗ[ℝ] ℝ) (j : ℕ) (p : Polynomial ℂ) (hp : p ≠ 0)
    (hLp : ∀ i < j, complexifyPolynomialObservations L i p = 0) :
    ∃ q : Polynomial ℝ, q ≠ 0 ∧ q.natDegree ≤ p.natDegree ∧ ∀ i < j, L i q = 0 := by
  sorry

theorem real_polynomial_map_natDegree (q : Polynomial ℝ) :
    (q.map (algebraMap ℝ ℂ)).natDegree = q.natDegree := by
  sorry

theorem real_polynomial_map_ne_zero (q : Polynomial ℝ) (hq : q ≠ 0) :
    q.map (algebraMap ℝ ℂ) ≠ 0 := by
  sorry

theorem real_polynomial_map_annihilated
    (L : ℕ → Polynomial ℝ →ₗ[ℝ] ℝ) (j : ℕ) (q : Polynomial ℝ)
    (hLq : ∀ i < j, L i q = 0) :
    ∀ i < j, complexifyPolynomialObservations L i (q.map (algebraMap ℝ ℂ)) = 0 := by
  sorry

/-- Real minimum degree is also minimum degree among all complex kernel elements.
This applies to any scalar normalization of a real minimum-degree polynomial. -/
theorem real_minimum_degree_is_complex_minimum
    (L : ℕ → Polynomial ℝ →ₗ[ℝ] ℝ) (j : ℕ) (q : Polynomial ℝ)
    (hmin : ∀ r : Polynomial ℝ, r ≠ 0 → (∀ i < j, L i r = 0) →
      q.natDegree ≤ r.natDegree) :
    ∀ r : Polynomial ℂ, r ≠ 0 → (∀ i < j, complexifyPolynomialObservations L i r = 0) →
      (q.map (algebraMap ℝ ℂ)).natDegree ≤ r.natDegree := by
  sorry

/-- The minimum-degree real polynomial exists with `d ≤ j` and remains minimal
in the actual complexified common kernel. -/
theorem exists_real_minimum_degree_complex_kernel_polynomial
    (L : ℕ → Polynomial ℝ →ₗ[ℝ] ℝ) (j : ℕ) :
    ∃ q : Polynomial ℝ, q ≠ 0 ∧ q.natDegree ≤ j ∧
      (∀ i < j, L i q = 0) ∧
      (∀ r : Polynomial ℝ, r ≠ 0 → (∀ i < j, L i r = 0) → q.natDegree ≤ r.natDegree) ∧
      (q.map (algebraMap ℝ ℂ) ≠ 0) ∧
      (∀ i < j, complexifyPolynomialObservations L i (q.map (algebraMap ℝ ℂ)) = 0) ∧
      ∀ r : Polynomial ℂ, r ≠ 0 → (∀ i < j, complexifyPolynomialObservations L i r = 0) →
        (q.map (algebraMap ℝ ℂ)).natDegree ≤ r.natDegree := by
  sorry

end KungTraub
