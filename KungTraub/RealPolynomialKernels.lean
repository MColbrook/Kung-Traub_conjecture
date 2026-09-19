import KungTraub.RealComplexInformation
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
    (realPartPolynomial p).coeff k = (p.coeff k).re := rfl

@[simp] theorem imagPartPolynomial_coeff (p : Polynomial ℂ) (k : ℕ) :
    (imagPartPolynomial p).coeff k = (p.coeff k).im := rfl

theorem realPartPolynomial_natDegree_le (p : Polynomial ℂ) :
    (realPartPolynomial p).natDegree ≤ p.natDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  simp [Polynomial.coeff_eq_zero_of_natDegree_lt hk]

theorem imagPartPolynomial_natDegree_le (p : Polynomial ℂ) :
    (imagPartPolynomial p).natDegree ≤ p.natDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  simp [Polynomial.coeff_eq_zero_of_natDegree_lt hk]

theorem polynomial_real_im_decomposition (p : Polynomial ℂ) :
    p = (realPartPolynomial p).map (algebraMap ℝ ℂ) +
      Complex.I • (imagPartPolynomial p).map (algebraMap ℝ ℂ) := by
  ext k
  apply Complex.ext <;> simp [Polynomial.coeff_map, Polynomial.coeff_smul, Complex.mul_re, Complex.mul_im]

theorem polynomial_real_or_im_nonzero (p : Polynomial ℂ) (hp : p ≠ 0) :
    realPartPolynomial p ≠ 0 ∨ imagPartPolynomial p ≠ 0 := by
  by_contra! h
  apply hp
  rw [polynomial_real_im_decomposition p, h.1, h.2]
  simp

/-- The complex-linear extension determined by the real functional's monomial values. -/
def complexifyPolynomialFunctional (L : Polynomial ℝ →ₗ[ℝ] ℝ) : Polynomial ℂ →ₗ[ℂ] ℂ :=
  (Polynomial.basisMonomials ℂ).constr ℂ
    (fun k => (L (Polynomial.monomial k 1) : ℂ))

theorem complexifyPolynomialFunctional_monomial_one (L : Polynomial ℝ →ₗ[ℝ] ℝ) (k : ℕ) :
    complexifyPolynomialFunctional L (Polynomial.monomial k 1) =
      (L (Polynomial.monomial k 1) : ℂ) := by
  have h := (Polynomial.basisMonomials ℂ).constr_basis ℂ
    (fun k => (L (Polynomial.monomial k 1) : ℂ)) k
  simpa only [complexifyPolynomialFunctional, Polynomial.coe_basisMonomials] using h

theorem complexifyPolynomialFunctional_map_real (L : Polynomial ℝ →ₗ[ℝ] ℝ) (p : Polynomial ℝ) :
    complexifyPolynomialFunctional L (p.map (algebraMap ℝ ℂ)) = (L p : ℂ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.map_add, map_add, hp, hq, Complex.ofReal_add]
  | monomial k a =>
    have hc : (Polynomial.monomial k a).map (algebraMap ℝ ℂ) =
        (a : ℂ) • Polynomial.monomial k 1 := by
      simp [Polynomial.smul_monomial]
    have hr : Polynomial.monomial k a = a • Polynomial.monomial k (1 : ℝ) := by
      simp [Polynomial.smul_monomial]
    rw [hc, map_smul, complexifyPolynomialFunctional_monomial_one, hr, map_smul]
    simp

def complexifyPolynomialObservations (L : ℕ → Polynomial ℝ →ₗ[ℝ] ℝ) :
    ℕ → Polynomial ℂ →ₗ[ℂ] ℂ := fun i => complexifyPolynomialFunctional (L i)

theorem complexifyPolynomialFunctional_re (L : Polynomial ℝ →ₗ[ℝ] ℝ) (p : Polynomial ℂ) :
    (complexifyPolynomialFunctional L p).re = L (realPartPolynomial p) := by
  conv_lhs => rw [polynomial_real_im_decomposition p]
  rw [map_add, map_smul, complexifyPolynomialFunctional_map_real,
    complexifyPolynomialFunctional_map_real]
  simp [Complex.mul_re]

theorem complexifyPolynomialFunctional_im (L : Polynomial ℝ →ₗ[ℝ] ℝ) (p : Polynomial ℂ) :
    (complexifyPolynomialFunctional L p).im = L (imagPartPolynomial p) := by
  conv_lhs => rw [polynomial_real_im_decomposition p]
  rw [map_add, map_smul, complexifyPolynomialFunctional_map_real,
    complexifyPolynomialFunctional_map_real]
  simp [Complex.mul_im]

theorem realPartPolynomial_annihilated
    (L : ℕ → Polynomial ℝ →ₗ[ℝ] ℝ) (j : ℕ) (p : Polynomial ℂ)
    (hp : ∀ i < j, complexifyPolynomialObservations L i p = 0) :
    ∀ i < j, L i (realPartPolynomial p) = 0 := by
  intro i hi
  rw [← complexifyPolynomialFunctional_re]
  have h := congrArg Complex.re (hp i hi)
  exact h

theorem imagPartPolynomial_annihilated
    (L : ℕ → Polynomial ℝ →ₗ[ℝ] ℝ) (j : ℕ) (p : Polynomial ℂ)
    (hp : ∀ i < j, complexifyPolynomialObservations L i p = 0) :
    ∀ i < j, L i (imagPartPolynomial p) = 0 := by
  intro i hi
  rw [← complexifyPolynomialFunctional_im]
  have h := congrArg Complex.im (hp i hi)
  exact h

/-- A nonzero complex kernel polynomial has a nonzero real coefficient part
in the real kernel, of no larger degree. -/
theorem exists_real_kernel_polynomial_of_complex
    (L : ℕ → Polynomial ℝ →ₗ[ℝ] ℝ) (j : ℕ) (p : Polynomial ℂ) (hp : p ≠ 0)
    (hLp : ∀ i < j, complexifyPolynomialObservations L i p = 0) :
    ∃ q : Polynomial ℝ, q ≠ 0 ∧ q.natDegree ≤ p.natDegree ∧ ∀ i < j, L i q = 0 := by
  rcases polynomial_real_or_im_nonzero p hp with hre | him
  · exact ⟨realPartPolynomial p, hre, realPartPolynomial_natDegree_le p,
      realPartPolynomial_annihilated L j p hLp⟩
  · exact ⟨imagPartPolynomial p, him, imagPartPolynomial_natDegree_le p,
      imagPartPolynomial_annihilated L j p hLp⟩

theorem real_polynomial_map_natDegree (q : Polynomial ℝ) :
    (q.map (algebraMap ℝ ℂ)).natDegree = q.natDegree :=
  Polynomial.natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective q

theorem real_polynomial_map_ne_zero (q : Polynomial ℝ) (hq : q ≠ 0) :
    q.map (algebraMap ℝ ℂ) ≠ 0 := Polynomial.map_ne_zero hq

theorem real_polynomial_map_annihilated
    (L : ℕ → Polynomial ℝ →ₗ[ℝ] ℝ) (j : ℕ) (q : Polynomial ℝ)
    (hLq : ∀ i < j, L i q = 0) :
    ∀ i < j, complexifyPolynomialObservations L i (q.map (algebraMap ℝ ℂ)) = 0 := by
  intro i hi
  change complexifyPolynomialFunctional (L i) (q.map (algebraMap ℝ ℂ)) = 0
  rw [complexifyPolynomialFunctional_map_real, hLq i hi, Complex.ofReal_zero]

/-- Real minimum degree is also minimum degree among all complex kernel elements.
This applies to any scalar normalization of a real minimum-degree polynomial. -/
theorem real_minimum_degree_is_complex_minimum
    (L : ℕ → Polynomial ℝ →ₗ[ℝ] ℝ) (j : ℕ) (q : Polynomial ℝ)
    (hmin : ∀ r : Polynomial ℝ, r ≠ 0 → (∀ i < j, L i r = 0) →
      q.natDegree ≤ r.natDegree) :
    ∀ r : Polynomial ℂ, r ≠ 0 → (∀ i < j, complexifyPolynomialObservations L i r = 0) →
      (q.map (algebraMap ℝ ℂ)).natDegree ≤ r.natDegree := by
  intro r hr hLr
  obtain ⟨p, hp, hdeg, hLp⟩ := exists_real_kernel_polynomial_of_complex L j r hr hLr
  rw [real_polynomial_map_natDegree]
  exact (hmin p hp hLp).trans hdeg

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
  obtain ⟨q, hq, hdeg, hLq, hmin⟩ := exists_minimum_degree_kernel_polynomial L j
  exact ⟨q, hq, hdeg, hLq, hmin, real_polynomial_map_ne_zero q hq,
    real_polynomial_map_annihilated L j q hLq,
    real_minimum_degree_is_complex_minimum L j q hmin⟩

end KungTraub
