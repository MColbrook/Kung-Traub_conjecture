import appendix_b_reference.KungTraubAppendices.ComplexAffineOracle
import appendix_b_reference.KungTraub.PolynomialFrames

/-!
# Complex polynomial rows of an affine execution

The real scale ε multiplies the constant coefficient. Coefficient extraction,
inverse scaling and bounded-degree reconstruction use `KungTraub.Coefficients`
and `KungTraub.PolynomialFrames`. The affine-row arguments follow
`KungTraub.AffinePolynomialInformation` over complex parameter spaces.

The rows are selected during the execution. Their common polynomial kernel
gives directions preserving the transcript. Reconstruction requires the degree
bound and a nonzero scale.
-/

noncomputable section

open KungTraub

namespace KungTraubAppendices

/-- Scale the constant coordinate and leave every positive-degree coefficient fixed. -/
def complexConstantScaleMap (n : ℕ) (ε : ℝ) :
    EuclideanSpace ℂ (Fin (n + 1)) →ₗ[ℂ] EuclideanSpace ℂ (Fin (n + 1)) where
  toFun u := WithLp.toLp 2 (fun i => if i = 0 then (ε : ℂ) * u i else u i)
  map_add' u v := by ext i; by_cases hi : i = 0 <;> simp [hi, mul_add]
  map_smul' c u := by ext i; by_cases hi : i = 0 <;> simp [hi, mul_left_comm]

/-- The actual complex parameter polynomial in the centered variable. -/
def complexParameterPolynomialMap (n : ℕ) (ε : ℝ) :
    EuclideanSpace ℂ (Fin (n + 1)) →ₗ[ℂ] Polynomial ℂ :=
  (polynomialOfCoefficientsLinearMap n).comp (complexConstantScaleMap n ε)

/-- Inverse coefficient scaling, extended to all polynomials by truncation after degree n. -/
def complexInverseCoefficientMap (n : ℕ) (ε : ℝ) :
    Polynomial ℂ →ₗ[ℂ] EuclideanSpace ℂ (Fin (n + 1)) where
  toFun q := inverseConstantScale ε (coefficientVector n q)
  map_add' q p := by
    ext i
    by_cases hi : i = 0 <;> simp [inverseConstantScale, coefficientVector, hi, add_div]
  map_smul' c q := by
    ext i
    by_cases hi : i = 0 <;>
      simp [inverseConstantScale, coefficientVector, hi, mul_div_assoc]

/-- Coefficient extraction gives exactly the scaled parameter, including degree zero. -/
theorem complexParameterPolynomialMap_coeff {n : ℕ} (ε : ℝ)
    (u : EuclideanSpace ℂ (Fin (n + 1))) (i : Fin (n + 1)) :
    (complexParameterPolynomialMap n ε u).coeff i.val =
      if i = 0 then (ε : ℂ) * u i else u i := by
  sorry

/-- The finite parameter space gives polynomials of degree at most n. -/
theorem complexParameterPolynomialMap_natDegree_le {n : ℕ} (ε : ℝ)
    (u : EuclideanSpace ℂ (Fin (n + 1))) :
    (complexParameterPolynomialMap n ε u).natDegree ≤ n := by
  sorry

/-- Scaling and inverse scaling cancel on every complex parameter vector. -/
theorem complexInverseCoefficientMap_parameterPolynomial {n : ℕ} {ε : ℝ} (hε : ε ≠ 0)
    (u : EuclideanSpace ℂ (Fin (n + 1))) :
    complexInverseCoefficientMap n ε (complexParameterPolynomialMap n ε u) = u := by
  sorry

/-- Reconstruction is exact on the full degree-at-most-n polynomial subspace. -/
theorem complexParameterPolynomialMap_inverseCoefficientMap {n : ℕ}
    (q : Polynomial ℂ) (hdegree : q.natDegree ≤ n) {ε : ℝ} (hε : ε ≠ 0) :
    complexParameterPolynomialMap n ε (complexInverseCoefficientMap n ε q) = q := by
  sorry

/-- Extending a parameter row to polynomials and then restricting it returns that row. -/
theorem complex_polynomial_observation_recomposition {n : ℕ}
    (L : EuclideanSpace ℂ (Fin (n + 1)) →ₗ[ℂ] ℂ) {ε : ℝ} (hε : ε ≠ 0) :
    (L.comp (complexInverseCoefficientMap n ε)).comp (complexParameterPolynomialMap n ε) = L := by
  sorry

/-- The unit direction obtained by normalizing the existing inverse-scaled coefficient vector. -/
def complexNormalizedPolynomialDirection {n : ℕ} (q : Polynomial ℂ) (ε : ℝ) :
    EuclideanSpace ℂ (Fin (n + 1)) :=
  (‖inverseConstantScale ε (coefficientVector n q)‖⁻¹ : ℂ) •
    inverseConstantScale ε (coefficientVector n q)

/-- A normalized coefficient polynomial supplies a complex unit direction. -/
theorem complexNormalizedPolynomialDirection_norm {n : ℕ} (q : Polynomial ℂ)
    (hnorm : ‖coefficientVector n q‖ = 1) {ε : ℝ} (hε : 0 < ε) :
    ‖complexNormalizedPolynomialDirection (n := n) q ε‖ = 1 := by
  sorry

/-- The parameter direction reconstructs the same polynomial with only its norm normalization. -/
theorem complexNormalizedPolynomialDirection_polynomial {n : ℕ} (q : Polynomial ℂ)
    (hdegree : q.natDegree ≤ n) {ε : ℝ} (hε : 0 < ε) :
    complexParameterPolynomialMap n ε (complexNormalizedPolynomialDirection q ε) =
      (‖inverseConstantScale ε (coefficientVector n q)‖⁻¹ : ℂ) • q := by
  sorry

/-- Complex polynomial kernel conditions give membership in the actual induced direction space. -/
theorem complexNormalizedPolynomialDirection_mem_kernel {n j : ℕ}
    (L : ℕ → Polynomial ℂ →ₗ[ℂ] ℂ) (q : Polynomial ℂ) (hdegree : q.natDegree ≤ n)
    (hLq : ∀ i < j, L i q = 0) {ε : ℝ} (hε : 0 < ε) :
    complexNormalizedPolynomialDirection q ε ∈
      scalarPrefixKernel (fun i => (L i).comp (complexParameterPolynomialMap n ε)) j := by
  sorry

/-- The polynomial row induced by the observation actually selected by the complex rules. -/
def ComplexAffineAlgorithm.polynomialObservation {n budget : ℕ}
    (A : ComplexAffineAlgorithm (EuclideanSpace ℂ (Fin (n + 1))) budget)
    (u : EuclideanSpace ℂ (Fin (n + 1))) (x : ℂ) (ε : ℝ) (i : ℕ) : Polynomial ℂ →ₗ[ℂ] ℂ :=
  (A.actualLinearMap u x i).comp (complexInverseCoefficientMap n ε)

theorem ComplexAffineAlgorithm.polynomialObservation_apply {n budget : ℕ}
    (A : ComplexAffineAlgorithm (EuclideanSpace ℂ (Fin (n + 1))) budget)
    (u : EuclideanSpace ℂ (Fin (n + 1))) (x : ℂ) (ε : ℝ) (i : ℕ) (q : Polynomial ℂ) :
    A.polynomialObservation u x ε i q =
      A.actualLinearMap u x i (inverseConstantScale ε (coefficientVector n q)) := by
  sorry

/-- Polynomial extension preserves the value of each observation row. -/
theorem ComplexAffineAlgorithm.polynomialObservation_parameterPolynomial {n budget : ℕ}
    (A : ComplexAffineAlgorithm (EuclideanSpace ℂ (Fin (n + 1))) budget)
    (u : EuclideanSpace ℂ (Fin (n + 1))) (x : ℂ) {ε : ℝ} (hε : ε ≠ 0) (i : ℕ) :
    (A.polynomialObservation u x ε i).comp (complexParameterPolynomialMap n ε) =
      A.actualLinearMap u x i := by
  sorry

/-- The actual complex transcript direction is exactly the induced polynomial kernel. -/
theorem ComplexAffineAlgorithm.direction_eq_polynomial_kernel {n budget : ℕ}
    (A : ComplexAffineAlgorithm (EuclideanSpace ℂ (Fin (n + 1))) budget)
    (u : EuclideanSpace ℂ (Fin (n + 1))) (x : ℂ) {ε : ℝ} (hε : ε ≠ 0) (j : ℕ) :
    A.direction u x j = scalarPrefixKernel
      (fun i => (A.polynomialObservation u x ε i).comp (complexParameterPolynomialMap n ε)) j := by
  sorry

/-- Equal prefixes preserve all polynomial rows up to and including the next selected query. -/
theorem ComplexAffineAlgorithm.polynomialObservation_eq_of_prefix_eq {n budget : ℕ}
    (A : ComplexAffineAlgorithm (EuclideanSpace ℂ (Fin (n + 1))) budget)
    {u v : EuclideanSpace ℂ (Fin (n + 1))} {x : ℂ} {ε : ℝ} {j i : ℕ}
    (hj : j < budget) (hi : i ≤ j)
    (heq : A.prefix v x j (Nat.le_of_lt hj) = A.prefix u x j (Nat.le_of_lt hj)) :
    A.polynomialObservation v x ε i = A.polynomialObservation u x ε i := by
  sorry

/-- A polynomial in all actual row kernels supplies a direction preserving the prefix. -/
theorem ComplexAffineAlgorithm.normalized_polynomial_direction_mem {n budget j : ℕ}
    (A : ComplexAffineAlgorithm (EuclideanSpace ℂ (Fin (n + 1))) budget)
    (u : EuclideanSpace ℂ (Fin (n + 1))) (x : ℂ) (q : Polynomial ℂ)
    (hdegree : q.natDegree ≤ n) {ε : ℝ} (hε : 0 < ε)
    (hLq : ∀ i < j, A.polynomialObservation u x ε i q = 0) :
    complexNormalizedPolynomialDirection q ε ∈ A.direction u x j := by
  sorry

end KungTraubAppendices
