import KungTraubAppendices.ComplexAffineOracle
import KungTraub.PolynomialFrames

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
  change (polynomialOfCoefficients (complexConstantScaleMap n ε u)).coeff i.val = _
  simp [polynomialOfCoefficients_coeff, i.isLt, complexConstantScaleMap]

/-- The finite parameter space gives polynomials of degree at most n. -/
theorem complexParameterPolynomialMap_natDegree_le {n : ℕ} (ε : ℝ)
    (u : EuclideanSpace ℂ (Fin (n + 1))) :
    (complexParameterPolynomialMap n ε u).natDegree ≤ n :=
  polynomialOfCoefficients_natDegree_le _

/-- Scaling and inverse scaling cancel on every complex parameter vector. -/
theorem complexInverseCoefficientMap_parameterPolynomial {n : ℕ} {ε : ℝ} (hε : ε ≠ 0)
    (u : EuclideanSpace ℂ (Fin (n + 1))) :
    complexInverseCoefficientMap n ε (complexParameterPolynomialMap n ε u) = u := by
  have hεc : (ε : ℂ) ≠ 0 := by exact_mod_cast hε
  ext i
  change (if i = 0 then (complexParameterPolynomialMap n ε u).coeff i.val / (ε : ℂ)
    else (complexParameterPolynomialMap n ε u).coeff i.val) = u i
  rw [complexParameterPolynomialMap_coeff]
  by_cases hi : i = 0 <;> simp [hi, hεc]

/-- Reconstruction is exact on the full degree-at-most-n polynomial subspace. -/
theorem complexParameterPolynomialMap_inverseCoefficientMap {n : ℕ}
    (q : Polynomial ℂ) (hdegree : q.natDegree ≤ n) {ε : ℝ} (hε : ε ≠ 0) :
    complexParameterPolynomialMap n ε (complexInverseCoefficientMap n ε q) = q := by
  have hεc : (ε : ℂ) ≠ 0 := by exact_mod_cast hε
  have heq : complexConstantScaleMap n ε (complexInverseCoefficientMap n ε q) =
      coefficientVector n q := by
    ext i
    by_cases hi : i = 0 <;>
      simp [complexConstantScaleMap, complexInverseCoefficientMap, inverseConstantScale,
        coefficientVector, hi]
    field_simp
  change polynomialOfCoefficients _ = q
  rw [heq]
  exact polynomialOfCoefficients_coefficientVector q hdegree

/-- Extending a parameter row to polynomials and then restricting it returns that row. -/
theorem complex_polynomial_observation_recomposition {n : ℕ}
    (L : EuclideanSpace ℂ (Fin (n + 1)) →ₗ[ℂ] ℂ) {ε : ℝ} (hε : ε ≠ 0) :
    (L.comp (complexInverseCoefficientMap n ε)).comp (complexParameterPolynomialMap n ε) = L := by
  ext u
  exact congrArg L (complexInverseCoefficientMap_parameterPolynomial hε u)

/-- The unit direction obtained by normalizing the existing inverse-scaled coefficient vector. -/
def complexNormalizedPolynomialDirection {n : ℕ} (q : Polynomial ℂ) (ε : ℝ) :
    EuclideanSpace ℂ (Fin (n + 1)) :=
  (‖inverseConstantScale ε (coefficientVector n q)‖⁻¹ : ℂ) •
    inverseConstantScale ε (coefficientVector n q)

/-- A normalized coefficient polynomial supplies a complex unit direction. -/
theorem complexNormalizedPolynomialDirection_norm {n : ℕ} (q : Polynomial ℂ)
    (hnorm : ‖coefficientVector n q‖ = 1) {ε : ℝ} (hε : 0 < ε) :
    ‖complexNormalizedPolynomialDirection (n := n) q ε‖ = 1 := by
  have hp := inverseConstantScale_norm_pos hε (coefficientVector n q) hnorm
  simp only [complexNormalizedPolynomialDirection, norm_smul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_norm]
  exact inv_mul_cancel₀ hp.ne'

/-- The parameter direction reconstructs the same polynomial with only its norm normalization. -/
theorem complexNormalizedPolynomialDirection_polynomial {n : ℕ} (q : Polynomial ℂ)
    (hdegree : q.natDegree ≤ n) {ε : ℝ} (hε : 0 < ε) :
    complexParameterPolynomialMap n ε (complexNormalizedPolynomialDirection q ε) =
      (‖inverseConstantScale ε (coefficientVector n q)‖⁻¹ : ℂ) • q := by
  change complexParameterPolynomialMap n ε
    ((‖inverseConstantScale ε (coefficientVector n q)‖⁻¹ : ℂ) •
      complexInverseCoefficientMap n ε q) = _
  rw [map_smul, complexParameterPolynomialMap_inverseCoefficientMap q hdegree hε.ne']

/-- Complex polynomial kernel conditions give membership in the actual induced direction space. -/
theorem complexNormalizedPolynomialDirection_mem_kernel {n j : ℕ}
    (L : ℕ → Polynomial ℂ →ₗ[ℂ] ℂ) (q : Polynomial ℂ) (hdegree : q.natDegree ≤ n)
    (hLq : ∀ i < j, L i q = 0) {ε : ℝ} (hε : 0 < ε) :
    complexNormalizedPolynomialDirection q ε ∈
      scalarPrefixKernel (fun i => (L i).comp (complexParameterPolynomialMap n ε)) j := by
  rw [mem_scalarPrefixKernel]
  intro i hi
  change L i (complexParameterPolynomialMap n ε (complexNormalizedPolynomialDirection q ε)) = 0
  rw [complexNormalizedPolynomialDirection_polynomial q hdegree hε, map_smul,
    hLq i hi, smul_zero]

/-- The polynomial row induced by the observation actually selected by the complex rules. -/
def ComplexAffineAlgorithm.polynomialObservation {n budget : ℕ}
    (A : ComplexAffineAlgorithm (EuclideanSpace ℂ (Fin (n + 1))) budget)
    (u : EuclideanSpace ℂ (Fin (n + 1))) (x : ℂ) (ε : ℝ) (i : ℕ) : Polynomial ℂ →ₗ[ℂ] ℂ :=
  (A.actualLinearMap u x i).comp (complexInverseCoefficientMap n ε)

theorem ComplexAffineAlgorithm.polynomialObservation_apply {n budget : ℕ}
    (A : ComplexAffineAlgorithm (EuclideanSpace ℂ (Fin (n + 1))) budget)
    (u : EuclideanSpace ℂ (Fin (n + 1))) (x : ℂ) (ε : ℝ) (i : ℕ) (q : Polynomial ℂ) :
    A.polynomialObservation u x ε i q =
      A.actualLinearMap u x i (inverseConstantScale ε (coefficientVector n q)) := rfl

/-- Polynomial extension preserves the value of each observation row. -/
theorem ComplexAffineAlgorithm.polynomialObservation_parameterPolynomial {n budget : ℕ}
    (A : ComplexAffineAlgorithm (EuclideanSpace ℂ (Fin (n + 1))) budget)
    (u : EuclideanSpace ℂ (Fin (n + 1))) (x : ℂ) {ε : ℝ} (hε : ε ≠ 0) (i : ℕ) :
    (A.polynomialObservation u x ε i).comp (complexParameterPolynomialMap n ε) =
      A.actualLinearMap u x i :=
  complex_polynomial_observation_recomposition _ hε

/-- The actual complex transcript direction is exactly the induced polynomial kernel. -/
theorem ComplexAffineAlgorithm.direction_eq_polynomial_kernel {n budget : ℕ}
    (A : ComplexAffineAlgorithm (EuclideanSpace ℂ (Fin (n + 1))) budget)
    (u : EuclideanSpace ℂ (Fin (n + 1))) (x : ℂ) {ε : ℝ} (hε : ε ≠ 0) (j : ℕ) :
    A.direction u x j = scalarPrefixKernel
      (fun i => (A.polynomialObservation u x ε i).comp (complexParameterPolynomialMap n ε)) j := by
  unfold ComplexAffineAlgorithm.direction
  congr 1
  funext i
  exact (A.polynomialObservation_parameterPolynomial u x hε i).symm

/-- Equal prefixes preserve all polynomial rows up to and including the next selected query. -/
theorem ComplexAffineAlgorithm.polynomialObservation_eq_of_prefix_eq {n budget : ℕ}
    (A : ComplexAffineAlgorithm (EuclideanSpace ℂ (Fin (n + 1))) budget)
    {u v : EuclideanSpace ℂ (Fin (n + 1))} {x : ℂ} {ε : ℝ} {j i : ℕ}
    (hj : j < budget) (hi : i ≤ j)
    (heq : A.prefix v x j (Nat.le_of_lt hj) = A.prefix u x j (Nat.le_of_lt hj)) :
    A.polynomialObservation v x ε i = A.polynomialObservation u x ε i := by
  unfold polynomialObservation
  rw [A.actualLinearMap_eq_of_prefix_eq (hi.trans_lt hj)
    (A.prefix_eq_of_later_prefix_eq hi (Nat.le_of_lt hj) heq)]

/-- A polynomial in all actual row kernels supplies a direction preserving the prefix. -/
theorem ComplexAffineAlgorithm.normalized_polynomial_direction_mem {n budget j : ℕ}
    (A : ComplexAffineAlgorithm (EuclideanSpace ℂ (Fin (n + 1))) budget)
    (u : EuclideanSpace ℂ (Fin (n + 1))) (x : ℂ) (q : Polynomial ℂ)
    (hdegree : q.natDegree ≤ n) {ε : ℝ} (hε : 0 < ε)
    (hLq : ∀ i < j, A.polynomialObservation u x ε i q = 0) :
    complexNormalizedPolynomialDirection q ε ∈ A.direction u x j := by
  rw [A.direction_eq_polynomial_kernel u x hε.ne' j]
  exact complexNormalizedPolynomialDirection_mem_kernel _ q hdegree hLq hε

end KungTraubAppendices
