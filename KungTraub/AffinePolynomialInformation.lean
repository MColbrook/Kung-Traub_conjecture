import KungTraub.AffineTranscripts
import KungTraub.PolynomialDirections

/-!
# Polynomial observations induced by an actual adaptive execution

An affine observation on the real parameter space induces a real linear
functional on polynomials by inverse scaling of the constant coefficient.
For nonzero scale, composition with the parameter polynomial is exactly the
original observation. Thus the common polynomial kernel supplies directions
in the actual adaptive transcript fibre.

Coefficients above the parameter degree are ignored by this extension. All
uses of reconstruction retain the degree bound explicitly. The finite-scale
argument needs only these restrictions, so arbitrary real affine observations
are covered without a continuity assumption.
-/

noncomputable section

namespace KungTraub

def realInverseCoefficientMap (n : ℕ) (ε : ℝ) :
    Polynomial ℝ →ₗ[ℝ] EuclideanSpace ℝ (Fin (n + 1)) where
  toFun q := realInverseConstantScale ε (realCoefficientVector n q)
  map_add' q p := by
    ext i
    by_cases hi : i = 0 <;>
      simp [realInverseConstantScale, realCoefficientVector, hi, add_div]
  map_smul' c q := by
    ext i
    by_cases hi : i = 0 <;>
      simp [realInverseConstantScale, realCoefficientVector, hi, mul_div_assoc]

theorem realInverseCoefficientMap_parameterPolynomial {n : ℕ} {ε : ℝ} (hε : ε ≠ 0)
    (u : EuclideanSpace ℝ (Fin (n + 1))) :
    realInverseCoefficientMap n ε (realParameterPolynomialMap n ε u) = u := by
  have hcoeff := Polynomial.toFn_comp_ofFn_eq_id (n + 1) (realConstantScaleMap n ε u)
  ext i
  have hi := congrFun hcoeff i
  change (Polynomial.ofFn (n + 1) (realConstantScaleMap n ε u)).coeff i.val =
    (realConstantScaleMap n ε u) i at hi
  change (if i = 0 then
      (Polynomial.ofFn (n + 1) (realConstantScaleMap n ε u)).coeff i.val / ε
    else (Polynomial.ofFn (n + 1) (realConstantScaleMap n ε u)).coeff i.val) = u i
  rw [hi]
  by_cases hi0 : i = 0 <;> simp [realConstantScaleMap, hi0, hε]

theorem realParameterPolynomialMap_inverseCoefficientMap {n : ℕ}
    (q : Polynomial ℝ) (hdegree : q.natDegree ≤ n) {ε : ℝ} (hε : ε ≠ 0) :
    realParameterPolynomialMap n ε (realInverseCoefficientMap n ε q) = q :=
  realParameterPolynomialMap_inverse_coefficients q hdegree hε

theorem polynomial_observation_recomposition {n : ℕ}
    (L : EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] ℝ) {ε : ℝ} (hε : ε ≠ 0) :
    (L.comp (realInverseCoefficientMap n ε)).comp (realParameterPolynomialMap n ε) = L := by
  ext u
  exact congrArg L (realInverseCoefficientMap_parameterPolynomial hε u)

def AffineAlgorithm.polynomialObservation {n budget : ℕ}
    (A : AffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) budget)
    (u : EuclideanSpace ℝ (Fin (n + 1))) (x ε : ℝ) (i : ℕ) : Polynomial ℝ →ₗ[ℝ] ℝ :=
  (A.actualLinearMap u x i).comp (realInverseCoefficientMap n ε)

theorem AffineAlgorithm.polynomialObservation_apply {n budget : ℕ}
    (A : AffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) budget)
    (u : EuclideanSpace ℝ (Fin (n + 1))) (x ε : ℝ) (i : ℕ) (q : Polynomial ℝ) :
    A.polynomialObservation u x ε i q =
      A.actualLinearMap u x i (realInverseConstantScale ε (realCoefficientVector n q)) := rfl

theorem AffineAlgorithm.polynomialObservation_parameterPolynomial {n budget : ℕ}
    (A : AffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) budget)
    (u : EuclideanSpace ℝ (Fin (n + 1))) (x : ℝ) {ε : ℝ} (hε : ε ≠ 0) (i : ℕ) :
    (A.polynomialObservation u x ε i).comp (realParameterPolynomialMap n ε) =
      A.actualLinearMap u x i :=
  polynomial_observation_recomposition _ hε

theorem AffineAlgorithm.direction_eq_polynomial_kernel {n budget : ℕ}
    (A : AffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) budget)
    (u : EuclideanSpace ℝ (Fin (n + 1))) (x : ℝ) {ε : ℝ} (hε : ε ≠ 0) (j : ℕ) :
    A.direction u x j = scalarPrefixKernel
      (fun i => (A.polynomialObservation u x ε i).comp (realParameterPolynomialMap n ε)) j := by
  unfold AffineAlgorithm.direction
  congr 1
  funext i
  exact (A.polynomialObservation_parameterPolynomial u x hε i).symm

theorem AffineAlgorithm.polynomialObservation_eq_of_prefix_eq {n budget : ℕ}
    (A : AffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) budget)
    {u v : EuclideanSpace ℝ (Fin (n + 1))} {x ε : ℝ} {j i : ℕ}
    (hj : j < budget) (hi : i ≤ j)
    (heq : A.prefix v x j (Nat.le_of_lt hj) = A.prefix u x j (Nat.le_of_lt hj)) :
    A.polynomialObservation v x ε i = A.polynomialObservation u x ε i := by
  unfold polynomialObservation
  rw [A.actualLinearMap_eq_of_prefix_eq (hi.trans_lt hj)
    (A.prefix_eq_of_later_prefix_eq hi (Nat.le_of_lt hj) heq)]

theorem AffineAlgorithm.normalized_polynomial_direction_mem {n budget j : ℕ}
    (A : AffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) budget)
    (u : EuclideanSpace ℝ (Fin (n + 1))) (x : ℝ) (q : Polynomial ℝ)
    (hdegree : q.natDegree ≤ n) {ε : ℝ} (hε : 0 < ε)
    (hLq : ∀ i < j, A.polynomialObservation u x ε i q = 0) :
    realNormalizedPolynomialDirection q ε ∈ A.direction u x j := by
  rw [A.direction_eq_polynomial_kernel u x hε.ne' j]
  exact realNormalizedPolynomialDirection_mem_kernel _ q hdegree hLq hε

theorem AffineAlgorithm.projected_sensitivity_of_polynomial_value {n budget j : ℕ}
    (A : AffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) budget)
    (u : EuclideanSpace ℝ (Fin (n + 1))) (x : ℝ)
    (q : Polynomial ℝ) (hdegree : q.natDegree ≤ n) (hnorm : ‖realCoefficientVector n q‖ = 1)
    (γ : ℕ → ℝ) (hγ : ∀ i < j, 0 < γ i)
    {ε R wmin w s : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 < R)
    (hwmin : 0 < wmin) (hw : wmin ≤ |w|)
    (hs : |s| ≤ R * ε) (hhalf : R * ε ≤ 1 / 2)
    (hLq : ∀ i < j, A.polynomialObservation u x ε i q = 0)
    (hvalue : sensitivityPolynomialConstant n γ j * ε ^ orderBound j ≤ |q.eval s|) :
    (wmin * sensitivityPolynomialConstant n γ j / (2 * R + 2)) * ε ^ orderBound j ≤
      ‖(A.direction u x j).starProjection (realPolynomialEvaluationVector n ε w s)‖ := by
  rw [A.direction_eq_polynomial_kernel u x hε.ne' j]
  exact real_polynomial_kernel_projected_sensitivity_lower_bound _ q hdegree hnorm hLq
    γ hγ hε hε1 hR hwmin hw hs hhalf hvalue

end KungTraub
