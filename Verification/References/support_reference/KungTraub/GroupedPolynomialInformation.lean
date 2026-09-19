import support_reference.KungTraub.AffinePolynomialInformation
import support_reference.KungTraub.GroupedAffineTranscripts

/-!
# Polynomial observations of an actual grouped execution

Every actual scalar row induces a polynomial functional through the same
inverse constant-coordinate scaling as in the scalar model. The common kernel
at a complete group prefix is exactly the grouped transcript direction.
-/

noncomputable section
namespace KungTraub

def GroupedAffineAlgorithm.polynomialObservation {n k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) sizes)
    (u : EuclideanSpace ℝ (Fin (n + 1))) (x ε : ℝ) (t : ℕ) : Polynomial ℝ →ₗ[ℝ] ℝ :=
  (A.actualLinearMap u x t).comp (realInverseCoefficientMap n ε)

theorem GroupedAffineAlgorithm.polynomialObservation_apply {n k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) sizes)
    (u : EuclideanSpace ℝ (Fin (n + 1))) (x ε : ℝ) (t : ℕ) (q : Polynomial ℝ) :
    A.polynomialObservation u x ε t q =
      A.actualLinearMap u x t (realInverseConstantScale ε (realCoefficientVector n q)) := by
  sorry

theorem GroupedAffineAlgorithm.polynomialObservation_parameterPolynomial
    {n k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) sizes)
    (u : EuclideanSpace ℝ (Fin (n + 1))) (x : ℝ) {ε : ℝ} (hε : ε ≠ 0) (t : ℕ) :
    (A.polynomialObservation u x ε t).comp (realParameterPolynomialMap n ε) =
      A.actualLinearMap u x t := by
  sorry

theorem GroupedAffineAlgorithm.direction_eq_polynomial_kernel {n k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) sizes)
    (u : EuclideanSpace ℝ (Fin (n + 1))) (x : ℝ) {ε : ℝ} (hε : ε ≠ 0) (j : ℕ) :
    A.direction u x j = scalarPrefixKernel
      (fun t => (A.polynomialObservation u x ε t).comp (realParameterPolynomialMap n ε))
      (groupedPrefixCount sizes j) := by
  sorry

theorem GroupedAffineAlgorithm.polynomialObservation_eq_of_prefix_eq
    {n k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) sizes)
    {u v : EuclideanSpace ℝ (Fin (n + 1))} {x ε : ℝ} {j t : ℕ} (hj : j ≤ k)
    (ht : t < groupedObservationCount sizes) (hgroup : scalarGroupAt sizes t ≤ j)
    (heq : A.prefix v x j hj = A.prefix u x j hj) :
    A.polynomialObservation v x ε t = A.polynomialObservation u x ε t := by
  sorry

theorem GroupedAffineAlgorithm.normalized_polynomial_direction_mem
    {n k j : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) sizes)
    (u : EuclideanSpace ℝ (Fin (n + 1))) (x : ℝ) (q : Polynomial ℝ)
    (hdegree : q.natDegree ≤ n) {ε : ℝ} (hε : 0 < ε)
    (hLq : ∀ t < groupedPrefixCount sizes j, A.polynomialObservation u x ε t q = 0) :
    realNormalizedPolynomialDirection q ε ∈ A.direction u x j := by
  sorry

end KungTraub
