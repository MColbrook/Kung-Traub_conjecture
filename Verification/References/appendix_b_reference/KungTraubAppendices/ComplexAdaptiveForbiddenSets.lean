import appendix_b_reference.KungTraubAppendices.ComplexPolynomialInformation
import appendix_b_reference.KungTraubAppendices.ComplexParameterBalls
import appendix_b_reference.KungTraub.ForbiddenWronskians

/-!
# Forbidden sets determined before a complex adaptive answer

Adapted from `KungTraub.AdaptiveForbiddenSets`, using complex polynomial
rows. The first i answers determine the row and location of query i,
and hence all of its forbidden set. The Wronskian cardinality estimate is reused
from `KungTraub.ForbiddenWronskians`. Adaptive rules may be arbitrary.
-/
noncomputable section
namespace KungTraubAppendices
open KungTraub

def ComplexAffineAlgorithm.queryLocation {n : ℕ}
    (A : ComplexAffineAlgorithm (EuclideanSpace ℂ (Fin (n + 1))) n)
    (u : EuclideanSpace ℂ (Fin (n + 1))) (x : ℂ) (i : ℕ) : Option ℂ :=
  if hi : i < n then (A.actualObservation u x ⟨i, hi⟩).location else none

def ComplexAffineAlgorithm.forbiddenSet {n : ℕ}
    (A : ComplexAffineAlgorithm (EuclideanSpace ℂ (Fin (n + 1))) n)
    (u : EuclideanSpace ℂ (Fin (n + 1))) (x : ℂ) (ε : ℝ) (i : ℕ) : Finset ℂ :=
  polynomialKernelForbiddenSet (A.polynomialObservation u x ε) (i + 1) n
    (x : ℂ) (A.queryLocation u x i)

theorem ComplexAffineAlgorithm.forbiddenSet_card_le {n : ℕ}
    (A : ComplexAffineAlgorithm (EuclideanSpace ℂ (Fin (n + 1))) n)
    (u : EuclideanSpace ℂ (Fin (n + 1))) (x : ℂ) (ε : ℝ) (i : ℕ) :
    (A.forbiddenSet u x ε i).card ≤ forbiddenWronskianCountBound n := by
  sorry

theorem ComplexAffineAlgorithm.queryLocation_eq_of_prefix_eq {n : ℕ}
    (A : ComplexAffineAlgorithm (EuclideanSpace ℂ (Fin (n + 1))) n)
    {u v : EuclideanSpace ℂ (Fin (n + 1))} {x : ℂ} {j i : ℕ}
    (hj : j < n) (hi : i ≤ j)
    (heq : A.prefix v x j (Nat.le_of_lt hj) = A.prefix u x j (Nat.le_of_lt hj)) :
    A.queryLocation v x i = A.queryLocation u x i := by
  sorry

theorem ComplexAffineAlgorithm.forbiddenSet_eq_of_prefix_eq {n : ℕ}
    (A : ComplexAffineAlgorithm (EuclideanSpace ℂ (Fin (n + 1))) n)
    {u v : EuclideanSpace ℂ (Fin (n + 1))} {x : ℂ} {ε : ℝ} {j i : ℕ}
    (hj : j < n) (hi : i ≤ j)
    (heq : A.prefix v x j (Nat.le_of_lt hj) = A.prefix u x j (Nat.le_of_lt hj)) :
    A.forbiddenSet v x ε i = A.forbiddenSet u x ε i := by
  sorry

theorem ComplexAffineAlgorithm.forbiddenSet_eq_on_parameterBall {n : ℕ}
    (A : ComplexAffineAlgorithm (EuclideanSpace ℂ (Fin (n + 1))) n)
    {u center : EuclideanSpace ℂ (Fin (n + 1))} {x : ℂ} {ε r : ℝ} {j : ℕ}
    (hj : j < n) (hu : u ∈ complexParameterBall center (A.direction center x j) r) :
    A.forbiddenSet u x ε j = A.forbiddenSet center x ε j := by
  sorry

theorem ComplexAffineAlgorithm.actual_location_mem_forbiddenSet {n : ℕ}
    (A : ComplexAffineAlgorithm (EuclideanSpace ℂ (Fin (n + 1))) n)
    (u : EuclideanSpace ℂ (Fin (n + 1))) (x : ℂ) (ε : ℝ) (i : Fin n) {z : ℂ}
    (hloc : (A.actualObservation u x i).location = some z) :
    (z : ℂ) ∈ A.forbiddenSet u x ε i.val := by
  sorry

theorem ComplexAffineAlgorithm.root_ne_actual_location_of_avoidance {n : ℕ}
    (A : ComplexAffineAlgorithm (EuclideanSpace ℂ (Fin (n + 1))) n)
    (u : EuclideanSpace ℂ (Fin (n + 1))) (x α : ℂ) (ε δ : ℝ) (i : Fin n)
    (hδ : 0 < δ)
    (havoid : ∀ z ∈ A.forbiddenSet u x ε i.val, δ ≤ ‖(α : ℂ) - z‖)
    {z : ℂ} (hloc : (A.actualObservation u x i).location = some z) : α ≠ z := by
  sorry

end KungTraubAppendices
