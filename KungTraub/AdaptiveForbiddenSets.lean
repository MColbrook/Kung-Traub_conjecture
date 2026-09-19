import KungTraub.AffinePolynomialInformation
import KungTraub.ParameterBalls
import KungTraub.ForbiddenWronskians
import KungTraub.RealPolynomialKernels

/-!
# Forbidden sets along an actual adaptive transcript

The set for step i uses exactly the first i+1 polynomial observation rows and
the location of query i, if present. Agreement through the first i answers
already determines this set: the next answer has not yet been selected.
The cardinality is at most H_n.
-/

noncomputable section

namespace KungTraub

def AffineAlgorithm.complexPolynomialObservations {n : ℕ}
    (A : AffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) n)
    (u : EuclideanSpace ℝ (Fin (n + 1))) (x ε : ℝ) :
    ℕ → Polynomial ℂ →ₗ[ℂ] ℂ :=
  complexifyPolynomialObservations (A.polynomialObservation u x ε)

def AffineAlgorithm.complexQueryLocation {n : ℕ}
    (A : AffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) n)
    (u : EuclideanSpace ℝ (Fin (n + 1))) (x : ℝ) (i : ℕ) : Option ℂ :=
  if hi : i < n then ((A.actualObservation u x ⟨i, hi⟩).location).map Complex.ofReal else none

def AffineAlgorithm.forbiddenSet {n : ℕ}
    (A : AffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) n)
    (u : EuclideanSpace ℝ (Fin (n + 1))) (x ε : ℝ) (i : ℕ) : Finset ℂ :=
  polynomialKernelForbiddenSet (A.complexPolynomialObservations u x ε) (i + 1) n
    (x : ℂ) (A.complexQueryLocation u x i)

theorem AffineAlgorithm.forbiddenSet_card_le {n : ℕ}
    (A : AffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) n)
    (u : EuclideanSpace ℝ (Fin (n + 1))) (x ε : ℝ) (i : ℕ) :
    (A.forbiddenSet u x ε i).card ≤ forbiddenWronskianCountBound n :=
  polynomialKernelForbiddenSet_card_le _ _ _ _ _

theorem AffineAlgorithm.complexQueryLocation_eq_of_prefix_eq {n : ℕ}
    (A : AffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) n)
    {u v : EuclideanSpace ℝ (Fin (n + 1))} {x : ℝ} {j i : ℕ}
    (hj : j < n) (hi : i ≤ j)
    (heq : A.prefix v x j (Nat.le_of_lt hj) = A.prefix u x j (Nat.le_of_lt hj)) :
    A.complexQueryLocation v x i = A.complexQueryLocation u x i := by
  have hin := hi.trans_lt hj
  simp only [complexQueryLocation, dif_pos hin]
  rw [A.actualObservation_eq_of_prefix_eq ⟨i, hin⟩
    (A.prefix_eq_of_later_prefix_eq hi (Nat.le_of_lt hj) heq)]

theorem AffineAlgorithm.forbiddenSet_eq_of_prefix_eq {n : ℕ}
    (A : AffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) n)
    {u v : EuclideanSpace ℝ (Fin (n + 1))} {x ε : ℝ} {j i : ℕ}
    (hj : j < n) (hi : i ≤ j)
    (heq : A.prefix v x j (Nat.le_of_lt hj) = A.prefix u x j (Nat.le_of_lt hj)) :
    A.forbiddenSet v x ε i = A.forbiddenSet u x ε i := by
  unfold forbiddenSet
  rw [A.complexQueryLocation_eq_of_prefix_eq hj hi heq]
  apply polynomialKernelForbiddenSet_congr
  intro k hk
  have hkj : k ≤ j := (Nat.le_of_lt_succ hk).trans hi
  exact congrArg complexifyPolynomialFunctional
    (A.polynomialObservation_eq_of_prefix_eq hj hkj heq)

theorem AffineAlgorithm.forbiddenSet_eq_on_parameterBall {n : ℕ}
    (A : AffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) n)
    {u center : EuclideanSpace ℝ (Fin (n + 1))} {x ε r : ℝ} {j : ℕ}
    (hj : j < n) (hu : u ∈ parameterBall center (A.direction center x j) r) :
    A.forbiddenSet u x ε j = A.forbiddenSet center x ε j :=
  A.forbiddenSet_eq_of_prefix_eq hj le_rfl (A.prefix_eq_on_parameterBall (Nat.le_of_lt hj) hu)

theorem AffineAlgorithm.actual_location_mem_forbiddenSet {n : ℕ}
    (A : AffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) n)
    (u : EuclideanSpace ℝ (Fin (n + 1))) (x ε : ℝ) (i : Fin n) {z : ℝ}
    (hloc : (A.actualObservation u x i).location = some z) :
    (z : ℂ) ∈ A.forbiddenSet u x ε i.val := by
  unfold forbiddenSet
  have hquery : A.complexQueryLocation u x i.val = some (z : ℂ) := by
    simp only [complexQueryLocation, dif_pos i.isLt, hloc, Option.map_some]
  rw [hquery]
  exact polynomialKernelForbiddenSet_contains_query _ _ _ _ _

theorem AffineAlgorithm.root_ne_actual_location_of_avoidance {n : ℕ}
    (A : AffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) n)
    (u : EuclideanSpace ℝ (Fin (n + 1))) (x ε α δ : ℝ) (i : Fin n)
    (hδ : 0 < δ)
    (havoid : ∀ z ∈ A.forbiddenSet u x ε i.val, δ ≤ ‖(α : ℂ) - z‖)
    {z : ℝ} (hloc : (A.actualObservation u x i).location = some z) : α ≠ z := by
  intro heq
  have h := havoid z (A.actual_location_mem_forbiddenSet u x ε i hloc)
  rw [heq, sub_self, norm_zero] at h
  exact (not_le_of_gt hδ) h

end KungTraub
