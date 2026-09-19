import KungTraubAppendices.ComplexPolynomialInformation
import KungTraubAppendices.ComplexParameterBalls
import KungTraub.ForbiddenWronskians

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
    (A.forbiddenSet u x ε i).card ≤ forbiddenWronskianCountBound n :=
  polynomialKernelForbiddenSet_card_le _ _ _ _ _

theorem ComplexAffineAlgorithm.queryLocation_eq_of_prefix_eq {n : ℕ}
    (A : ComplexAffineAlgorithm (EuclideanSpace ℂ (Fin (n + 1))) n)
    {u v : EuclideanSpace ℂ (Fin (n + 1))} {x : ℂ} {j i : ℕ}
    (hj : j < n) (hi : i ≤ j)
    (heq : A.prefix v x j (Nat.le_of_lt hj) = A.prefix u x j (Nat.le_of_lt hj)) :
    A.queryLocation v x i = A.queryLocation u x i := by
  have hin := hi.trans_lt hj
  simp only [queryLocation, dif_pos hin]
  rw [A.actualObservation_eq_of_prefix_eq ⟨i, hin⟩
    (A.prefix_eq_of_later_prefix_eq hi (Nat.le_of_lt hj) heq)]

theorem ComplexAffineAlgorithm.forbiddenSet_eq_of_prefix_eq {n : ℕ}
    (A : ComplexAffineAlgorithm (EuclideanSpace ℂ (Fin (n + 1))) n)
    {u v : EuclideanSpace ℂ (Fin (n + 1))} {x : ℂ} {ε : ℝ} {j i : ℕ}
    (hj : j < n) (hi : i ≤ j)
    (heq : A.prefix v x j (Nat.le_of_lt hj) = A.prefix u x j (Nat.le_of_lt hj)) :
    A.forbiddenSet v x ε i = A.forbiddenSet u x ε i := by
  unfold forbiddenSet
  rw [A.queryLocation_eq_of_prefix_eq hj hi heq]
  apply polynomialKernelForbiddenSet_congr
  intro k hk
  have hkj : k ≤ j := (Nat.le_of_lt_succ hk).trans hi
  exact A.polynomialObservation_eq_of_prefix_eq hj hkj heq

theorem ComplexAffineAlgorithm.forbiddenSet_eq_on_parameterBall {n : ℕ}
    (A : ComplexAffineAlgorithm (EuclideanSpace ℂ (Fin (n + 1))) n)
    {u center : EuclideanSpace ℂ (Fin (n + 1))} {x : ℂ} {ε r : ℝ} {j : ℕ}
    (hj : j < n) (hu : u ∈ complexParameterBall center (A.direction center x j) r) :
    A.forbiddenSet u x ε j = A.forbiddenSet center x ε j :=
  A.forbiddenSet_eq_of_prefix_eq hj le_rfl (A.prefix_eq_on_parameterBall (Nat.le_of_lt hj) hu)

theorem ComplexAffineAlgorithm.actual_location_mem_forbiddenSet {n : ℕ}
    (A : ComplexAffineAlgorithm (EuclideanSpace ℂ (Fin (n + 1))) n)
    (u : EuclideanSpace ℂ (Fin (n + 1))) (x : ℂ) (ε : ℝ) (i : Fin n) {z : ℂ}
    (hloc : (A.actualObservation u x i).location = some z) :
    (z : ℂ) ∈ A.forbiddenSet u x ε i.val := by
  unfold forbiddenSet
  have hquery : A.queryLocation u x i.val = some (z : ℂ) := by
    simp only [queryLocation, dif_pos i.isLt, hloc]
  rw [hquery]
  exact polynomialKernelForbiddenSet_contains_query _ _ _ _ _

theorem ComplexAffineAlgorithm.root_ne_actual_location_of_avoidance {n : ℕ}
    (A : ComplexAffineAlgorithm (EuclideanSpace ℂ (Fin (n + 1))) n)
    (u : EuclideanSpace ℂ (Fin (n + 1))) (x α : ℂ) (ε δ : ℝ) (i : Fin n)
    (hδ : 0 < δ)
    (havoid : ∀ z ∈ A.forbiddenSet u x ε i.val, δ ≤ ‖(α : ℂ) - z‖)
    {z : ℂ} (hloc : (A.actualObservation u x i).location = some z) : α ≠ z := by
  intro heq
  have h := havoid z (A.actual_location_mem_forbiddenSet u x ε i hloc)
  rw [heq, sub_self, norm_zero] at h
  exact (not_le_of_gt hδ) h

end KungTraubAppendices
