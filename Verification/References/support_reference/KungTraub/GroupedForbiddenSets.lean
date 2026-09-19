import support_reference.KungTraub.GroupedPolynomialInformation
import support_reference.KungTraub.GroupedPolynomialSensitivity
import support_reference.KungTraub.GroupedParameterBalls

/-!
# Forbidden sets fixed before a group is answered

Each scalar prefix contributes its actual canonical polynomial Wronskian roots
and query location. The current group uses their finite union. Every row and
location entering this union is already determined by the earlier complete
groups, so the entire union is fixed on their exact transcript fibre.
-/

noncomputable section
open scoped BigOperators
namespace KungTraub

def GroupedAffineAlgorithm.complexPolynomialObservations {n k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) sizes)
    (u : EuclideanSpace ℝ (Fin (n + 1))) (x ε : ℝ) :
    ℕ → Polynomial ℂ →ₗ[ℂ] ℂ :=
  complexifyPolynomialObservations (A.polynomialObservation u x ε)

def GroupedAffineAlgorithm.complexQueryLocation {n k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) sizes)
    (u : EuclideanSpace ℝ (Fin (n + 1))) (x : ℝ) (t : ℕ) : Option ℂ :=
  if ht : t < groupedObservationCount sizes then
    let pair := (groupSlotEquiv sizes).symm ⟨t, ht⟩
    ((A.actualObservations u x pair.1 pair.2).location).map Complex.ofReal
  else none

def GroupedAffineAlgorithm.scalarForbiddenSet {n k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) sizes)
    (u : EuclideanSpace ℝ (Fin (n + 1))) (x ε : ℝ) (t : ℕ) : Finset ℂ :=
  polynomialKernelForbiddenSet (A.complexPolynomialObservations u x ε) (t + 1) n
    (x : ℂ) (A.complexQueryLocation u x t)

def GroupedAffineAlgorithm.groupForbiddenSet {n k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) sizes)
    (u : EuclideanSpace ℝ (Fin (n + 1))) (x ε : ℝ) (g : Fin k) : Finset ℂ :=
  Finset.univ.biUnion (fun slot : Fin (sizes g) =>
    A.scalarForbiddenSet u x ε (groupSlotEquiv sizes ⟨g, slot⟩).val)

theorem GroupedAffineAlgorithm.scalarForbiddenSet_card_le {n k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) sizes)
    (u : EuclideanSpace ℝ (Fin (n + 1))) (x ε : ℝ) (t : ℕ) :
    (A.scalarForbiddenSet u x ε t).card ≤ forbiddenWronskianCountBound n := by
  sorry

theorem GroupedAffineAlgorithm.groupForbiddenSet_card_le {n k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) sizes)
    (u : EuclideanSpace ℝ (Fin (n + 1))) (x ε : ℝ) (g : Fin k) :
    (A.groupForbiddenSet u x ε g).card ≤ sizes g * forbiddenWronskianCountBound n := by
  sorry

theorem GroupedAffineAlgorithm.complexQueryLocation_groupSlotEquiv
    {n k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) sizes)
    (u : EuclideanSpace ℝ (Fin (n + 1))) (x : ℝ) (g : Fin k) (slot : Fin (sizes g)) :
    A.complexQueryLocation u x (groupSlotEquiv sizes ⟨g, slot⟩).val =
      ((A.actualObservations u x g slot).location).map Complex.ofReal := by
  sorry

theorem GroupedAffineAlgorithm.complexQueryLocation_eq_of_prefix_eq
    {n k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) sizes)
    {u v : EuclideanSpace ℝ (Fin (n + 1))} {x : ℝ} {j t : ℕ} (hj : j ≤ k)
    (ht : t < groupedObservationCount sizes) (hgroup : scalarGroupAt sizes t ≤ j)
    (heq : A.prefix v x j hj = A.prefix u x j hj) :
    A.complexQueryLocation v x t = A.complexQueryLocation u x t := by
  sorry

/-- Every scalar set through the current group is fixed by the preceding complete
group prefix, even when the scalar row lies inside the current group. -/
theorem GroupedAffineAlgorithm.scalarForbiddenSet_eq_of_prefix_eq
    {n k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) sizes)
    {u v : EuclideanSpace ℝ (Fin (n + 1))} {x ε : ℝ} {j t : ℕ} (hj : j < k)
    (ht : t < groupedPrefixCount sizes (j + 1))
    (heq : A.prefix v x j hj.le = A.prefix u x j hj.le) :
    A.scalarForbiddenSet v x ε t = A.scalarForbiddenSet u x ε t := by
  sorry

theorem GroupedAffineAlgorithm.groupForbiddenSet_eq_of_prefix_eq
    {n k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) sizes)
    {u v : EuclideanSpace ℝ (Fin (n + 1))} {x ε : ℝ} (g : Fin k)
    (heq : A.prefix v x g.val g.isLt.le = A.prefix u x g.val g.isLt.le) :
    A.groupForbiddenSet v x ε g = A.groupForbiddenSet u x ε g := by
  sorry

theorem GroupedAffineAlgorithm.scalarForbiddenSet_subset_groupForbiddenSet
    {n k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) sizes)
    (u : EuclideanSpace ℝ (Fin (n + 1))) (x ε : ℝ) (g : Fin k) (slot : Fin (sizes g)) :
    A.scalarForbiddenSet u x ε (groupSlotEquiv sizes ⟨g, slot⟩).val ⊆
      A.groupForbiddenSet u x ε g := by
  sorry

theorem GroupedAffineAlgorithm.groupForbiddenSet_eq_on_parameterBall
    {n k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) sizes)
    {u center : EuclideanSpace ℝ (Fin (n + 1))} {x ε r : ℝ} (g : Fin k)
    (hu : u ∈ parameterBall center (A.direction center x g.val) r) :
    A.groupForbiddenSet u x ε g = A.groupForbiddenSet center x ε g := by
  sorry

theorem GroupedAffineAlgorithm.scalarForbiddenSet_subset_groupForbiddenSet_of_range
    {n k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) sizes)
    (u : EuclideanSpace ℝ (Fin (n + 1))) (x ε : ℝ) (g : Fin k) {t : ℕ}
    (hlo : groupedPrefixCount sizes g.val ≤ t)
    (hhi : t < groupedPrefixCount sizes (g.val + 1)) :
    A.scalarForbiddenSet u x ε t ⊆ A.groupForbiddenSet u x ε g := by
  sorry

theorem GroupedAffineAlgorithm.actual_location_mem_scalarForbiddenSet
    {n k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) sizes)
    (u : EuclideanSpace ℝ (Fin (n + 1))) (x ε : ℝ) (g : Fin k) (slot : Fin (sizes g)) {z : ℝ}
    (hloc : (A.actualObservations u x g slot).location = some z) :
    (z : ℂ) ∈ A.scalarForbiddenSet u x ε (groupSlotEquiv sizes ⟨g, slot⟩).val := by
  sorry

theorem GroupedAffineAlgorithm.actual_location_mem_groupForbiddenSet
    {n k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) sizes)
    (u : EuclideanSpace ℝ (Fin (n + 1))) (x ε : ℝ) (g : Fin k) (slot : Fin (sizes g)) {z : ℝ}
    (hloc : (A.actualObservations u x g slot).location = some z) :
    (z : ℂ) ∈ A.groupForbiddenSet u x ε g := by
  sorry

theorem GroupedAffineAlgorithm.root_ne_actual_location_of_scalar_avoidance
    {n k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) sizes)
    (u : EuclideanSpace ℝ (Fin (n + 1))) (x ε α δ : ℝ) (g : Fin k) (slot : Fin (sizes g))
    (hδ : 0 < δ)
    (havoid : ∀ z ∈ A.scalarForbiddenSet u x ε (groupSlotEquiv sizes ⟨g, slot⟩).val,
      δ ≤ ‖(α : ℂ) - z‖)
    {z : ℝ} (hloc : (A.actualObservations u x g slot).location = some z) : α ≠ z := by
  sorry

theorem GroupedAffineAlgorithm.projected_sensitivity_of_forbidden_avoidance
    {k j : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm
      (EuclideanSpace ℝ (Fin (groupedObservationCount sizes + 1))) sizes)
    (hsizes : ∀ i, 0 < sizes i) (hj : 0 < j) (hjk : j ≤ k)
    (u : EuclideanSpace ℝ (Fin (groupedObservationCount sizes + 1))) (α x : ℝ)
    (γ : ℕ → ℝ) (hγ : ∀ t < groupedPrefixCount sizes j, 0 < γ t)
    {ε R wmin w : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 < R)
    (hwmin : 0 < wmin) (hw : wmin ≤ |w|)
    (ha : |α - x| ≤ R * ε) (hhalf : R * ε ≤ 1 / 2)
    (havoid : ∀ t < groupedPrefixCount sizes j, ∀ z ∈ A.scalarForbiddenSet u x ε t,
      γ t * ε ^ groupedScalarExponent sizes t ≤ ‖(α : ℂ) - z‖) :
    (wmin * sensitivityPolynomialConstant (groupedObservationCount sizes) γ
      (groupedPrefixCount sizes j) / (2 * R + 2)) * ε ^ groupedStageExponent sizes j ≤
      ‖(A.direction u x j).starProjection
        (realPolynomialEvaluationVector (groupedObservationCount sizes) ε w (α - x))‖ := by
  sorry

/-- The group-indexed invariant supplies the avoidance hypotheses at every scalar
rank position, with the exponent before that scalar's group. -/
theorem GroupedAffineAlgorithm.scalar_avoidance_of_group_avoidance
    {n k j : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) sizes)
    (hjk : j ≤ k) (u : EuclideanSpace ℝ (Fin (n + 1))) (x ε α : ℝ) (γ : ℕ → ℝ)
    (havoid : ∀ g : Fin k, g.val < j → ∀ z ∈ A.groupForbiddenSet u x ε g,
      γ g.val * ε ^ groupedStageExponent sizes g.val ≤ ‖(α : ℂ) - z‖) :
    ∀ t < groupedPrefixCount sizes j, ∀ z ∈ A.scalarForbiddenSet u x ε t,
      γ (scalarGroupAt sizes t) * ε ^ groupedScalarExponent sizes t ≤ ‖(α : ℂ) - z‖ := by
  sorry

/-- The exact grouped sensitivity bound follows directly from the group-indexed
avoidance invariant, without any scalar-exponent or rank-sum assumption. -/
theorem GroupedAffineAlgorithm.projected_sensitivity_of_group_forbidden_avoidance
    {k j : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm
      (EuclideanSpace ℝ (Fin (groupedObservationCount sizes + 1))) sizes)
    (hsizes : ∀ i, 0 < sizes i) (hj : 0 < j) (hjk : j ≤ k)
    (u : EuclideanSpace ℝ (Fin (groupedObservationCount sizes + 1))) (α x : ℝ)
    (γ : ℕ → ℝ) (hγ : ∀ i < j, 0 < γ i)
    {ε R wmin w : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 < R)
    (hwmin : 0 < wmin) (hw : wmin ≤ |w|)
    (ha : |α - x| ≤ R * ε) (hhalf : R * ε ≤ 1 / 2)
    (havoid : ∀ g : Fin k, g.val < j → ∀ z ∈ A.groupForbiddenSet u x ε g,
      γ g.val * ε ^ groupedStageExponent sizes g.val ≤ ‖(α : ℂ) - z‖) :
    (wmin * sensitivityPolynomialConstant (groupedObservationCount sizes)
      (fun t => γ (scalarGroupAt sizes t)) (groupedPrefixCount sizes j) / (2 * R + 2)) *
      ε ^ groupedStageExponent sizes j ≤
      ‖(A.direction u x j).starProjection
        (realPolynomialEvaluationVector (groupedObservationCount sizes) ε w (α - x))‖ := by
  sorry

end KungTraub
