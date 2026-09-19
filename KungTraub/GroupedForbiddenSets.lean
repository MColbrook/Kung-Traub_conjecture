import KungTraub.GroupedPolynomialInformation
import KungTraub.GroupedPolynomialSensitivity
import KungTraub.GroupedParameterBalls

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
    (A.scalarForbiddenSet u x ε t).card ≤ forbiddenWronskianCountBound n :=
  polynomialKernelForbiddenSet_card_le _ _ _ _ _

theorem GroupedAffineAlgorithm.groupForbiddenSet_card_le {n k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) sizes)
    (u : EuclideanSpace ℝ (Fin (n + 1))) (x ε : ℝ) (g : Fin k) :
    (A.groupForbiddenSet u x ε g).card ≤ sizes g * forbiddenWronskianCountBound n := by
  classical
  calc
    (A.groupForbiddenSet u x ε g).card ≤
        ∑ slot : Fin (sizes g), (A.scalarForbiddenSet u x ε (groupSlotEquiv sizes ⟨g, slot⟩).val).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _slot : Fin (sizes g), forbiddenWronskianCountBound n :=
      Finset.sum_le_sum (fun slot _ => A.scalarForbiddenSet_card_le u x ε _)
    _ = sizes g * forbiddenWronskianCountBound n := by simp

theorem GroupedAffineAlgorithm.complexQueryLocation_groupSlotEquiv
    {n k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) sizes)
    (u : EuclideanSpace ℝ (Fin (n + 1))) (x : ℝ) (g : Fin k) (slot : Fin (sizes g)) :
    A.complexQueryLocation u x (groupSlotEquiv sizes ⟨g, slot⟩).val =
      ((A.actualObservations u x g slot).location).map Complex.ofReal := by
  simp only [complexQueryLocation, dif_pos (groupSlotEquiv sizes ⟨g, slot⟩).isLt]
  exact congrArg (fun pair : (g : Fin k) × Fin (sizes g) =>
    ((A.actualObservations u x pair.1 pair.2).location).map Complex.ofReal)
    ((groupSlotEquiv sizes).symm_apply_apply ⟨g, slot⟩)

theorem GroupedAffineAlgorithm.complexQueryLocation_eq_of_prefix_eq
    {n k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) sizes)
    {u v : EuclideanSpace ℝ (Fin (n + 1))} {x : ℝ} {j t : ℕ} (hj : j ≤ k)
    (ht : t < groupedObservationCount sizes) (hgroup : scalarGroupAt sizes t ≤ j)
    (heq : A.prefix v x j hj = A.prefix u x j hj) :
    A.complexQueryLocation v x t = A.complexQueryLocation u x t := by
  obtain ⟨pair, hp⟩ := (groupSlotEquiv sizes).surjective ⟨t, ht⟩
  have hval : (groupSlotEquiv sizes pair).val = t := congrArg Fin.val hp
  have hgj : pair.1.val ≤ j := by
    rw [← hval, scalarGroupAt_groupSlotEquiv] at hgroup
    exact hgroup
  rw [← hval, A.complexQueryLocation_groupSlotEquiv, A.complexQueryLocation_groupSlotEquiv]
  rw [A.actualObservations_eq_of_prefix_eq pair.1 (A.prefix_eq_of_later_prefix_eq hgj hj heq)]

/-- Every scalar set through the current group is fixed by the preceding complete
group prefix, even when the scalar row lies inside the current group. -/
theorem GroupedAffineAlgorithm.scalarForbiddenSet_eq_of_prefix_eq
    {n k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) sizes)
    {u v : EuclideanSpace ℝ (Fin (n + 1))} {x ε : ℝ} {j t : ℕ} (hj : j < k)
    (ht : t < groupedPrefixCount sizes (j + 1))
    (heq : A.prefix v x j hj.le = A.prefix u x j hj.le) :
    A.scalarForbiddenSet v x ε t = A.scalarForbiddenSet u x ε t := by
  have htotal := ht.trans_le (groupedPrefixCount_le_total sizes (Nat.succ_le_of_lt hj))
  have hg : scalarGroupAt sizes t ≤ j := Nat.le_of_lt_succ
    ((scalarGroupAt_lt_prefix_iff sizes ⟨t, htotal⟩ (Nat.succ_le_of_lt hj)).mpr ht)
  unfold scalarForbiddenSet
  rw [A.complexQueryLocation_eq_of_prefix_eq hj.le htotal hg heq]
  apply polynomialKernelForbiddenSet_congr
  intro i hi
  have hinext : i < groupedPrefixCount sizes (j + 1) :=
    (Nat.le_of_lt_succ hi).trans_lt ht
  have hitotal := hinext.trans_le (groupedPrefixCount_le_total sizes (Nat.succ_le_of_lt hj))
  have hig : scalarGroupAt sizes i ≤ j := Nat.le_of_lt_succ
    ((scalarGroupAt_lt_prefix_iff sizes ⟨i, hitotal⟩ (Nat.succ_le_of_lt hj)).mpr hinext)
  exact congrArg complexifyPolynomialFunctional
    (A.polynomialObservation_eq_of_prefix_eq hj.le hitotal hig heq)

theorem GroupedAffineAlgorithm.groupForbiddenSet_eq_of_prefix_eq
    {n k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) sizes)
    {u v : EuclideanSpace ℝ (Fin (n + 1))} {x ε : ℝ} (g : Fin k)
    (heq : A.prefix v x g.val g.isLt.le = A.prefix u x g.val g.isLt.le) :
    A.groupForbiddenSet v x ε g = A.groupForbiddenSet u x ε g := by
  classical
  unfold groupForbiddenSet
  apply Finset.biUnion_congr rfl
  intro slot _
  exact A.scalarForbiddenSet_eq_of_prefix_eq g.isLt
    ((groupSlotEquiv_lt_prefix_iff sizes g slot (Nat.succ_le_of_lt g.isLt)).mpr
      (Nat.lt_succ_self g.val)) heq

theorem GroupedAffineAlgorithm.scalarForbiddenSet_subset_groupForbiddenSet
    {n k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) sizes)
    (u : EuclideanSpace ℝ (Fin (n + 1))) (x ε : ℝ) (g : Fin k) (slot : Fin (sizes g)) :
    A.scalarForbiddenSet u x ε (groupSlotEquiv sizes ⟨g, slot⟩).val ⊆
      A.groupForbiddenSet u x ε g := by
  classical
  intro z hz
  exact Finset.mem_biUnion.mpr ⟨slot, Finset.mem_univ _, hz⟩

theorem GroupedAffineAlgorithm.groupForbiddenSet_eq_on_parameterBall
    {n k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) sizes)
    {u center : EuclideanSpace ℝ (Fin (n + 1))} {x ε r : ℝ} (g : Fin k)
    (hu : u ∈ parameterBall center (A.direction center x g.val) r) :
    A.groupForbiddenSet u x ε g = A.groupForbiddenSet center x ε g :=
  A.groupForbiddenSet_eq_of_prefix_eq g (A.prefix_eq_on_parameterBall g.isLt.le hu)

theorem GroupedAffineAlgorithm.scalarForbiddenSet_subset_groupForbiddenSet_of_range
    {n k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) sizes)
    (u : EuclideanSpace ℝ (Fin (n + 1))) (x ε : ℝ) (g : Fin k) {t : ℕ}
    (hlo : groupedPrefixCount sizes g.val ≤ t)
    (hhi : t < groupedPrefixCount sizes (g.val + 1)) :
    A.scalarForbiddenSet u x ε t ⊆ A.groupForbiddenSet u x ε g := by
  have ht : t - groupedPrefixCount sizes g.val < sizes g := by
    rw [groupedPrefixCount_succ sizes g.isLt] at hhi
    change t < groupedPrefixCount sizes g.val + sizes g at hhi
    omega
  let slot : Fin (sizes g) := ⟨t - groupedPrefixCount sizes g.val, ht⟩
  have heq : (groupSlotEquiv sizes ⟨g, slot⟩).val = t := by
    rw [groupSlotEquiv_apply]
    exact Nat.add_sub_of_le hlo
  rw [← heq]
  exact A.scalarForbiddenSet_subset_groupForbiddenSet u x ε g slot

theorem GroupedAffineAlgorithm.actual_location_mem_scalarForbiddenSet
    {n k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) sizes)
    (u : EuclideanSpace ℝ (Fin (n + 1))) (x ε : ℝ) (g : Fin k) (slot : Fin (sizes g)) {z : ℝ}
    (hloc : (A.actualObservations u x g slot).location = some z) :
    (z : ℂ) ∈ A.scalarForbiddenSet u x ε (groupSlotEquiv sizes ⟨g, slot⟩).val := by
  unfold scalarForbiddenSet
  rw [A.complexQueryLocation_groupSlotEquiv, hloc, Option.map_some]
  exact polynomialKernelForbiddenSet_contains_query _ _ _ _ _

theorem GroupedAffineAlgorithm.actual_location_mem_groupForbiddenSet
    {n k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) sizes)
    (u : EuclideanSpace ℝ (Fin (n + 1))) (x ε : ℝ) (g : Fin k) (slot : Fin (sizes g)) {z : ℝ}
    (hloc : (A.actualObservations u x g slot).location = some z) :
    (z : ℂ) ∈ A.groupForbiddenSet u x ε g :=
  A.scalarForbiddenSet_subset_groupForbiddenSet u x ε g slot
    (A.actual_location_mem_scalarForbiddenSet u x ε g slot hloc)

theorem GroupedAffineAlgorithm.root_ne_actual_location_of_scalar_avoidance
    {n k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) sizes)
    (u : EuclideanSpace ℝ (Fin (n + 1))) (x ε α δ : ℝ) (g : Fin k) (slot : Fin (sizes g))
    (hδ : 0 < δ)
    (havoid : ∀ z ∈ A.scalarForbiddenSet u x ε (groupSlotEquiv sizes ⟨g, slot⟩).val,
      δ ≤ ‖(α : ℂ) - z‖)
    {z : ℝ} (hloc : (A.actualObservations u x g slot).location = some z) : α ≠ z := by
  intro heq
  have h := havoid z (A.actual_location_mem_scalarForbiddenSet u x ε g slot hloc)
  rw [heq, sub_self, norm_zero] at h
  exact (not_le_of_gt hδ) h

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
  rw [A.direction_eq_polynomial_kernel u x hε.ne' j]
  exact grouped_real_kernel_projected_sensitivity_lower_bound sizes hsizes hj hjk
    (A.polynomialObservation u x ε) α x γ hγ hε hε1 hR hwmin hw ha hhalf
    (A.complexQueryLocation u x) havoid

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
  intro t ht z hz
  have htotal := ht.trans_le (groupedPrefixCount_le_total sizes hjk)
  obtain ⟨pair, hp⟩ := (groupSlotEquiv sizes).surjective ⟨t, htotal⟩
  have hval : (groupSlotEquiv sizes pair).val = t := congrArg Fin.val hp
  have hg : pair.1.val < j := (groupSlotEquiv_lt_prefix_iff sizes pair.1 pair.2 hjk).mp
    (by simpa only [hval] using ht)
  have hgroup : scalarGroupAt sizes (groupSlotEquiv sizes pair).val = pair.1.val :=
    scalarGroupAt_groupSlotEquiv sizes pair.1 pair.2
  rw [← hval] at hz ⊢
  simpa only [groupedScalarExponent, hgroup] using
    havoid pair.1 hg z (A.scalarForbiddenSet_subset_groupForbiddenSet u x ε pair.1 pair.2 hz)

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
  have hγscalar : ∀ t < groupedPrefixCount sizes j, 0 < γ (scalarGroupAt sizes t) := by
    intro t ht
    have htotal := ht.trans_le (groupedPrefixCount_le_total sizes hjk)
    exact hγ _ ((scalarGroupAt_lt_prefix_iff sizes ⟨t, htotal⟩ hjk).mpr ht)
  exact A.projected_sensitivity_of_forbidden_avoidance hsizes hj hjk u α x
    (fun t => γ (scalarGroupAt sizes t)) hγscalar hε hε1 hR hwmin hw ha hhalf
    (A.scalar_avoidance_of_group_avoidance hjk u x ε α γ havoid)

end KungTraub
