import appendix_reference.KungTraub.GroupedExponents

/-!
# Scalar positions in a prescribed group schedule

Mathlib's explicit `finSigmaFinEquiv` orders group/slot pairs by group and then
slot. Its offset formula proves that a group prefix is exactly a scalar prefix.
The exponent assigned to each scalar position is the exponent before its group;
the sum over any injective set of rank positions is bounded by the exact C_j.
-/

namespace KungTraub
open scoped BigOperators

def groupSlotEquiv {k : ℕ} (sizes : Fin k → ℕ) :
    ((g : Fin k) × Fin (sizes g)) ≃ Fin (groupedObservationCount sizes) :=
  finSigmaFinEquiv

theorem groupedPrefixCount_eq_sum_fin {k : ℕ} (sizes : Fin k → ℕ)
    {j : ℕ} (hj : j ≤ k) :
    groupedPrefixCount sizes j = ∑ i : Fin j, sizes ⟨i.val, i.isLt.trans_le hj⟩ := by
  sorry

theorem groupSlotEquiv_apply {k : ℕ} (sizes : Fin k → ℕ)
    (g : Fin k) (slot : Fin (sizes g)) :
    (groupSlotEquiv sizes ⟨g, slot⟩).val = groupedPrefixCount sizes g.val + slot.val := by
  sorry

theorem groupSlotEquiv_lt_prefix_iff {k : ℕ} (sizes : Fin k → ℕ)
    (g : Fin k) (slot : Fin (sizes g)) {j : ℕ} (_hj : j ≤ k) :
    (groupSlotEquiv sizes ⟨g, slot⟩).val < groupedPrefixCount sizes j ↔ g.val < j := by
  sorry

def scalarGroupAt {k : ℕ} (sizes : Fin k → ℕ) (t : ℕ) : ℕ :=
  if ht : t < groupedObservationCount sizes then ((groupSlotEquiv sizes).symm ⟨t, ht⟩).1.val else k

theorem scalarGroupAt_groupSlotEquiv {k : ℕ} (sizes : Fin k → ℕ)
    (g : Fin k) (slot : Fin (sizes g)) :
    scalarGroupAt sizes (groupSlotEquiv sizes ⟨g, slot⟩).val = g.val := by
  sorry

theorem scalarGroupAt_offset {k : ℕ} (sizes : Fin k → ℕ)
    {j t : ℕ} (hj : j < k) (ht : t < sizes ⟨j, hj⟩) :
    scalarGroupAt sizes (groupedPrefixCount sizes j + t) = j := by
  sorry

theorem scalarGroupAt_lt_prefix_iff {k : ℕ} (sizes : Fin k → ℕ)
    (t : Fin (groupedObservationCount sizes)) {j : ℕ} (hj : j ≤ k) :
    scalarGroupAt sizes t.val < j ↔ t.val < groupedPrefixCount sizes j := by
  sorry

def groupedScalarExponent {k : ℕ} (sizes : Fin k → ℕ) (t : ℕ) : ℕ :=
  groupedStageExponent sizes (scalarGroupAt sizes t)

theorem groupedScalarExponent_offset {k : ℕ} (sizes : Fin k → ℕ)
    {j t : ℕ} (hj : j < k) (ht : t < sizes ⟨j, hj⟩) :
    groupedScalarExponent sizes (groupedPrefixCount sizes j + t) = groupedStageExponent sizes j := by
  sorry

theorem sum_groupedScalarExponent_prefix_eq_weighted_sum {k : ℕ} (sizes : Fin k → ℕ)
    {j : ℕ} (hj : j ≤ k) :
    ∑ t ∈ Finset.range (groupedPrefixCount sizes j), groupedScalarExponent sizes t =
      ∑ i ∈ Finset.range j, groupSizeAt sizes i * groupedStageExponent sizes i := by
  sorry

theorem sum_groupedScalarExponent_prefix {k : ℕ} (sizes : Fin k → ℕ)
    {j : ℕ} (hj : 0 < j) (hjk : j ≤ k) :
    ∑ t ∈ Finset.range (groupedPrefixCount sizes j), groupedScalarExponent sizes t =
      groupedStageExponent sizes j := by
  sorry

/-- The actual distinct scalar rank-increase indices have total exponent at most C_j. -/
theorem sum_groupedScalarExponent_selected_le {k d : ℕ} (sizes : Fin k → ℕ)
    {j : ℕ} (hj : 0 < j) (hjk : j ≤ k)
    (indices : Fin d → Fin (groupedPrefixCount sizes j)) (hinj : Function.Injective indices) :
    (∑ i : Fin d, groupedScalarExponent sizes (indices i).val) ≤ groupedStageExponent sizes j := by
  sorry

end KungTraub
