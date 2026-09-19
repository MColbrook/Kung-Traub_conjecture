import KungTraub.GroupedExponents

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
  rw [groupedPrefixCount, ← Fin.sum_univ_eq_sum_range (groupSizeAt sizes)]
  apply Finset.sum_congr rfl
  intro i _
  exact groupSizeAt_of_lt sizes (i.isLt.trans_le hj)

theorem groupSlotEquiv_apply {k : ℕ} (sizes : Fin k → ℕ)
    (g : Fin k) (slot : Fin (sizes g)) :
    (groupSlotEquiv sizes ⟨g, slot⟩).val = groupedPrefixCount sizes g.val + slot.val := by
  change (finSigmaFinEquiv (n := sizes) ⟨g, slot⟩).val = _
  rw [finSigmaFinEquiv_apply,
    groupedPrefixCount_eq_sum_fin sizes g.isLt.le]
  rfl

theorem groupSlotEquiv_lt_prefix_iff {k : ℕ} (sizes : Fin k → ℕ)
    (g : Fin k) (slot : Fin (sizes g)) {j : ℕ} (_hj : j ≤ k) :
    (groupSlotEquiv sizes ⟨g, slot⟩).val < groupedPrefixCount sizes j ↔ g.val < j := by
  rw [groupSlotEquiv_apply]
  constructor
  · intro h
    by_contra hgj
    have hmono := groupedPrefixCount_mono sizes (Nat.le_of_not_gt hgj)
    omega
  · intro hgj
    have hmono := groupedPrefixCount_mono sizes (Nat.succ_le_of_lt hgj)
    rw [groupedPrefixCount_succ sizes g.isLt] at hmono
    change groupedPrefixCount sizes g.val + sizes g ≤ groupedPrefixCount sizes j at hmono
    have := slot.isLt
    omega

def scalarGroupAt {k : ℕ} (sizes : Fin k → ℕ) (t : ℕ) : ℕ :=
  if ht : t < groupedObservationCount sizes then ((groupSlotEquiv sizes).symm ⟨t, ht⟩).1.val else k

theorem scalarGroupAt_groupSlotEquiv {k : ℕ} (sizes : Fin k → ℕ)
    (g : Fin k) (slot : Fin (sizes g)) :
    scalarGroupAt sizes (groupSlotEquiv sizes ⟨g, slot⟩).val = g.val := by
  simp [scalarGroupAt]

theorem scalarGroupAt_offset {k : ℕ} (sizes : Fin k → ℕ)
    {j t : ℕ} (hj : j < k) (ht : t < sizes ⟨j, hj⟩) :
    scalarGroupAt sizes (groupedPrefixCount sizes j + t) = j := by
  have h := scalarGroupAt_groupSlotEquiv sizes ⟨j, hj⟩ ⟨t, ht⟩
  rwa [groupSlotEquiv_apply] at h

theorem scalarGroupAt_lt_prefix_iff {k : ℕ} (sizes : Fin k → ℕ)
    (t : Fin (groupedObservationCount sizes)) {j : ℕ} (hj : j ≤ k) :
    scalarGroupAt sizes t.val < j ↔ t.val < groupedPrefixCount sizes j := by
  obtain ⟨pair, rfl⟩ := (groupSlotEquiv sizes).surjective t
  rw [scalarGroupAt_groupSlotEquiv]
  exact (groupSlotEquiv_lt_prefix_iff sizes pair.1 pair.2 hj).symm

def groupedScalarExponent {k : ℕ} (sizes : Fin k → ℕ) (t : ℕ) : ℕ :=
  groupedStageExponent sizes (scalarGroupAt sizes t)

theorem groupedScalarExponent_offset {k : ℕ} (sizes : Fin k → ℕ)
    {j t : ℕ} (hj : j < k) (ht : t < sizes ⟨j, hj⟩) :
    groupedScalarExponent sizes (groupedPrefixCount sizes j + t) = groupedStageExponent sizes j := by
  rw [groupedScalarExponent, scalarGroupAt_offset sizes hj ht]

theorem sum_groupedScalarExponent_prefix_eq_weighted_sum {k : ℕ} (sizes : Fin k → ℕ)
    {j : ℕ} (hj : j ≤ k) :
    ∑ t ∈ Finset.range (groupedPrefixCount sizes j), groupedScalarExponent sizes t =
      ∑ i ∈ Finset.range j, groupSizeAt sizes i * groupedStageExponent sizes i := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hjk : j < k := by omega
    rw [groupedPrefixCount_succ sizes hjk, Finset.sum_range_add, ih (by omega),
      Finset.sum_range_succ, groupSizeAt_of_lt sizes hjk]
    congr 1
    calc
      ∑ t ∈ Finset.range (sizes ⟨j, hjk⟩),
          groupedScalarExponent sizes (groupedPrefixCount sizes j + t) =
          ∑ _t ∈ Finset.range (sizes ⟨j, hjk⟩), groupedStageExponent sizes j := by
        apply Finset.sum_congr rfl
        intro t ht
        exact groupedScalarExponent_offset sizes hjk (Finset.mem_range.mp ht)
      _ = sizes ⟨j, hjk⟩ * groupedStageExponent sizes j := by simp

theorem sum_groupedScalarExponent_prefix {k : ℕ} (sizes : Fin k → ℕ)
    {j : ℕ} (hj : 0 < j) (hjk : j ≤ k) :
    ∑ t ∈ Finset.range (groupedPrefixCount sizes j), groupedScalarExponent sizes t =
      groupedStageExponent sizes j := by
  rw [sum_groupedScalarExponent_prefix_eq_weighted_sum sizes hjk,
    ← groupedStageExponent_eq_weighted_sum sizes hj hjk]

/-- The actual distinct scalar rank-increase indices have total exponent at most C_j. -/
theorem sum_groupedScalarExponent_selected_le {k d : ℕ} (sizes : Fin k → ℕ)
    {j : ℕ} (hj : 0 < j) (hjk : j ≤ k)
    (indices : Fin d → Fin (groupedPrefixCount sizes j)) (hinj : Function.Injective indices) :
    (∑ i : Fin d, groupedScalarExponent sizes (indices i).val) ≤ groupedStageExponent sizes j := by
  classical
  let s := Finset.univ.image (fun i : Fin d => (indices i).val)
  have hs : s ⊆ Finset.range (groupedPrefixCount sizes j) := by
    intro t ht
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ht
    exact Finset.mem_range.mpr (indices i).isLt
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hs
    (f := groupedScalarExponent sizes) (by intros; exact Nat.zero_le _)
  have heq : (∑ t ∈ s, groupedScalarExponent sizes t) =
      ∑ i : Fin d, groupedScalarExponent sizes (indices i).val := by
    exact Finset.sum_image (by intro i _ l _ hil; exact hinj (Fin.ext hil))
  rw [heq, sum_groupedScalarExponent_prefix sizes hj hjk] at hsum
  exact hsum

end KungTraub
