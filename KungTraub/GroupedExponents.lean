import KungTraub.Definitions
import Mathlib.Tactic

/-!
# Exact exponents for prescribed groups

Groups are indexed from zero;
`groupedStageExponent sizes j` is the exponent after the first j complete groups.
The finite schedule is extended by zero only to obtain a total natural-indexed
function. The sharper grouped threshold is proved equal to `groupedOrderBound`.
The proofs use Mathlib finite-product and finite-sum identities.
-/

namespace KungTraub
open scoped BigOperators

def groupSizeAt {k : ℕ} (sizes : Fin k → ℕ) (i : ℕ) : ℕ :=
  if hi : i < k then sizes ⟨i, hi⟩ else 0

theorem groupSizeAt_of_lt {k : ℕ} (sizes : Fin k → ℕ) {i : ℕ} (hi : i < k) :
    groupSizeAt sizes i = sizes ⟨i, hi⟩ := by simp [groupSizeAt, hi]

theorem groupSizeAt_of_le {k : ℕ} (sizes : Fin k → ℕ) {i : ℕ} (hi : k ≤ i) :
    groupSizeAt sizes i = 0 := by simp [groupSizeAt, Nat.not_lt.mpr hi]

def groupedStageExponent {k : ℕ} (sizes : Fin k → ℕ) (j : ℕ) : ℕ :=
  ∏ i ∈ Finset.range j, if i = 0 then groupSizeAt sizes i else groupSizeAt sizes i + 1

@[simp] theorem groupedStageExponent_zero {k : ℕ} (sizes : Fin k → ℕ) :
    groupedStageExponent sizes 0 = 1 := by simp [groupedStageExponent]

theorem groupedStageExponent_one {k : ℕ} (sizes : Fin k → ℕ) (hk : 0 < k) :
    groupedStageExponent sizes 1 = sizes ⟨0, hk⟩ := by
  simp [groupedStageExponent, groupSizeAt, hk]

theorem groupedStageExponent_succ {k : ℕ} (sizes : Fin k → ℕ) {j : ℕ}
    (hj : 0 < j) (hjk : j < k) :
    groupedStageExponent sizes (j + 1) =
      (sizes ⟨j, hjk⟩ + 1) * groupedStageExponent sizes j := by
  simp [groupedStageExponent, Finset.prod_range_succ, Nat.ne_of_gt hj,
    groupSizeAt_of_lt sizes hjk, mul_comm]

theorem groupedStageExponent_pos {k : ℕ} (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 0 < sizes i) {j : ℕ} (hj : j ≤ k) :
    0 < groupedStageExponent sizes j := by
  apply Finset.prod_pos
  intro i hi
  have hik : i < k := (Finset.mem_range.mp hi).trans_le hj
  split_ifs
  · rw [groupSizeAt_of_lt sizes hik]
    exact hsizes _
  · exact Nat.succ_pos _

theorem groupedStageExponent_one_le {k : ℕ} (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 0 < sizes i) {j : ℕ} (hj : j ≤ k) :
    1 ≤ groupedStageExponent sizes j := groupedStageExponent_pos sizes hsizes hj

/-- The full weighted sum uses the exponent before each group, including C_0=1. -/
theorem groupedStageExponent_eq_weighted_sum {k : ℕ} (sizes : Fin k → ℕ)
    {j : ℕ} (hj : 0 < j) (hjk : j ≤ k) :
    groupedStageExponent sizes j =
      ∑ i ∈ Finset.range j, groupSizeAt sizes i * groupedStageExponent sizes i := by
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases hj0 : j = 0
    · subst j
      simp [groupedStageExponent, groupSizeAt]
    · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
      rw [groupedStageExponent_succ sizes hjpos (by omega), Finset.sum_range_succ,
        ← ih hjpos (by omega), groupSizeAt_of_lt sizes (by omega : j < k)]
      ring

theorem groupedStageExponent_eq_groupedOrderBound {k : ℕ} (sizes : Fin k → ℕ) :
    groupedStageExponent sizes k = groupedOrderBound sizes := by
  have hprod := Fin.prod_univ_eq_prod_range
    (fun i => if i = 0 then groupSizeAt sizes i else groupSizeAt sizes i + 1) k
  rw [groupedStageExponent, ← hprod, groupedOrderBound]
  apply Finset.prod_congr rfl
  intro i _
  rw [groupSizeAt_of_lt sizes i.isLt]

/-- At most the prescribed number of rank increments from each group contributes
at most the grouped exponent. -/
theorem grouped_weighted_count_le {k : ℕ} (sizes : Fin k → ℕ) {j : ℕ}
    (hj : 0 < j) (hjk : j ≤ k) (count : ℕ → ℕ)
    (hcount : ∀ i < j, count i ≤ groupSizeAt sizes i) :
    ∑ i ∈ Finset.range j, count i * groupedStageExponent sizes i ≤ groupedStageExponent sizes j := by
  rw [groupedStageExponent_eq_weighted_sum sizes hj hjk]
  exact Finset.sum_le_sum (fun i hi => Nat.mul_le_mul_right _ (hcount i (Finset.mem_range.mp hi)))

def groupedPrefixCount {k : ℕ} (sizes : Fin k → ℕ) (j : ℕ) : ℕ :=
  ∑ i ∈ Finset.range j, groupSizeAt sizes i

@[simp] theorem groupedPrefixCount_zero {k : ℕ} (sizes : Fin k → ℕ) :
    groupedPrefixCount sizes 0 = 0 := by simp [groupedPrefixCount]

theorem groupedPrefixCount_succ {k : ℕ} (sizes : Fin k → ℕ) {j : ℕ} (hj : j < k) :
    groupedPrefixCount sizes (j + 1) = groupedPrefixCount sizes j + sizes ⟨j, hj⟩ := by
  simp [groupedPrefixCount, Finset.sum_range_succ, groupSizeAt_of_lt sizes hj]

theorem groupedPrefixCount_eq_total {k : ℕ} (sizes : Fin k → ℕ) :
    groupedPrefixCount sizes k = groupedObservationCount sizes := by
  rw [groupedPrefixCount, ← Fin.sum_univ_eq_sum_range (groupSizeAt sizes), groupedObservationCount]
  apply Finset.sum_congr rfl
  intro i _
  exact groupSizeAt_of_lt sizes i.isLt

theorem groupedPrefixCount_mono {k : ℕ} (sizes : Fin k → ℕ) : Monotone (groupedPrefixCount sizes) := by
  intro i j hij
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hij) (by intros; exact Nat.zero_le _)

theorem groupedPrefixCount_le_total {k : ℕ} (sizes : Fin k → ℕ) {j : ℕ} (hj : j ≤ k) :
    groupedPrefixCount sizes j ≤ groupedObservationCount sizes := by
  rw [← groupedPrefixCount_eq_total]
  exact groupedPrefixCount_mono sizes hj

end KungTraub
