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
    groupSizeAt sizes i = sizes ⟨i, hi⟩ := by
  sorry

theorem groupSizeAt_of_le {k : ℕ} (sizes : Fin k → ℕ) {i : ℕ} (hi : k ≤ i) :
    groupSizeAt sizes i = 0 := by
  sorry

def groupedStageExponent {k : ℕ} (sizes : Fin k → ℕ) (j : ℕ) : ℕ :=
  ∏ i ∈ Finset.range j, if i = 0 then groupSizeAt sizes i else groupSizeAt sizes i + 1

@[simp] theorem groupedStageExponent_zero {k : ℕ} (sizes : Fin k → ℕ) :
    groupedStageExponent sizes 0 = 1 := by
  sorry

theorem groupedStageExponent_one {k : ℕ} (sizes : Fin k → ℕ) (hk : 0 < k) :
    groupedStageExponent sizes 1 = sizes ⟨0, hk⟩ := by
  sorry

theorem groupedStageExponent_succ {k : ℕ} (sizes : Fin k → ℕ) {j : ℕ}
    (hj : 0 < j) (hjk : j < k) :
    groupedStageExponent sizes (j + 1) =
      (sizes ⟨j, hjk⟩ + 1) * groupedStageExponent sizes j := by
  sorry

theorem groupedStageExponent_pos {k : ℕ} (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 0 < sizes i) {j : ℕ} (hj : j ≤ k) :
    0 < groupedStageExponent sizes j := by
  sorry

theorem groupedStageExponent_one_le {k : ℕ} (sizes : Fin k → ℕ)
    (hsizes : ∀ i, 0 < sizes i) {j : ℕ} (hj : j ≤ k) :
    1 ≤ groupedStageExponent sizes j := by
  sorry

/-- The full weighted sum uses the exponent before each group, including C_0=1. -/
theorem groupedStageExponent_eq_weighted_sum {k : ℕ} (sizes : Fin k → ℕ)
    {j : ℕ} (hj : 0 < j) (hjk : j ≤ k) :
    groupedStageExponent sizes j =
      ∑ i ∈ Finset.range j, groupSizeAt sizes i * groupedStageExponent sizes i := by
  sorry

theorem groupedStageExponent_eq_groupedOrderBound {k : ℕ} (sizes : Fin k → ℕ) :
    groupedStageExponent sizes k = groupedOrderBound sizes := by
  sorry

/-- At most the prescribed number of rank increments from each group contributes
at most the grouped exponent. -/
theorem grouped_weighted_count_le {k : ℕ} (sizes : Fin k → ℕ) {j : ℕ}
    (hj : 0 < j) (hjk : j ≤ k) (count : ℕ → ℕ)
    (hcount : ∀ i < j, count i ≤ groupSizeAt sizes i) :
    ∑ i ∈ Finset.range j, count i * groupedStageExponent sizes i ≤ groupedStageExponent sizes j := by
  sorry

def groupedPrefixCount {k : ℕ} (sizes : Fin k → ℕ) (j : ℕ) : ℕ :=
  ∑ i ∈ Finset.range j, groupSizeAt sizes i

@[simp] theorem groupedPrefixCount_zero {k : ℕ} (sizes : Fin k → ℕ) :
    groupedPrefixCount sizes 0 = 0 := by
  sorry

theorem groupedPrefixCount_succ {k : ℕ} (sizes : Fin k → ℕ) {j : ℕ} (hj : j < k) :
    groupedPrefixCount sizes (j + 1) = groupedPrefixCount sizes j + sizes ⟨j, hj⟩ := by
  sorry

theorem groupedPrefixCount_eq_total {k : ℕ} (sizes : Fin k → ℕ) :
    groupedPrefixCount sizes k = groupedObservationCount sizes := by
  sorry

theorem groupedPrefixCount_mono {k : ℕ} (sizes : Fin k → ℕ) : Monotone (groupedPrefixCount sizes) := by
  sorry

theorem groupedPrefixCount_le_total {k : ℕ} (sizes : Fin k → ℕ) {j : ℕ} (hj : j ≤ k) :
    groupedPrefixCount sizes j ≤ groupedObservationCount sizes := by
  sorry

end KungTraub
