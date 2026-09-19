import KungTraub.Definitions
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Exponent identities for the Kung–Traub bound

These supporting statements implement the sequence in equation `eq:B` of
Matthew J. Colbrook's manuscript. The proofs use Mathlib finite-sum identities.
-/

namespace KungTraub

@[simp] theorem orderBound_zero : orderBound 0 = 1 := by
  sorry

@[simp] theorem orderBound_succ (n : ℕ) : orderBound (n + 1) = 2 ^ n := by
  sorry

theorem orderBound_pos (n : ℕ) : 0 < orderBound n := by
  sorry

theorem orderBound_one_le (n : ℕ) : 1 ≤ orderBound n := by
  sorry

/-- The sum of all preceding exponents is the next exponent. -/
theorem sum_orderBound_range_succ (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), orderBound i = orderBound (n + 1) := by
  sorry

theorem sum_orderBound_range {n : ℕ} (hn : 0 < n) :
    ∑ i ∈ Finset.range n, orderBound i = orderBound n := by
  sorry

/-- Distinct observation indices contribute at most the full exponent. -/
theorem sum_orderBound_le {n : ℕ} (hn : 0 < n) (s : Finset ℕ)
    (hs : s ⊆ Finset.range n) :
    ∑ i ∈ s, orderBound i ≤ orderBound n := by
  sorry

end KungTraub
