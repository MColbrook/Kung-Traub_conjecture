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
  simp [orderBound]

@[simp] theorem orderBound_succ (n : ℕ) : orderBound (n + 1) = 2 ^ n := by
  simp [orderBound]

theorem orderBound_pos (n : ℕ) : 0 < orderBound n := by
  cases n with
  | zero => simp
  | succ n => simp

theorem orderBound_one_le (n : ℕ) : 1 ≤ orderBound n :=
  orderBound_pos n

/-- The sum of all preceding exponents is the next exponent. -/
theorem sum_orderBound_range_succ (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), orderBound i = orderBound (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [orderBound_succ]
    rw [pow_succ]
    omega

theorem sum_orderBound_range {n : ℕ} (hn : 0 < n) :
    ∑ i ∈ Finset.range n, orderBound i = orderBound n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact sum_orderBound_range_succ m

/-- Distinct observation indices contribute at most the full exponent. -/
theorem sum_orderBound_le {n : ℕ} (hn : 0 < n) (s : Finset ℕ)
    (hs : s ⊆ Finset.range n) :
    ∑ i ∈ s, orderBound i ≤ orderBound n := by
  rw [← sum_orderBound_range hn]
  exact Finset.sum_le_sum_of_subset_of_nonneg hs (by
    intro i _ _
    exact Nat.zero_le _)

end KungTraub
