import appendix_b_reference.KungTraubAppendices.ConfluentRolle
import Mathlib.Data.List.OfFn
import Mathlib.Order.Interval.Finset.Fin

/-! Counting equal nodes without imposing distinctness. -/

namespace KungTraubAppendices

theorem count_ofFn_eq_card_filter {α : Type*} [DecidableEq α]
    {n : ℕ} (x : Fin n → α) (a : α) :
    (List.ofFn x).count a = (Finset.univ.filter (fun i => x i = a)).card := by
  sorry

/-- A constant block from `i` to `j` contributes at least `j-i+1` copies,
including when it is part of a larger constant block. -/
theorem index_difference_lt_count_of_monotone {n : ℕ} (x : Fin n → ℝ)
    (hx : Monotone x) {i j : Fin n} (hij : i ≤ j) (heq : x i = x j) :
    j.val - i.val < (List.ofFn x).count (x i) := by
  sorry

end KungTraubAppendices
