import KungTraubAppendices.ConfluentRolle
import Mathlib.Data.List.OfFn
import Mathlib.Order.Interval.Finset.Fin

/-! Counting equal nodes without imposing distinctness. -/

namespace KungTraubAppendices

theorem count_ofFn_eq_card_filter {α : Type*} [DecidableEq α]
    {n : ℕ} (x : Fin n → α) (a : α) :
    (List.ofFn x).count a = (Finset.univ.filter (fun i => x i = a)).card := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.count_cons, Fin.sum_univ_succ, ih]
    simp only [beq_iff_eq, add_comm]

/-- A constant block from `i` to `j` contributes at least `j-i+1` copies,
including when it is part of a larger constant block. -/
theorem index_difference_lt_count_of_monotone {n : ℕ} (x : Fin n → ℝ)
    (hx : Monotone x) {i j : Fin n} (hij : i ≤ j) (heq : x i = x j) :
    j.val - i.val < (List.ofFn x).count (x i) := by
  classical
  rw [count_ofFn_eq_card_filter]
  have hsubset : Finset.Icc i j ⊆ Finset.univ.filter (fun k => x k = x i) := by
    intro k hk
    have hb := Finset.mem_Icc.mp hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact le_antisymm ((hx hb.2).trans_eq heq.symm) (hx hb.1)
  have hcard := Finset.card_le_card hsubset
  rw [Fin.card_Icc] at hcard
  have hval := Fin.le_iff_val_le_val.mp hij
  omega

end KungTraubAppendices
