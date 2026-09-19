import appendix_reference.KungTraubAppendices.HermiteLocalOrder

/-! Unstopped observation histories and their relation to actual executions. -/

noncomputable section
open KungTraub
namespace KungTraubAppendices

/-- The successive interpolation histories, before zero-answer stopping is
applied. They use exactly the same observed-data updates as the actual tree. -/
def inverseHermiteHistory (f : ℝ → ℝ) : (j : ℕ) → ℝ → Fin (j + 1) → ℝ
  | 0, x => fun _ => x
  | j + 1, x =>
      let points := inverseHermiteHistory f j x
      Fin.snoc points ((hermiteWithDerivative Finset.univ (fun i => f (points i))
        points 0 (deriv f x)⁻¹).eval 0)

/-- The initial point remains the distinguished point in every history. -/
@[simp] theorem inverseHermiteHistory_zero (f : ℝ → ℝ) (j : ℕ) (x : ℝ) :
    inverseHermiteHistory f j x 0 = x := by
  sorry

/-- A new history preserves every previously computed point. -/
theorem inverseHermiteHistory_castSucc (f : ℝ → ℝ) (j : ℕ) (x : ℝ)
    (i : Fin (j + 1)) :
    inverseHermiteHistory f (j + 1) x i.castSucc = inverseHermiteHistory f j x i := by
  sorry

/-- The final entry of the extended history is the actual polynomial update. -/
theorem inverseHermiteHistory_last (f : ℝ → ℝ) (j : ℕ) (x : ℝ) :
    inverseHermiteHistory f (j + 1) x (Fin.last (j + 1)) =
      (hermiteWithDerivative Finset.univ (fun i => f (inverseHermiteHistory f j x i))
        (inverseHermiteHistory f j x) 0 (deriv f x)⁻¹).eval 0 := by
  sorry

/-- If the queried new entries are nonzero, the actual tail follows this
history. No nonzero test is required at the final unqueried output. -/
theorem inverseHermiteTail_run_eq_history (f : ℝ → ℝ) (x : ℝ)
    (remaining j : ℕ)
    (hnonzero : ∀ k, j + 1 ≤ k → k ≤ j + remaining →
      f (inverseHermiteHistory f k x (Fin.last k)) ≠ 0) :
    (inverseHermiteTail remaining j (fun i => f (inverseHermiteHistory f j x i))
      (inverseHermiteHistory f j x) (deriv f x)⁻¹
      (inverseHermiteHistory f (j + 1) x (Fin.last (j + 1)))).run f =
        inverseHermiteHistory f (j + remaining + 1) x (Fin.last (j + remaining + 1)) := by
  sorry

/-- On a nonzero observation history the actual fixed-slot algorithm has the
same final output, with the initial derivative as its sole derivative query. -/
theorem inverseHermite_run_eq_history (n : ℕ) (hn : 2 ≤ n) (f : ℝ → ℝ) (x : ℝ)
    (hd : deriv f x ≠ 0)
    (hnonzero : ∀ k, k < n - 1 → f (inverseHermiteHistory f k x (Fin.last k)) ≠ 0) :
    (inverseHermiteAlgorithm n).run f x =
      inverseHermiteHistory f (n - 1) x (Fin.last (n - 1)) := by
  sorry

end KungTraubAppendices
