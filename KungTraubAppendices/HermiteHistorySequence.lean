import KungTraubAppendices.HermiteLocalOrder

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
  induction j with
  | zero => rfl
  | succ j ih => simpa only [inverseHermiteHistory, Fin.snoc_apply_zero] using ih

/-- A new history preserves every previously computed point. -/
theorem inverseHermiteHistory_castSucc (f : ℝ → ℝ) (j : ℕ) (x : ℝ)
    (i : Fin (j + 1)) :
    inverseHermiteHistory f (j + 1) x i.castSucc = inverseHermiteHistory f j x i := by
  simp only [inverseHermiteHistory, Fin.snoc_castSucc]

/-- The final entry of the extended history is the actual polynomial update. -/
theorem inverseHermiteHistory_last (f : ℝ → ℝ) (j : ℕ) (x : ℝ) :
    inverseHermiteHistory f (j + 1) x (Fin.last (j + 1)) =
      (hermiteWithDerivative Finset.univ (fun i => f (inverseHermiteHistory f j x i))
        (inverseHermiteHistory f j x) 0 (deriv f x)⁻¹).eval 0 := by
  simp only [inverseHermiteHistory, Fin.snoc_last]

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
  induction remaining generalizing j with
  | zero => rfl
  | succ remaining ih =>
    have hz := hnonzero (j + 1) le_rfl (by omega)
    simp only [inverseHermiteTail, BoundedRealTree.run, RealQuery.answer,
      iteratedDeriv_zero, if_neg hz]
    have hext : Fin.snoc (inverseHermiteHistory f j x)
        (inverseHermiteHistory f (j + 1) x (Fin.last (j + 1))) =
        inverseHermiteHistory f (j + 1) x := by
      rw [inverseHermiteHistory_last]
      rfl
    have hvalues : Fin.snoc (fun i => f (inverseHermiteHistory f j x i))
        (f (inverseHermiteHistory f (j + 1) x (Fin.last (j + 1)))) =
        fun i => f (inverseHermiteHistory f (j + 1) x i) := by
      simpa only [hext, Function.comp_def] using
        (Fin.comp_snoc f (inverseHermiteHistory f j x)
          (inverseHermiteHistory f (j + 1) x (Fin.last (j + 1)))).symm
    rw [hext, hvalues, ← inverseHermiteHistory_last]
    have h := ih (j + 1) (fun k hlow hhigh => hnonzero k (by omega) (by omega))
    convert h using 1
    congr 2 <;> omega

/-- On a nonzero observation history the actual fixed-slot algorithm has the
same final output, with the initial derivative as its sole derivative query. -/
theorem inverseHermite_run_eq_history (n : ℕ) (hn : 2 ≤ n) (f : ℝ → ℝ) (x : ℝ)
    (hd : deriv f x ≠ 0)
    (hnonzero : ∀ k, k < n - 1 → f (inverseHermiteHistory f k x (Fin.last k)) ≠ 0) :
    (inverseHermiteAlgorithm n).run f x =
      inverseHermiteHistory f (n - 1) x (Fin.last (n - 1)) := by
  obtain ⟨k, hk⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  subst n
  have hz : f x ≠ 0 := hnonzero 0 (by omega)
  rw [inverseHermite_run_eq]
  simp only [inverseHermiteMethod, StoppingRealAlgorithm.run, inverseHermiteTree,
    BoundedRealTree.run, RealQuery.answer, iteratedDeriv_zero, iteratedDeriv_one,
    if_neg hz, if_neg hd]
  have h := inverseHermiteTail_run_eq_history f x k 0
    (fun i _ hi => hnonzero i (by omega))
  have hfirst : inverseHermiteHistory f 1 x (Fin.last 1) = x - f x / deriv f x := by
    rw [inverseHermiteHistory_last]
    change (hermiteWithDerivative Finset.univ (fun _ : Fin 1 => f x)
      (fun _ : Fin 1 => x) 0 (deriv f x)⁻¹).eval 0 = _
    exact hermite_initial_eval f x
  rw [hfirst] at h
  have hindex : k + 2 - 1 = k + 1 := by omega
  have hindex2 : 0 + k + 1 = k + 1 := by omega
  rw [hindex2] at h
  rw [hindex]
  exact h

end KungTraubAppendices
