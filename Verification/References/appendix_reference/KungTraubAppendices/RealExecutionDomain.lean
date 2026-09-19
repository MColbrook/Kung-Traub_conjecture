import appendix_reference.KungTraubAppendices.SharpnessDefinitions

/-! Domain admissibility for actual stopping executions and their idle padding. -/

namespace KungTraubAppendices

open KungTraub

/-- Only the branch selected by the actual answer is executed. A stopped
tree makes no further queries, and an idle query has no location. -/
def realTreeExecutionIn : {n : ℕ} → BoundedRealTree n → (ℝ → ℝ) → Set ℝ → Prop
  | _, .stop _, _, _ => True
  | _, .observe q next, f, U =>
      (match q with | .derivative z _ => z ∈ U | .idle => True) ∧
        realTreeExecutionIn (next (q.answer f)) f U

/-- Every fixed-slot query obtained by padding an admissible stopping
execution is either idle or located in the original domain. -/
theorem realTreeExecutionIn_paddedQuery {n : ℕ} {tree : BoundedRealTree n}
    {f : ℝ → ℝ} {U : Set ℝ} (h : realTreeExecutionIn tree f U) (j : Fin n) :
    match tree.paddedQuery j
        (scalarPrefixRestriction (tree.paddedAnswers f) j.val j.isLt.le) with
    | .derivative z _ => z ∈ U
    | .idle => True := by
  sorry

/-- Domain admissibility is preserved by padding the stopping execution. -/
theorem realExecutionIn_of_tree_execution {n : ℕ} (A : StoppingRealAlgorithm n)
    {f : ℝ → ℝ} {x : ℝ} {U : Set ℝ} (h : realTreeExecutionIn (A x) f U) :
    realExecutionIn A.padded f x U := by
  sorry

end KungTraubAppendices
