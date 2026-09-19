import KungTraubAppendices.SharpnessDefinitions

/-!
# Elementary properties of the sharpness procedure

Budget and padding identities use `KungTraub.LocalAndStoppingAlgorithms`.
The coefficient identities and positivity give the elementary recurrence
properties used in Appendix A.
-/

noncomputable section

open scoped BigOperators

namespace KungTraubAppendices

/-- Every execution of the concrete stopping tree uses at most its stated budget. -/
theorem inverseHermite_observationCount_le (n : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    ((inverseHermiteMethod n) x).observationCount f ≤ n :=
  KungTraub.BoundedRealTree.observationCount_le _ _

/-- Padding the concrete tree preserves its actual output, including early stops. -/
theorem inverseHermite_run_eq (n : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    (inverseHermiteAlgorithm n).run f x = (inverseHermiteMethod n).run f x :=
  KungTraub.StoppingRealAlgorithm.padded_run_eq _ _ _

/-- The first nontrivial coefficient has the exact value in Appendix A. -/
theorem sharpnessCoefficient_one : sharpnessCoefficient 1 = (1 / 2 : ℝ) := by
  rw [sharpnessCoefficient]
  simp

/-- The recurrence, including its empty-product base at index zero. -/
theorem sharpnessCoefficient_succ (j : ℕ) :
    sharpnessCoefficient (j + 1) =
      (∏ i : Fin j, sharpnessCoefficient (i.val + 1)) / ((j : ℝ) + 2) := by
  rw [sharpnessCoefficient]

/-- Every specified leading coefficient is strictly positive. -/
theorem sharpnessCoefficient_pos (j : ℕ) : 0 < sharpnessCoefficient j := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    cases j with
    | zero => simp [sharpnessCoefficient]
    | succ j =>
      rw [sharpnessCoefficient_succ]
      apply div_pos
      · exact Finset.prod_pos (fun i _ => ih (i.val + 1) (by omega))
      · positivity

/-- With two observations the constructed output is precisely Newton's update.
The equality also describes total extensions at zero values or zero derivatives. -/
theorem inverseHermite_two_run (f : ℝ → ℝ) (x : ℝ) :
    (inverseHermiteAlgorithm 2).run f x = x - f x / deriv f x := by
  rw [inverseHermite_run_eq]
  by_cases hvalue : f x = 0
  · simp [inverseHermiteMethod, KungTraub.StoppingRealAlgorithm.run,
      inverseHermiteTree, KungTraub.BoundedRealTree.run, KungTraub.RealQuery.answer,
      hvalue]
  · by_cases hderiv : deriv f x = 0
    · simp [inverseHermiteMethod, KungTraub.StoppingRealAlgorithm.run,
        inverseHermiteTree, KungTraub.BoundedRealTree.run, KungTraub.RealQuery.answer,
        hvalue, hderiv]
    · simp [inverseHermiteMethod, KungTraub.StoppingRealAlgorithm.run,
        inverseHermiteTree, inverseHermiteTail, KungTraub.BoundedRealTree.run,
        KungTraub.RealQuery.answer, hvalue, hderiv]

end KungTraubAppendices
