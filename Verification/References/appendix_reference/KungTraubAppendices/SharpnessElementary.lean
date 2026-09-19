import appendix_reference.KungTraubAppendices.SharpnessDefinitions

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
    ((inverseHermiteMethod n) x).observationCount f ≤ n := by
  sorry

/-- Padding the concrete tree preserves its actual output, including early stops. -/
theorem inverseHermite_run_eq (n : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    (inverseHermiteAlgorithm n).run f x = (inverseHermiteMethod n).run f x := by
  sorry

/-- The first nontrivial coefficient has the exact value in Appendix A. -/
theorem sharpnessCoefficient_one : sharpnessCoefficient 1 = (1 / 2 : ℝ) := by
  sorry

/-- The recurrence, including its empty-product base at index zero. -/
theorem sharpnessCoefficient_succ (j : ℕ) :
    sharpnessCoefficient (j + 1) =
      (∏ i : Fin j, sharpnessCoefficient (i.val + 1)) / ((j : ℝ) + 2) := by
  sorry

/-- Every specified leading coefficient is strictly positive. -/
theorem sharpnessCoefficient_pos (j : ℕ) : 0 < sharpnessCoefficient j := by
  sorry

/-- With two observations the constructed output is precisely Newton's update.
The equality also describes total extensions at zero values or zero derivatives. -/
theorem inverseHermite_two_run (f : ℝ → ℝ) (x : ℝ) :
    (inverseHermiteAlgorithm 2).run f x = x - f x / deriv f x := by
  sorry

end KungTraubAppendices
