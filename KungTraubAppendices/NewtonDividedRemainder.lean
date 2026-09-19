import KungTraubAppendices.ConfluentPermutation

/-! The Newton remainder coefficient is the canonical divided difference. -/

noncomputable section

open Polynomial Set

namespace KungTraubAppendices

/-- Appending the evaluation node exposes precisely the next Newton
coefficient, even if some or all of the nodes coincide. -/
theorem newtonPolynomial_append_coeff (f : ℝ → ℝ) (xs : List ℝ) (t : ℝ) :
    (newtonPolynomial f (xs ++ [t])).coeff xs.length = newtonRemainderFunction f xs t := by
  induction xs generalizing f with
  | nil => simp [newtonPolynomial, newtonRemainderFunction]
  | cons a xs ih =>
    have hdegree : (newtonPolynomial (dslope f a) (xs ++ [t])).natDegree ≤ xs.length := by
      simpa using newtonPolynomial_natDegree_le (dslope f a) (xs ++ [t])
    have hzero : (newtonPolynomial (dslope f a) (xs ++ [t])).coeff (xs.length + 1) = 0 :=
      coeff_eq_zero_of_natDegree_lt (by omega)
    simp only [List.cons_append, newtonPolynomial, List.length_cons, coeff_add,
      coeff_C_succ, zero_add, coeff_X_sub_C_mul, hzero, mul_zero, sub_zero,
      newtonRemainderFunction]
    exact ih (dslope f a)

/-- The successive-slope remainder is the canonical divided difference with
the evaluation point as one further node. -/
theorem newtonRemainderFunction_eq_dividedDifference {f : ℝ → ℝ}
    (xs : List ℝ) (t : ℝ) (hf : ∀ z ∈ t :: xs, AnalyticAt ℝ f z) :
    newtonRemainderFunction f xs t = confluentDividedDifference f (t :: xs) := by
  have hperm : (t :: xs).Perm (xs ++ [t]) := by
    exact (show ([t] ++ xs).Perm (xs ++ [t]) from List.perm_append_comm)
  rw [confluentDividedDifference_perm f hperm,
    confluentDividedDifference_eq_coeff (xs ++ [t])
      (fun z hz => hf z (hperm.mem_iff.mpr hz))]
  simpa using (newtonPolynomial_append_coeff f xs t).symm

/-- The exact remainder uses this same divided difference, with repetitions
retained, including coincident nodes. -/
theorem newtonPolynomial_dividedDifference_remainder {f : ℝ → ℝ}
    (xs : List ℝ) (t : ℝ) (hf : ∀ z ∈ t :: xs, AnalyticAt ℝ f z) :
    f t - (newtonPolynomial f xs).eval t =
      confluentDividedDifference f (t :: xs) * (xs.map (fun a => t - a)).prod := by
  rw [newtonPolynomial_remainder, newtonRemainderFunction_eq_dividedDifference xs t hf]
  exact mul_comm _ _

end KungTraubAppendices
