import KungTraubAppendices.HermiteInterpolation

/-!
# Uniqueness of the inverse Hermite interpolant

After one linear factor is removed, the derivative condition supplies the
missing value condition. Mathlib's indexed polynomial determination theorem
then applies. This argument works over every field.
-/

noncomputable section

open Polynomial

namespace KungTraubAppendices

variable {𝕜 ι : Type*} [Field 𝕜] [DecidableEq ι]

/-- A polynomial with these values and derivative cannot have degree at most
the number of distinct nodes unless it vanishes identically. -/
theorem eq_zero_of_values_and_derivative_zero {s : Finset ι} {nodes : ι → 𝕜}
    (hnodes : Set.InjOn nodes s) {i : ι} (hi : i ∈ s) {P : 𝕜[X]}
    (hdegree : P.degree ≤ (s.card : WithBot ℕ))
    (hvalues : ∀ j ∈ s, P.eval (nodes j) = 0)
    (hderivative : P.derivative.eval (nodes i) = 0) : P = 0 := by
  obtain ⟨Q, hQ⟩ := dvd_iff_isRoot.mpr (hvalues i hi)
  by_cases hzero : Q = 0
  · simp [hQ, hzero]
  have hdegreeQ : Q.degree < (s.card : WithBot ℕ) := by
    rw [hQ, degree_mul, degree_X_sub_C, degree_eq_natDegree hzero] at hdegree
    have hnat : 1 + Q.natDegree ≤ s.card := by exact_mod_cast hdegree
    rw [degree_eq_natDegree hzero]
    exact_mod_cast (show Q.natDegree < s.card by omega)
  have hvaluesQ : ∀ j ∈ s, Q.eval (nodes j) = 0 := by
    intro j hj
    by_cases heq : j = i
    · subst j
      simpa [hQ, derivative_mul] using hderivative
    · have hfactor : nodes j - nodes i ≠ 0 :=
        sub_ne_zero.mpr (fun h => heq (hnodes hj hi h))
      have hprod := hvalues j hj
      simpa only [hQ, eval_mul, eval_sub, eval_X, eval_C,
        mul_eq_zero, hfactor, false_or] using hprod
  have := eq_zero_of_degree_lt_of_eval_index_eq_zero s hnodes hdegreeQ hvaluesQ
  simp [hQ, this]

/-- The explicit inverse Hermite interpolant is uniquely determined by its
degree, all supplied values, and the single supplied derivative. -/
theorem hermiteWithDerivative_unique {s : Finset ι} {nodes : ι → 𝕜}
    (values : ι → 𝕜) (d : 𝕜) (hnodes : Set.InjOn nodes s)
    {i : ι} (hi : i ∈ s) {P : 𝕜[X]}
    (hdegree : P.degree ≤ (s.card : WithBot ℕ))
    (hvalues : ∀ j ∈ s, P.eval (nodes j) = values j)
    (hderivative : P.derivative.eval (nodes i) = d) :
    P = hermiteWithDerivative s nodes values i d := by
  apply sub_eq_zero.mp
  apply eq_zero_of_values_and_derivative_zero hnodes hi
  · exact degree_sub_le _ _ |>.trans
      (max_le hdegree (hermiteWithDerivative_degree_le values i d hnodes))
  · intro j hj
    simp only [eval_sub, hvalues j hj,
      hermiteWithDerivative_eval values i d hnodes hj, sub_self]
  · simp only [derivative_sub, eval_sub, hderivative,
      hermiteWithDerivative_derivative values d hnodes hi, sub_self]

/-- Existence and uniqueness include the same full degree bound as the paper. -/
theorem existsUnique_hermiteWithDerivative {s : Finset ι} {nodes : ι → 𝕜}
    (values : ι → 𝕜) (d : 𝕜) (hnodes : Set.InjOn nodes s)
    {i : ι} (hi : i ∈ s) :
    ∃! P : 𝕜[X], P.degree ≤ (s.card : WithBot ℕ) ∧
      (∀ j ∈ s, P.eval (nodes j) = values j) ∧
      P.derivative.eval (nodes i) = d := by
  refine ⟨hermiteWithDerivative s nodes values i d, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact hermiteWithDerivative_degree_le values i d hnodes
  · exact fun j hj => hermiteWithDerivative_eval values i d hnodes hj
  · exact hermiteWithDerivative_derivative values d hnodes hi
  · intro P hP
    exact hermiteWithDerivative_unique values d hnodes hi hP.1 hP.2.1 hP.2.2

end KungTraubAppendices
