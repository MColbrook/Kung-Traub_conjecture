import KungTraubAppendices.ConfluentInterpolation

/-! Polynomial determination by arbitrary confluent interpolation conditions. -/

noncomputable section

open Polynomial Set

namespace KungTraubAppendices

/-- A polynomial of degree at most `n` with `n+1` prescribed zeros counted
with multiplicity has vanishing coefficient of degree `n`. -/
theorem polynomial_top_coeff_zero_of_ordered_jets (n : ℕ)
    (x : Fin (n + 1) → ℝ) (hx : Monotone x) {P : ℝ[X]}
    (hdegree : P.degree ≤ (n : WithBot ℕ))
    (hjets : OrderedVanishingJets (fun t => P.eval t) x) : P.coeff n = 0 := by
  have hxin : ∀ i, x i ∈ Icc (x 0) (x (Fin.last n)) := by
    intro i
    exact ⟨hx (Fin.zero_le i), hx (Fin.le_last i)⟩
  have hPan : AnalyticOnNhd ℝ (fun t => P.eval t) (Icc (x 0) (x (Fin.last n))) :=
    (AnalyticOnNhd.eval_polynomial P).mono (subset_univ _)
  obtain ⟨c, _, hc⟩ := exists_iteratedDeriv_zero_of_ordered_vanishing_jets n x hx hxin hjets
    (fun k _ => analytic_iteratedDeriv_continuousOn hPan k)
  rw [iteratedDeriv_polynomial_eval, iterate_derivative_eq_factorial_coeff hdegree] at hc
  have hprod : (n.factorial : ℝ) * P.coeff n = 0 := by simpa using hc
  exact (mul_eq_zero.mp hprod).resolve_left (by positivity)

/-- All coefficients vanish: the complete confluent interpolation conditions
determine a polynomial of degree at most `n` uniquely. -/
theorem polynomial_eq_zero_of_ordered_jets (n : ℕ)
    (x : Fin (n + 1) → ℝ) (hx : Monotone x) {P : ℝ[X]}
    (hdegree : P.degree ≤ (n : WithBot ℕ))
    (hjets : OrderedVanishingJets (fun t => P.eval t) x) : P = 0 := by
  induction n with
  | zero =>
    have hcoeff := polynomial_top_coeff_zero_of_ordered_jets 0 x hx hdegree hjets
    rw [eq_C_of_degree_le_zero hdegree, hcoeff, C_0]
  | succ n ih =>
    have hcoeff := polynomial_top_coeff_zero_of_ordered_jets (n + 1) x hx hdegree hjets
    have hdegree' : P.degree ≤ (n : WithBot ℕ) := by
      apply (degree_le_iff_coeff_zero P _).mpr
      intro m hm
      have hm' : n < m := by exact_mod_cast hm
      by_cases hmn : m = n + 1
      · simpa [hmn] using hcoeff
      · exact coeff_eq_zero_of_degree_lt (hdegree.trans_lt
          (by exact_mod_cast (show n + 1 < m by omega)))
    let y : Fin (n + 1) → ℝ := fun i => x i.castSucc
    have hy : Monotone y := fun i j hij => hx (by exact hij)
    have hyjets : OrderedVanishingJets (fun t => P.eval t) y := by
      intro i j hij heq
      exact hjets i.castSucc j.castSucc (by exact hij) heq
    exact ih y hy hdegree' hyjets

/-- The Newton polynomial is the unique polynomial satisfying all prescribed
derivatives at all nodes, including arbitrarily repeated nodes. -/
theorem newtonPolynomial_unique (n : ℕ) {f : ℝ → ℝ}
    (x : Fin (n + 1) → ℝ) (hx : Monotone x) (hf : ∀ i, AnalyticAt ℝ f (x i))
    {P : ℝ[X]} (hdegree : P.degree ≤ (n : WithBot ℕ))
    (hdata : ∀ i (k : ℕ), k < (List.ofFn x).count (x i) →
      iteratedDeriv k (fun t => P.eval t) (x i) = iteratedDeriv k f (x i)) :
    P = newtonPolynomial f (List.ofFn x) := by
  let Q := newtonPolynomial f (List.ofFn x)
  have hQdegree : Q.degree ≤ (n : WithBot ℕ) := by
    apply degree_le_natDegree.trans
    have h := newtonPolynomial_natDegree_le f (List.ofFn x)
    simp only [List.length_ofFn, Nat.add_sub_cancel] at h
    exact_mod_cast h
  apply sub_eq_zero.mp
  apply polynomial_eq_zero_of_ordered_jets n x hx
    ((degree_sub_le P Q).trans (max_le hdegree hQdegree))
  intro i j hij heq
  have hcount := index_difference_lt_count_of_monotone x hx hij heq
  have hPa : AnalyticAt ℝ (fun t => P.eval t) (x i) :=
    AnalyticOnNhd.eval_polynomial P _ (mem_univ _)
  have hQa : AnalyticAt ℝ (fun t => Q.eval t) (x i) :=
    AnalyticOnNhd.eval_polynomial Q _ (mem_univ _)
  have hfun : (fun t => (P - Q).eval t) = fun t => P.eval t - Q.eval t := by
    funext t
    exact Polynomial.eval_sub P Q t
  rw [hfun, iteratedDeriv_fun_sub hPa.contDiffAt hQa.contDiffAt,
    hdata i _ hcount, newtonPolynomial_jet_eq (List.ofFn x) (hf i) hcount, sub_self]

end KungTraubAppendices
