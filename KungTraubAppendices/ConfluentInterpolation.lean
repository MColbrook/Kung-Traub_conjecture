import KungTraubAppendices.NewtonJets
import KungTraubAppendices.NodeMultiplicity

/-!
# The confluent divided-difference mean-value formula

For n+1 nodes, the coefficient of degree n of the Newton interpolant is the divided difference.
Every repeated-node derivative condition is proved from the Newton remainder,
then the full multiplicity version of Rolle gives the exact factorial constant.
-/

noncomputable section

open Polynomial Set

namespace KungTraubAppendices

/-- The Newton interpolation error has precisely the vanishing jets required
by the multiplicities of an ordered list, with arbitrary coincidences. -/
theorem newtonPolynomial_ordered_error_jets {n : ℕ} {f : ℝ → ℝ}
    (x : Fin n → ℝ) (hx : Monotone x) (hf : ∀ i, AnalyticAt ℝ f (x i)) :
    OrderedVanishingJets
      (fun t => f t - (newtonPolynomial f (List.ofFn x)).eval t) x := by
  intro i j hij heq
  exact newtonPolynomial_error_jet_zero (List.ofFn x) (hf i)
    (index_difference_lt_count_of_monotone x hx hij heq)

/-- The exact confluent mean-value formula on the full closed interval, for
`n+1` nodes counted with repetitions. -/
theorem newtonPolynomial_coefficient_mean_value (n : ℕ) {f : ℝ → ℝ} {a b : ℝ}
    (hf : AnalyticOnNhd ℝ f (Icc a b)) (x : Fin (n + 1) → ℝ)
    (hx : Monotone x) (hxin : ∀ i, x i ∈ Icc a b) :
    ∃ c ∈ Icc a b, (newtonPolynomial f (List.ofFn x)).coeff n =
      iteratedDeriv n f c / (n.factorial : ℝ) := by
  let P := newtonPolynomial f (List.ofFn x)
  have hPan : AnalyticOnNhd ℝ (fun t => P.eval t) (Icc a b) :=
    (AnalyticOnNhd.eval_polynomial P).mono (subset_univ _)
  have hEan : AnalyticOnNhd ℝ (fun t => f t - P.eval t) (Icc a b) := hf.sub hPan
  have hjets : OrderedVanishingJets (fun t => f t - P.eval t) x :=
    newtonPolynomial_ordered_error_jets x hx (fun i => hf _ (hxin i))
  obtain ⟨c, hc, hzero⟩ := exists_iteratedDeriv_zero_of_ordered_vanishing_jets
    n x hx hxin hjets (fun k _ => analytic_iteratedDeriv_continuousOn hEan k)
  have hdegree : P.degree ≤ (n : WithBot ℕ) := by
    apply degree_le_natDegree.trans
    have h := newtonPolynomial_natDegree_le f (List.ofFn x)
    simp only [List.length_ofFn, Nat.add_sub_cancel] at h
    exact_mod_cast h
  have hderivP : iteratedDeriv n (fun t => P.eval t) c =
      (n.factorial : ℝ) * P.coeff n := by
    rw [iteratedDeriv_polynomial_eval, iterate_derivative_eq_factorial_coeff hdegree]
    simp
  rw [iteratedDeriv_fun_sub (hf c hc).contDiffAt (hPan c hc).contDiffAt, hderivP] at hzero
  refine ⟨c, hc, ?_⟩
  apply (eq_div_iff (by positivity : (n.factorial : ℝ) ≠ 0)).mpr
  change P.coeff n * (n.factorial : ℝ) = iteratedDeriv n f c
  nlinarith

end KungTraubAppendices
