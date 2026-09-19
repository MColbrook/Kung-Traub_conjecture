import KungTraubAppendices.RepeatedRolle
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Calculus prerequisites for the confluent remainder

The factorial normalization follows from Mathlib's coefficient formula for
iterated polynomial derivatives. The repeated Rolle argument remains on the
given closed interval; analyticity is only required near that interval.
-/

noncomputable section

open Polynomial Set

namespace KungTraubAppendices

/-- Algebraic and analytic iterated polynomial derivatives agree. -/
theorem iteratedDeriv_polynomial_eval (n : ℕ) (P : ℝ[X]) :
    iteratedDeriv n (fun t => P.eval t) = fun t => (derivative^[n] P).eval t := by
  induction n generalizing P with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ']
    have hd : deriv (fun t => P.eval t) = fun t => P.derivative.eval t :=
      funext (fun _ => P.deriv)
    rw [hd, ih, Function.iterate_succ_apply]

/-- At the top allowed degree, the derivative is exactly the factorial times
the leading coefficient, including when that coefficient is zero. -/
theorem iterate_derivative_eq_factorial_coeff {n : ℕ} {P : ℝ[X]}
    (hdegree : P.degree ≤ (n : WithBot ℕ)) :
    derivative^[n] P = C ((n.factorial : ℝ) * P.coeff n) := by
  ext m
  cases m with
  | zero => simp [coeff_iterate_derivative, Nat.descFactorial_self]
  | succ m =>
    have hlt : P.degree < ((m + 1 + n : ℕ) : WithBot ℕ) :=
      hdegree.trans_lt (by exact_mod_cast (show n < m + 1 + n by omega))
    simp [coeff_iterate_derivative, coeff_eq_zero_of_degree_lt hlt]

/-- A monic degree-`n` polynomial has constant `n`th derivative `n!`. -/
theorem iteratedDeriv_monic_polynomial {n : ℕ} {P : ℝ[X]}
    (hmonic : P.Monic) (hdegree : P.natDegree = n) (t : ℝ) :
    iteratedDeriv n (fun z => P.eval z) t = (n.factorial : ℝ) := by
  rw [iteratedDeriv_polynomial_eval, iterate_derivative_eq_factorial_coeff
    (by rw [← hdegree]; exact degree_le_natDegree)]
  simp only [eval_C]
  rw [← hdegree, coeff_natDegree, hmonic.leadingCoeff, mul_one]

/-- The analytic hypotheses needed for every Rolle step are local to the
original interval. -/
theorem analytic_iteratedDeriv_continuousOn {f : ℝ → ℝ} {s : Set ℝ}
    (hf : AnalyticOnNhd ℝ f s) (n : ℕ) :
    ContinuousOn (iteratedDeriv n f) s := by
  rw [iteratedDeriv_eq_iterate]
  exact (hf.iterated_deriv n).continuousOn

/-- Finite-set form of Rolle with one repeated node and analytic input. -/
theorem analytic_exists_iteratedDeriv_zero_of_double_node (n : ℕ)
    {f : ℝ → ℝ} {a b : ℝ} (hf : AnalyticOnNhd ℝ f (Icc a b))
    (s : Finset ℝ) (hs : s.card = n + 1)
    (hsin : ∀ z ∈ s, z ∈ Icc a b) (hzero : ∀ z ∈ s, f z = 0)
    {r : ℝ} (hr : r ∈ s) (hderiv : deriv f r = 0) :
    ∃ c ∈ Icc a b, iteratedDeriv (n + 1) f c = 0 := by
  have hrange : r ∈ Set.range (s.orderEmbOfFin hs) := by
    rw [Finset.range_orderEmbOfFin]
    exact hr
  obtain ⟨i, hi⟩ := hrange
  exact exists_iteratedDeriv_zero_of_derivative_zero n (s.orderEmbOfFin hs)
    (s.orderEmbOfFin hs).strictMono
    (fun j => hsin _ (s.orderEmbOfFin_mem hs j))
    (fun j => hzero _ (s.orderEmbOfFin_mem hs j)) i (by simpa [hi] using hderiv)
    (fun k _ => analytic_iteratedDeriv_continuousOn hf k)

end KungTraubAppendices
