import appendix_b_reference.KungTraubAppendices.RepeatedRolle
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
  sorry

/-- At the top allowed degree, the derivative is exactly the factorial times
the leading coefficient, including when that coefficient is zero. -/
theorem iterate_derivative_eq_factorial_coeff {n : ℕ} {P : ℝ[X]}
    (hdegree : P.degree ≤ (n : WithBot ℕ)) :
    derivative^[n] P = C ((n.factorial : ℝ) * P.coeff n) := by
  sorry

/-- A monic degree-`n` polynomial has constant `n`th derivative `n!`. -/
theorem iteratedDeriv_monic_polynomial {n : ℕ} {P : ℝ[X]}
    (hmonic : P.Monic) (hdegree : P.natDegree = n) (t : ℝ) :
    iteratedDeriv n (fun z => P.eval z) t = (n.factorial : ℝ) := by
  sorry

/-- The analytic hypotheses needed for every Rolle step are local to the
original interval. -/
theorem analytic_iteratedDeriv_continuousOn {f : ℝ → ℝ} {s : Set ℝ}
    (hf : AnalyticOnNhd ℝ f s) (n : ℕ) :
    ContinuousOn (iteratedDeriv n f) s := by
  sorry

/-- Finite-set form of Rolle with one repeated node and analytic input. -/
theorem analytic_exists_iteratedDeriv_zero_of_double_node (n : ℕ)
    {f : ℝ → ℝ} {a b : ℝ} (hf : AnalyticOnNhd ℝ f (Icc a b))
    (s : Finset ℝ) (hs : s.card = n + 1)
    (hsin : ∀ z ∈ s, z ∈ Icc a b) (hzero : ∀ z ∈ s, f z = 0)
    {r : ℝ} (hr : r ∈ s) (hderiv : deriv f r = 0) :
    ∃ c ∈ Icc a b, iteratedDeriv (n + 1) f c = 0 := by
  sorry

end KungTraubAppendices
