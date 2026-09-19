import KungTraub.Consequences
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Real analyticity of entire restrictions

Entire real-type functions belong to the whole-line real-analytic class.
Mathlib's complex differentiability theorem, in the Cauchy integral module by Yury Kudryashov,
gives `ContDiff` at the analytic order `ω`. The real restriction theorem by Sébastien Gouëzel
and Yourong Zang preserves that order, and `ContDiffAt.analyticAt` gives real analyticity.
An entire counterexample therefore also excludes universal order on the real-analytic class.
-/

open scoped ContDiff

namespace KungTraub

/-- The real part of an entire function restricted to the real line is real analytic.
This fact does not require the entire function itself to be real-valued on the real line. -/
theorem analyticAt_realRestriction_of_differentiable {F : ℂ → ℂ}
    (hF : Differentiable ℂ F) (x : ℝ) : AnalyticAt ℝ (realRestriction F) x := by
  exact ((hF.contDiff : ContDiff ℂ ω F).real_of_complex.contDiffAt).analyticAt

/-- Every entire real-type input belongs to the whole-line real-analytic class. -/
theorem EntireRealType.analyticAt_realRestriction {F : ℂ → ℂ}
    (hF : EntireRealType F) (x : ℝ) : AnalyticAt ℝ (realRestriction F) x :=
  analyticAt_realRestriction_of_differentiable hF.1 x

/-- Universal order on the whole-line real-analytic class implies the same property on
the entire real-type class. -/
theorem AnalyticUniversalLocalOrder.entireUniversalLocalOrder {T : RealUpdate} {p : ℝ}
    (h : AnalyticUniversalLocalOrder T p) : EntireUniversalLocalOrder T p := by
  intro F hF α hα
  exact h (realRestriction F) hF.analyticAt_realRestriction α hα

/-- A full entire counterexample also rules out universal local order on the whole-line
real-analytic class. -/
theorem EntireCounterexample.not_analyticUniversalLocalOrder {T : RealUpdate} {p : ℝ}
    (h : EntireCounterexample T p) : ¬ AnalyticUniversalLocalOrder T p := by
  intro huniversal
  exact h.not_entireUniversalLocalOrder huniversal.entireUniversalLocalOrder

end KungTraub
