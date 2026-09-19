import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# The analytic inverse used in Appendix A

The inverse is obtained from Mathlib's analytic inverse function theorem
(David Loeffler) and its strict-derivative inverse theorem (Yury Kudryashov).
It is an object for the analysis, independent of the observation procedure.
All assumptions concern the original function near its simple zero.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace KungTraubAppendices

/-- A simple analytic zero has an analytic inverse germ with both inverse
identities and the exact reciprocal derivative. -/
theorem exists_analytic_inverse_at_simple_zero {f : ℝ → ℝ} {α : ℝ}
    (hf : AnalyticAt ℝ f α) (hzero : f α = 0) (hd : deriv f α ≠ 0) :
    ∃ g : ℝ → ℝ, AnalyticAt ℝ g 0 ∧ g 0 = α ∧
      deriv g 0 = 1 / deriv f α ∧
      (∀ᶠ y in 𝓝 α, g (f y) = y) ∧ (∀ᶠ t in 𝓝 (0 : ℝ), f (g t) = t) := by
  sorry

/-- The inverse and injectivity hold on an actual open interval inside the
given input domain. Its image has an analytic inverse, whose derivative at
every image point is the reciprocal derivative of the original function. -/
theorem exists_analytic_inverse_interval {f : ℝ → ℝ} {α : ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hα : α ∈ U) (hf : AnalyticAt ℝ f α)
    (hzero : f α = 0) (hd : deriv f α ≠ 0) :
    ∃ a b : ℝ, ∃ g : ℝ → ℝ, a < α ∧ α < b ∧ Ioo a b ⊆ U ∧
      InjOn f (Ioo a b) ∧ AnalyticOnNhd ℝ f (Ioo a b) ∧
      (∀ y ∈ Ioo a b, deriv f y ≠ 0) ∧
      AnalyticOnNhd ℝ g (f '' Ioo a b) ∧ g 0 = α ∧
      (∀ y ∈ Ioo a b, g (f y) = y) ∧
      (∀ y ∈ Ioo a b, deriv g (f y) = 1 / deriv f y) := by
  sorry

end KungTraubAppendices
