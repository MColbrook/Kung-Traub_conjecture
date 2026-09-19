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
  let g := hf.hasStrictDerivAt.localInverse f (deriv f α) α hd
  have hg : AnalyticAt ℝ g (f α) := hf.analyticAt_localInverse hd
  have hleft : ∀ᶠ y in 𝓝 α, g (f y) = y :=
    hf.hasStrictDerivAt.eventually_left_inverse hd
  have hright : ∀ᶠ t in 𝓝 (f α), f (g t) = t :=
    hf.hasStrictDerivAt.eventually_right_inverse hd
  have hderiv : deriv g (f α) = (deriv f α)⁻¹ :=
    (hf.hasStrictDerivAt.to_localInverse hd).hasDerivAt.deriv
  refine ⟨g, ?_, ?_, ?_, hleft, ?_⟩
  · simpa [hzero] using hg
  · simpa [hzero] using hleft.self_of_nhds
  · simpa [hzero, one_div] using hderiv
  · simpa [hzero] using hright

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
  obtain ⟨g, hg, hgzero, _, hleft, _⟩ :=
    exists_analytic_inverse_at_simple_zero hf hzero hd
  have hgan : ∀ᶠ y in 𝓝 α, AnalyticAt ℝ g (f y) := by
    have hfc : Tendsto f (𝓝 α) (𝓝 (0 : ℝ)) := by simpa [hzero] using hf.continuousAt.tendsto
    exact hfc.eventually hg.eventually_analyticAt
  have hnonzero : ∀ᶠ y in 𝓝 α, deriv f y ≠ 0 := hf.deriv.continuousAt.eventually_ne hd
  have hleftEq : (g ∘ f) =ᶠ[𝓝 α] id := hleft
  have hgood : ∀ᶠ y in 𝓝 α, y ∈ U ∧ AnalyticAt ℝ f y ∧ deriv f y ≠ 0 ∧
      AnalyticAt ℝ g (f y) ∧ g (f y) = y ∧ deriv g (f y) = 1 / deriv f y := by
    filter_upwards [hU.mem_nhds hα, hf.eventually_analyticAt, hnonzero, hgan,
      hleft, hleftEq.deriv] with y hy hfy hdy hgy hly hderiv
    refine ⟨hy, hfy, hdy, hgy, hly, ?_⟩
    have hprod : deriv g (f y) * deriv f y = 1 := by
      simpa only [deriv_comp y hgy.differentiableAt hfy.differentiableAt, deriv_id] using hderiv
    exact (eq_div_iff hdy).mpr hprod
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hgood
  have hI : ∀ y ∈ Ioo (α - r) (α + r), y ∈ U ∧ AnalyticAt ℝ f y ∧
      deriv f y ≠ 0 ∧ AnalyticAt ℝ g (f y) ∧ g (f y) = y ∧
      deriv g (f y) = 1 / deriv f y := by
    intro y hy
    apply hball
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hy.1, hy.2]
  refine ⟨α - r, α + r, g, by linarith, by linarith,
    (fun y hy => (hI y hy).1), ?_, (fun y hy => (hI y hy).2.1),
    (fun y hy => (hI y hy).2.2.1), ?_, hgzero,
    (fun y hy => (hI y hy).2.2.2.2.1),
    (fun y hy => (hI y hy).2.2.2.2.2)⟩
  · intro y hy z hz heq
    calc y = g (f y) := (hI y hy).2.2.2.2.1.symm
         _ = g (f z) := congrArg g heq
         _ = z := (hI z hz).2.2.2.2.1
  · rintro t ⟨y, hy, rfl⟩
    exact (hI y hy).2.2.2.1

end KungTraubAppendices
