import appendix_reference.KungTraubAppendices.LocalInverse
import Mathlib.Tactic

/-! Common neighborhoods and the finite family of strict bounds in Appendix A. -/

noncomputable section

open Set Filter
open scoped Topology

namespace KungTraubAppendices

/-- Every neighborhood of a simple analytic zero has an image containing a
nondegenerate compact interval about zero. -/
theorem exists_closed_interval_in_analytic_image {f : ℝ → ℝ} {α : ℝ} {I : Set ℝ}
    (hf : AnalyticAt ℝ f α) (hzero : f α = 0) (hd : deriv f α ≠ 0)
    (hI : I ∈ 𝓝 α) : ∃ r > 0, Icc (-r) r ⊆ f '' I := by
  sorry

/-- Analyticity at the zero gives the local linear bound with one fixed
constant at least one, independent of the subsequent starting point. -/
theorem exists_local_linear_bound {f : ℝ → ℝ} {α : ℝ}
    (hf : AnalyticAt ℝ f α) (hzero : f α = 0) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ᶠ y in 𝓝 α, |f y| ≤ L * |y - α| := by
  sorry

/-- One positive radius satisfies every strict power inequality in the
complete index range. All constants are fixed before its choice. -/
theorem exists_small_hermite_radius (n : ℕ) (hn : 2 ≤ n) (D L : ℝ)
    {r : ℝ} (hr : 0 < r) :
    ∃ δ > 0, δ < r ∧ ∀ j : ℕ, j ≤ n - 2 →
      D * L ^ (j + 2) * δ ^ (j + 1) < (1 / 2 : ℝ) := by
  sorry

/-- All interval, image, linear-bound and contraction requirements hold on
one closed neighborhood, before any execution is analysed. -/
theorem exists_common_hermite_neighborhood (n : ℕ) (hn : 2 ≤ n)
    {f : ℝ → ℝ} {α D L : ℝ} {I K : Set ℝ}
    (hf : ContinuousAt f α) (hzero : f α = 0) (hI : I ∈ 𝓝 α) (hK : K ∈ 𝓝 (0 : ℝ))
    (hL : ∀ᶠ y in 𝓝 α, |f y| ≤ L * |y - α|) :
    ∃ δ > 0, Icc (α - δ) (α + δ) ⊆ I ∧
      (∀ y ∈ Icc (α - δ) (α + δ), f y ∈ K ∧ |f y| ≤ L * |y - α|) ∧
      (∀ j : ℕ, j ≤ n - 2 → D * L ^ (j + 2) * δ ^ (j + 1) < (1 / 2 : ℝ)) := by
  sorry

end KungTraubAppendices
