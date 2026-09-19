import support_reference.KungTraub.EntireWitnessAssembly

/-!
# Global uniform convergence of the real stages

The uniform real correction budgets in Section 4.2 of Matthew J. Colbrook's
manuscript imply
uniform convergence on the whole real line both of the finite functions and of
their first derivatives. The limit is the already constructed entire Gaussian
series.

The finite-tail argument follows the value-tail estimate in
`EntireWitnessAssembly`; convergence uses Mathlib's metric characterization of
uniform convergence and its theorem that a summable sequence tends to zero.
-/

noncomputable section

open Filter
open scoped BigOperators Topology

namespace KungTraub

theorem GaussianStageBounds.budget_tendsto_zero {P : ℕ → Polynomial ℝ}
    {lam b : ℕ → ℝ} (h : GaussianStageBounds P lam b) :
    Tendsto b atTop (𝓝 0) := by
  sorry

/-- A finite derivative tail has the same uniform bound as a value tail. -/
theorem GaussianStageBounds.finite_derivative_tail_bound {P : ℕ → Polynomial ℝ}
    {lam b : ℕ → ℝ} (h : GaussianStageBounds P lam b)
    (s N : ℕ) (hN : s ≤ N) (t : ℝ) :
    |deriv (gaussianRealStage P lam N) t - deriv (gaussianRealStage P lam s) t| ≤
      2 * b s := by
  sorry

/-- Pointwise derivative convergence of the entire stages identifies the uniform tail. -/
theorem GaussianStageBounds.limit_derivative_tail_bound {P : ℕ → Polynomial ℝ}
    {lam b : ℕ → ℝ} (h : GaussianStageBounds P lam b) (s : ℕ) (t : ℝ) :
    |deriv (realRestriction (gaussianEntireLimit P lam)) t -
      deriv (gaussianRealStage P lam s) t| ≤ 2 * b s := by
  sorry

/-- Uniform convergence of the functions on all of ℝ, with the same entire limit. -/
theorem GaussianStageBounds.uniform_real_limit {P : ℕ → Polynomial ℝ}
    {lam b : ℕ → ℝ} (h : GaussianStageBounds P lam b) :
    TendstoUniformly (gaussianRealStage P lam)
      (realRestriction (gaussianEntireLimit P lam)) atTop := by
  sorry

/-- Uniform convergence of first derivatives on all of ℝ. -/
theorem GaussianStageBounds.uniform_real_derivative_limit {P : ℕ → Polynomial ℝ}
    {lam b : ℕ → ℝ} (h : GaussianStageBounds P lam b) :
    TendstoUniformly (fun N => deriv (gaussianRealStage P lam N))
      (deriv (realRestriction (gaussianEntireLimit P lam))) atTop := by
  sorry

end KungTraub
