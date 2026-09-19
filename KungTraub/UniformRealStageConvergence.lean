import KungTraub.EntireWitnessAssembly

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
    Tendsto b atTop (𝓝 0) :=
  (summable_budget (fun i => (h.budget_pos i).le) h.budget_half).tendsto_atTop_zero

/-- A finite derivative tail has the same uniform bound as a value tail. -/
theorem GaussianStageBounds.finite_derivative_tail_bound {P : ℕ → Polynomial ℝ}
    {lam b : ℕ → ℝ} (h : GaussianStageBounds P lam b)
    (s N : ℕ) (hN : s ≤ N) (t : ℝ) :
    |deriv (gaussianRealStage P lam N) t - deriv (gaussianRealStage P lam s) t| ≤
      2 * b s := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  have hd (N : ℕ) : deriv (gaussianRealStage P lam N) t =
      1 + ∑ i ∈ Finset.range N, deriv (fun y => lam i * gaussianPolynomial (P i) y) t :=
    (finiteEntireStage_hasDerivAt
      (fun i y => ((gaussianPolynomial_hasDerivAt (P i) y).const_mul (lam i)).differentiableAt)
      N t).deriv
  have heq : deriv (gaussianRealStage P lam (s + k)) t -
      deriv (gaussianRealStage P lam s) t =
      ∑ i ∈ Finset.range k, deriv (fun y => lam (s + i) * gaussianPolynomial (P (s + i)) y) t := by
    simp [hd, Finset.sum_range_add]
  rw [heq]
  have hsummable : Summable (fun i => b (s + i)) :=
    summable_budget (fun i => (h.budget_pos (s + i)).le)
      (fun i => by simpa only [Nat.add_assoc] using h.budget_half (s + i))
  calc
    _ ≤ ∑ i ∈ Finset.range k, b (s + i) :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun i _ => h.deriv_bound (s + i) t))
    _ ≤ ∑' i, b (s + i) :=
      hsummable.sum_le_tsum _ (fun i _ => (h.budget_pos (s + i)).le)
    _ ≤ 2 * b s := by simpa only [Nat.add_comm] using
      tsum_budget_tail_le_twice (fun i => (h.budget_pos i).le) h.budget_half s

/-- Pointwise derivative convergence of the entire stages identifies the uniform tail. -/
theorem GaussianStageBounds.limit_derivative_tail_bound {P : ℕ → Polynomial ℝ}
    {lam b : ℕ → ℝ} (h : GaussianStageBounds P lam b) (s : ℕ) (t : ℝ) :
    |deriv (realRestriction (gaussianEntireLimit P lam)) t -
      deriv (gaussianRealStage P lam s) t| ≤ 2 * b s := by
  have hderiv : Tendsto (fun N => deriv (gaussianRealStage P lam N) t) atTop
      (𝓝 (deriv (realRestriction (gaussianEntireLimit P lam)) t)) := by
    simpa only [iteratedDeriv_one] using h.real_derivative_limit 1 t
  apply le_of_tendsto ((hderiv.sub_const (deriv (gaussianRealStage P lam s) t)).abs)
  exact (eventually_ge_atTop s).mono (fun N hN => h.finite_derivative_tail_bound s N hN t)

/-- Uniform convergence of the functions on all of ℝ, with the same entire limit. -/
theorem GaussianStageBounds.uniform_real_limit {P : ℕ → Polynomial ℝ}
    {lam b : ℕ → ℝ} (h : GaussianStageBounds P lam b) :
    TendstoUniformly (gaussianRealStage P lam)
      (realRestriction (gaussianEntireLimit P lam)) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have htail : Tendsto (fun N => 2 * b N) atTop (𝓝 0) := by
    simpa using h.budget_tendsto_zero.const_mul 2
  filter_upwards [htail.eventually (gt_mem_nhds hε)] with N hN
  intro t
  simpa only [Real.dist_eq] using (h.limit_tail_bound N t).trans_lt hN

/-- Uniform convergence of first derivatives on all of ℝ. -/
theorem GaussianStageBounds.uniform_real_derivative_limit {P : ℕ → Polynomial ℝ}
    {lam b : ℕ → ℝ} (h : GaussianStageBounds P lam b) :
    TendstoUniformly (fun N => deriv (gaussianRealStage P lam N))
      (deriv (realRestriction (gaussianEntireLimit P lam))) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have htail : Tendsto (fun N => 2 * b N) atTop (𝓝 0) := by
    simpa using h.budget_tendsto_zero.const_mul 2
  filter_upwards [htail.eventually (gt_mem_nhds hε)] with N hN
  intro t
  simpa only [Real.dist_eq] using (h.limit_derivative_tail_bound N t).trans_lt hN

end KungTraub
