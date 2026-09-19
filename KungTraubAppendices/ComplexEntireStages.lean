import KungTraubAppendices.ComplexRoots
import KungTraub.EntireLimit
import KungTraub.DiagonalEstimates
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-!
# Polynomial stages and their entire limit

Index `i` denotes positive stage `i+1`, whose controlled complex disc has radius
`i+3`. The limit estimates of Appendix B use the complex series arguments in
`KungTraub.EntireLimit` and the budget arithmetic in `KungTraub.DiagonalEstimates`.
-/

noncomputable section
open Filter Set
open scoped BigOperators Topology

namespace KungTraubAppendices

def complexPolynomialStage (P : ℕ → Polynomial ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  z + ∑ i ∈ Finset.range N, (P i).eval z

def complexPolynomialLimit (P : ℕ → Polynomial ℂ) (z : ℂ) : ℂ :=
  z + ∑' i, (P i).eval z

/-- Complete bounds on actual corrections, with the multiplier absorbed into P. -/
structure ComplexPolynomialStageBounds (P : ℕ → Polynomial ℂ) (b : ℕ → ℝ) : Prop where
  budget_pos : ∀ i, 0 < b i
  budget_half : ∀ i, b (i + 1) ≤ b i / 2
  budget_first : b 0 ≤ 1 / 32
  disc_bound : ∀ (i : ℕ) (z : ℂ), ‖z‖ ≤ (i : ℝ) + 3 → ‖(P i).eval z‖ ≤ b i
  deriv_bound : ∀ (i : ℕ) (z : ℂ), ‖z‖ ≤ 1 → ‖(P i).derivative.eval z‖ ≤ b i

theorem complexPolynomialStage_eq_eval (P : ℕ → Polynomial ℂ) (N : ℕ) :
    complexPolynomialStage P N = fun z => (Polynomial.X + ∑ i ∈ Finset.range N, P i).eval z := by
  funext z
  simp [complexPolynomialStage, Polynomial.eval_finsetSum]

theorem complexPolynomialStage_differentiable (P : ℕ → Polynomial ℂ) (N : ℕ) :
    Differentiable ℂ (complexPolynomialStage P N) := by
  rw [complexPolynomialStage_eq_eval]
  exact fun _ => (Polynomial.X + ∑ i ∈ Finset.range N, P i).differentiableAt

theorem complexPolynomialStage_deriv (P : ℕ → Polynomial ℂ) (N : ℕ) (z : ℂ) :
    deriv (complexPolynomialStage P N) z = 1 + ∑ i ∈ Finset.range N, (P i).derivative.eval z := by
  rw [complexPolynomialStage_eq_eval, Polynomial.deriv]
  simp [Polynomial.eval_finsetSum]

theorem ComplexPolynomialStageBounds.value_bound {P : ℕ → Polynomial ℂ} {b : ℕ → ℝ}
    (h : ComplexPolynomialStageBounds P b) (i : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖(P i).eval z‖ ≤ b i := h.disc_bound i z (by have := Nat.cast_nonneg (α := ℝ) i; linarith)

theorem ComplexPolynomialStageBounds.partial_budget {P : ℕ → Polynomial ℂ} {b : ℕ → ℝ}
    (h : ComplexPolynomialStageBounds P b) (N : ℕ) :
    (∑ i ∈ Finset.range N, b i) ≤ (1 / 16 : ℝ) :=
  ((KungTraub.summable_budget (fun i => (h.budget_pos i).le) h.budget_half).sum_le_tsum _
    (fun i _ => (h.budget_pos i).le)).trans
      (KungTraub.tsum_budget_le_one_sixteenth (fun i => (h.budget_pos i).le)
        h.budget_half h.budget_first)

theorem ComplexPolynomialStageBounds.finite_bounds {P : ℕ → Polynomial ℂ} {b : ℕ → ℝ}
    (h : ComplexPolynomialStageBounds P b) (N : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖complexPolynomialStage P N z - z‖ ≤ (1 / 16 : ℝ) ∧
      ‖deriv (complexPolynomialStage P N) z - 1‖ ≤ (1 / 16 : ℝ) := by
  constructor
  · simp only [complexPolynomialStage, add_sub_cancel_left]
    exact (norm_sum_le _ _).trans
      ((Finset.sum_le_sum (fun i _ => h.value_bound i z hz)).trans (h.partial_budget N))
  · rw [complexPolynomialStage_deriv, add_sub_cancel_left]
    exact (norm_sum_le _ _).trans
      ((Finset.sum_le_sum (fun i _ => h.deriv_bound i z hz)).trans (h.partial_budget N))

theorem ComplexPolynomialStageBounds.eventual_disc_bounds
    {P : ℕ → Polynomial ℂ} {b : ℕ → ℝ} (h : ComplexPolynomialStageBounds P b) :
    ∀ R : ℝ, 0 < R → ∀ᶠ i : ℕ in atTop,
      ∀ z : ℂ, ‖z‖ ≤ R → ‖(P i).eval z‖ ≤ b i := by
  intro R _
  have hcast : Tendsto (fun i : ℕ => (i : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hcast.eventually (eventually_ge_atTop R)] with i hi
  exact fun z hz => h.disc_bound i z (by linarith)

theorem ComplexPolynomialStageBounds.locally_uniform_limit
    {P : ℕ → Polynomial ℂ} {b : ℕ → ℝ} (h : ComplexPolynomialStageBounds P b) :
    TendstoLocallyUniformly (complexPolynomialStage P) (complexPolynomialLimit P) atTop := by
  have hsum := KungTraub.tendstoLocallyUniformly_sum_of_disc_bounds
    (KungTraub.summable_budget (fun i => (h.budget_pos i).le) h.budget_half) h.eventual_disc_bounds
  have hid : TendstoUniformly (fun _ : ℕ => (fun z : ℂ => z)) (fun z : ℂ => z) atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    exact Eventually.of_forall (fun _ z => by simpa using hε)
  exact hid.tendstoLocallyUniformly.add hsum

theorem ComplexPolynomialStageBounds.entire
    {P : ℕ → Polynomial ℂ} {b : ℕ → ℝ} (h : ComplexPolynomialStageBounds P b) :
    Differentiable ℂ (complexPolynomialLimit P) :=
  differentiable_id.add (KungTraub.differentiable_tsum_of_disc_bounds
    (fun i _ => (P i).differentiableAt)
    (KungTraub.summable_budget (fun i => (h.budget_pos i).le) h.budget_half) h.eventual_disc_bounds)

theorem ComplexPolynomialStageBounds.limit_bounds {P : ℕ → Polynomial ℂ} {b : ℕ → ℝ}
    (h : ComplexPolynomialStageBounds P b) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖complexPolynomialLimit P z - z‖ ≤ (1 / 16 : ℝ) ∧
      ‖deriv (complexPolynomialLimit P) z - 1‖ ≤ (1 / 16 : ℝ) := by
  have hvalue := h.locally_uniform_limit.tendstoLocallyUniformlyOn.tendsto_at (mem_univ z)
  have hderiv : Tendsto (fun N => deriv (complexPolynomialStage P N) z) atTop
      (𝓝 (deriv (complexPolynomialLimit P) z)) := by
    have hi := KungTraub.tendstoLocallyUniformly_iteratedDeriv
      (complexPolynomialStage_differentiable P) h.locally_uniform_limit 1
    simpa only [iteratedDeriv_one] using
      hi.tendstoLocallyUniformlyOn.tendsto_at (mem_univ z)
  exact ⟨le_of_tendsto' ((hvalue.sub_const z).norm) (fun N => (h.finite_bounds N z hz).1),
    le_of_tendsto' ((hderiv.sub_const 1).norm) (fun N => (h.finite_bounds N z hz).2)⟩

theorem ComplexPolynomialStageBounds.exists_unique_simple_root
    {P : ℕ → Polynomial ℂ} {b : ℕ → ℝ} (h : ComplexPolynomialStageBounds P b) :
    ∃ α : ℂ, ‖α‖ ≤ (1 / 16 : ℝ) ∧ SimpleComplexRoot (complexPolynomialLimit P) α ∧
      ∀ z : ℂ, ‖z‖ ≤ 1 → complexPolynomialLimit P z = 0 → z = α :=
  exists_unique_simple_root_on_unit_disc h.entire
    (fun z hz => (h.limit_bounds z hz).1) (fun z hz => (h.limit_bounds z hz).2)

theorem ComplexPolynomialStageBounds.finite_tail_bound
    {P : ℕ → Polynomial ℂ} {b : ℕ → ℝ} (h : ComplexPolynomialStageBounds P b)
    (s N : ℕ) (hN : s ≤ N) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖complexPolynomialStage P N z - complexPolynomialStage P s z‖ ≤ 2 * b s := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  have heq : complexPolynomialStage P (s + k) z - complexPolynomialStage P s z =
      ∑ i ∈ Finset.range k, (P (s + i)).eval z := by
    simp [complexPolynomialStage, Finset.sum_range_add]
  rw [heq]
  have hsummable : Summable (fun i => b (s + i)) :=
    KungTraub.summable_budget (fun i => (h.budget_pos (s + i)).le)
      (fun i => by simpa only [Nat.add_assoc] using h.budget_half (s + i))
  calc
    _ ≤ ∑ i ∈ Finset.range k, b (s + i) :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => h.value_bound (s + i) z hz))
    _ ≤ ∑' i, b (s + i) := hsummable.sum_le_tsum _ (fun i _ => (h.budget_pos (s + i)).le)
    _ ≤ 2 * b s := by simpa only [Nat.add_comm] using
      KungTraub.tsum_budget_tail_le_twice (fun i => (h.budget_pos i).le) h.budget_half s

theorem ComplexPolynomialStageBounds.limit_tail_bound
    {P : ℕ → Polynomial ℂ} {b : ℕ → ℝ} (h : ComplexPolynomialStageBounds P b)
    (s : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖complexPolynomialLimit P z - complexPolynomialStage P s z‖ ≤ 2 * b s := by
  have hvalue := h.locally_uniform_limit.tendstoLocallyUniformlyOn.tendsto_at (mem_univ z)
  apply le_of_tendsto ((hvalue.sub_const (complexPolynomialStage P s z)).norm)
  exact (eventually_ge_atTop s).mono (fun N hN => h.finite_tail_bound s N hN z hz)

theorem ComplexPolynomialStageBounds.root_displacement
    {P : ℕ → Polynomial ℂ} {b : ℕ → ℝ} (h : ComplexPolynomialStageBounds P b)
    (s : ℕ) {α a : ℂ} (hαnorm : ‖α‖ ≤ 1) (hanorm : ‖a‖ ≤ 1)
    (hα : complexPolynomialLimit P α = 0) (ha : complexPolynomialStage P (s + 1) a = 0) :
    ‖α - a‖ ≤ 4 * b (s + 1) := by
  have hv : ‖complexPolynomialLimit P a‖ ≤ 2 * b (s + 1) := by
    simpa only [ha, sub_zero] using h.limit_tail_bound (s + 1) a hanorm
  have hd := (near_identity_bilipschitz_on_unit_disc h.entire (1 / 16)
    (fun z hz => by simpa using (h.limit_bounds z hz).2) hαnorm hanorm).1
  rw [hα, zero_sub, norm_neg] at hd
  norm_num at hd
  nlinarith [norm_nonneg (α - a)]

end KungTraubAppendices
