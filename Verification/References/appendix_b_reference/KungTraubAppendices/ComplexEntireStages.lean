import appendix_b_reference.KungTraubAppendices.ComplexRoots
import appendix_b_reference.KungTraub.EntireLimit
import appendix_b_reference.KungTraub.DiagonalEstimates
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
  sorry

theorem complexPolynomialStage_differentiable (P : ℕ → Polynomial ℂ) (N : ℕ) :
    Differentiable ℂ (complexPolynomialStage P N) := by
  sorry

theorem complexPolynomialStage_deriv (P : ℕ → Polynomial ℂ) (N : ℕ) (z : ℂ) :
    deriv (complexPolynomialStage P N) z = 1 + ∑ i ∈ Finset.range N, (P i).derivative.eval z := by
  sorry

theorem ComplexPolynomialStageBounds.value_bound {P : ℕ → Polynomial ℂ} {b : ℕ → ℝ}
    (h : ComplexPolynomialStageBounds P b) (i : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖(P i).eval z‖ ≤ b i := by
  sorry

theorem ComplexPolynomialStageBounds.partial_budget {P : ℕ → Polynomial ℂ} {b : ℕ → ℝ}
    (h : ComplexPolynomialStageBounds P b) (N : ℕ) :
    (∑ i ∈ Finset.range N, b i) ≤ (1 / 16 : ℝ) := by
  sorry

theorem ComplexPolynomialStageBounds.finite_bounds {P : ℕ → Polynomial ℂ} {b : ℕ → ℝ}
    (h : ComplexPolynomialStageBounds P b) (N : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖complexPolynomialStage P N z - z‖ ≤ (1 / 16 : ℝ) ∧
      ‖deriv (complexPolynomialStage P N) z - 1‖ ≤ (1 / 16 : ℝ) := by
  sorry

theorem ComplexPolynomialStageBounds.eventual_disc_bounds
    {P : ℕ → Polynomial ℂ} {b : ℕ → ℝ} (h : ComplexPolynomialStageBounds P b) :
    ∀ R : ℝ, 0 < R → ∀ᶠ i : ℕ in atTop,
      ∀ z : ℂ, ‖z‖ ≤ R → ‖(P i).eval z‖ ≤ b i := by
  sorry

theorem ComplexPolynomialStageBounds.locally_uniform_limit
    {P : ℕ → Polynomial ℂ} {b : ℕ → ℝ} (h : ComplexPolynomialStageBounds P b) :
    TendstoLocallyUniformly (complexPolynomialStage P) (complexPolynomialLimit P) atTop := by
  sorry

theorem ComplexPolynomialStageBounds.entire
    {P : ℕ → Polynomial ℂ} {b : ℕ → ℝ} (h : ComplexPolynomialStageBounds P b) :
    Differentiable ℂ (complexPolynomialLimit P) := by
  sorry

theorem ComplexPolynomialStageBounds.limit_bounds {P : ℕ → Polynomial ℂ} {b : ℕ → ℝ}
    (h : ComplexPolynomialStageBounds P b) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖complexPolynomialLimit P z - z‖ ≤ (1 / 16 : ℝ) ∧
      ‖deriv (complexPolynomialLimit P) z - 1‖ ≤ (1 / 16 : ℝ) := by
  sorry

theorem ComplexPolynomialStageBounds.exists_unique_simple_root
    {P : ℕ → Polynomial ℂ} {b : ℕ → ℝ} (h : ComplexPolynomialStageBounds P b) :
    ∃ α : ℂ, ‖α‖ ≤ (1 / 16 : ℝ) ∧ SimpleComplexRoot (complexPolynomialLimit P) α ∧
      ∀ z : ℂ, ‖z‖ ≤ 1 → complexPolynomialLimit P z = 0 → z = α := by
  sorry

theorem ComplexPolynomialStageBounds.finite_tail_bound
    {P : ℕ → Polynomial ℂ} {b : ℕ → ℝ} (h : ComplexPolynomialStageBounds P b)
    (s N : ℕ) (hN : s ≤ N) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖complexPolynomialStage P N z - complexPolynomialStage P s z‖ ≤ 2 * b s := by
  sorry

theorem ComplexPolynomialStageBounds.limit_tail_bound
    {P : ℕ → Polynomial ℂ} {b : ℕ → ℝ} (h : ComplexPolynomialStageBounds P b)
    (s : ℕ) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖complexPolynomialLimit P z - complexPolynomialStage P s z‖ ≤ 2 * b s := by
  sorry

theorem ComplexPolynomialStageBounds.root_displacement
    {P : ℕ → Polynomial ℂ} {b : ℕ → ℝ} (h : ComplexPolynomialStageBounds P b)
    (s : ℕ) {α a : ℂ} (hαnorm : ‖α‖ ≤ 1) (hanorm : ‖a‖ ≤ 1)
    (hα : complexPolynomialLimit P α = 0) (ha : complexPolynomialStage P (s + 1) a = 0) :
    ‖α - a‖ ≤ 4 * b (s + 1) := by
  sorry

end KungTraubAppendices
