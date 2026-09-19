import KungTraubAppendices.ComplexEntireStages
import KungTraubAppendices.ComplexTranscriptLimits
import KungTraubAppendices.ComplexDiagonalEstimates

/-!
# An entire witness from finite polynomial stages

Appendix B's limit argument follows `KungTraub.EntireWitnessAssembly` for
complex polynomial corrections. The finite stage invariants give an entire
limit with the required root, derivative bounds and divergent error ratios.
-/

noncomputable section
open Filter
open scoped Topology
namespace KungTraubAppendices

structure ComplexAdversarialStages {n : ℕ} (A : ComplexAlgorithm n) (B p : ℝ) where
  polynomial : ℕ → Polynomial ℂ
  budget : ℕ → ℝ
  epsilon : ℕ → ℝ
  starts : ℕ → ℂ
  roots : ℕ → ℂ
  coefficient : ℕ → ℝ
  bounds : ComplexPolynomialStageBounds polynomial budget
  epsilon_pos : ∀ s, 0 < epsilon s
  epsilon_cap : ∀ s, epsilon s < 1 / ((s : ℝ) + 1)
  coefficient_pos : ∀ s, 0 < coefficient s
  root_norm : ∀ s, ‖roots s‖ ≤ 1
  stage_root : ∀ s, complexPolynomialStage polynomial (s + 1) (roots s) = 0
  start_lower : ∀ s, (3 / 4 : ℝ) * epsilon s ≤ ‖starts s - roots s‖
  start_upper : ∀ s, ‖starts s - roots s‖ ≤ (5 / 4 : ℝ) * epsilon s
  error_bound : ∀ s, coefficient s * epsilon s ^ B ≤
    ‖A.run (complexPolynomialStage polynomial (s + 1)) (starts s) - roots s‖
  amplification : ∀ s : ℕ, ((s : ℝ) + 1) * (2 * epsilon s) ^ p ≤
    (coefficient s / 2) * epsilon s ^ B
  next_budget_error : ∀ s, budget (s + 1) ≤
    ‖A.run (complexPolynomialStage polynomial (s + 1)) (starts s) - roots s‖ / 32
  next_budget_scale : ∀ s, budget (s + 1) ≤ epsilon s / 32
  jets_preserved : ∀ s (j : Fin n) z k,
    A.actualQuery (complexPolynomialStage polynomial (s + 1)) (starts s) j = .derivative z k →
    ∀ N, s + 1 ≤ N → iteratedDeriv k (complexPolynomialStage polynomial N) z =
      iteratedDeriv k (complexPolynomialStage polynomial (s + 1)) z

theorem ComplexAdversarialStages.run_eq_limit {n : ℕ} {A : ComplexAlgorithm n}
    {B p : ℝ} (D : ComplexAdversarialStages A B p) (s : ℕ) :
    A.run (complexPolynomialLimit D.polynomial) (D.starts s) =
      A.run (complexPolynomialStage D.polynomial (s + 1)) (D.starts s) := by
  apply A.run_eq_entire_limit (complexPolynomialStage_differentiable D.polynomial)
    D.bounds.locally_uniform_limit
  intro j
  cases hq : A.actualQuery (complexPolynomialStage D.polynomial (s + 1)) (D.starts s) j with
  | idle => simp [ComplexQuery.answer]
  | derivative z k =>
    simp only [ComplexQuery.answer]
    exact (eventually_ge_atTop (s + 1)).mono (fun N hN => D.jets_preserved s j z k hq N hN)

/-- The complete witness follows from the stated finite stage invariants. -/
theorem ComplexAdversarialStages.counterexample {n : ℕ} {A : ComplexAlgorithm n}
    {B p : ℝ} (D : ComplexAdversarialStages A B p) (hp : 0 ≤ p) :
    ComplexEntireCounterexample A.run p := by
  obtain ⟨α, hαsmall, hαroot, hunique⟩ := D.bounds.exists_unique_simple_root
  have hαnorm : ‖α‖ ≤ 1 := hαsmall.trans (by norm_num)
  have hdisplacement (s : ℕ) : ‖α - D.roots s‖ ≤ 4 * D.budget (s + 1) :=
    D.bounds.root_displacement s hαnorm (D.root_norm s) hαroot.1 (D.stage_root s)
  have hrelative (s : ℕ) := complex_root_displacement_of_budget (hdisplacement s)
    (D.next_budget_error s) (D.next_budget_scale s)
  obtain ⟨hne, hstarts, hratios⟩ := complex_stage_bounds_imply_divergence hp
    D.epsilon_pos D.epsilon_cap D.start_lower D.start_upper
    (fun s => (hrelative s).2) (fun s => (hrelative s).1) D.error_bound D.amplification
  refine ⟨complexPolynomialLimit D.polynomial, α, D.starts, ?_, ?_⟩
  · refine ⟨D.bounds.entire, ?_, hαroot.1, hαsmall.trans_lt (by norm_num),
      hunique, hstarts, hne⟩
    intro z hz
    exact (D.bounds.limit_bounds z hz).2.trans (by norm_num)
  · simpa only [complexErrorRatio, D.run_eq_limit, Real.rpow_eq_pow] using hratios

end KungTraubAppendices
