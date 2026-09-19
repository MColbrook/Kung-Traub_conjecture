import support_reference.KungTraub.EntireStages
import support_reference.KungTraub.EntireLimit
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-!
# Assembly of an entire witness from discrete stages

The limiting argument in Section 4 of Matthew J. Colbrook's manuscript.
Finite Gaussian stages, their numerical bounds, and exact preservation of
observations determine an entire counterexample.
-/

noncomputable section

open Filter Set
open scoped BigOperators Topology

namespace KungTraub

def gaussianRealStage (P : ℕ → Polynomial ℝ) (lam : ℕ → ℝ) (N : ℕ) : ℝ → ℝ :=
  finiteEntireStage (fun i t => lam i * gaussianPolynomial (P i) t) N

def gaussianComplexStage (P : ℕ → Polynomial ℝ) (lam : ℕ → ℝ) (N : ℕ) (z : ℂ) : ℂ :=
  z + ∑ i ∈ Finset.range N, (lam i : ℂ) * complexGaussianPolynomial (P i) z

def gaussianEntireLimit (P : ℕ → Polynomial ℝ) (lam : ℕ → ℝ) (z : ℂ) : ℂ :=
  z + ∑' i, (lam i : ℂ) * complexGaussianPolynomial (P i) z

/-- Actual bounds on the corrections; index zero is the first positive paper stage.
Its complex disc therefore has radius three. -/
structure GaussianStageBounds (P : ℕ → Polynomial ℝ) (lam b : ℕ → ℝ) : Prop where
  budget_pos : ∀ i, 0 < b i
  budget_half : ∀ i, b (i + 1) ≤ b i / 2
  budget_first : b 0 ≤ 1 / 32
  value_bound : ∀ i t, |lam i * gaussianPolynomial (P i) t| ≤ b i
  deriv_bound : ∀ i t, |deriv (fun y => lam i * gaussianPolynomial (P i) y) t| ≤ b i
  disc_bound : ∀ (i : ℕ) (z : ℂ), ‖z‖ ≤ (i : ℝ) + 3 →
    ‖(lam i : ℂ) * complexGaussianPolynomial (P i) z‖ ≤ b i

theorem gaussianComplexStage_ofReal (P : ℕ → Polynomial ℝ) (lam : ℕ → ℝ)
    (N : ℕ) (t : ℝ) :
    gaussianComplexStage P lam N t = (gaussianRealStage P lam N t : ℂ) := by
  sorry

theorem gaussianComplexStage_differentiable (P : ℕ → Polynomial ℝ) (lam : ℕ → ℝ)
    (N : ℕ) : Differentiable ℂ (gaussianComplexStage P lam N) := by
  sorry

theorem GaussianStageBounds.eventual_disc_bounds {P : ℕ → Polynomial ℝ} {lam b : ℕ → ℝ}
    (h : GaussianStageBounds P lam b) :
    ∀ R : ℝ, 0 < R → ∀ᶠ i : ℕ in atTop,
      ∀ z : ℂ, ‖z‖ ≤ R → ‖(lam i : ℂ) * complexGaussianPolynomial (P i) z‖ ≤ b i := by
  sorry

theorem GaussianStageBounds.locally_uniform_limit {P : ℕ → Polynomial ℝ} {lam b : ℕ → ℝ}
    (h : GaussianStageBounds P lam b) :
    TendstoLocallyUniformly (gaussianComplexStage P lam) (gaussianEntireLimit P lam) atTop := by
  sorry

theorem GaussianStageBounds.entire_real_type {P : ℕ → Polynomial ℝ} {lam b : ℕ → ℝ}
    (h : GaussianStageBounds P lam b) : EntireRealType (gaussianEntireLimit P lam) := by
  sorry

theorem GaussianStageBounds.real_derivative_limit {P : ℕ → Polynomial ℝ} {lam b : ℕ → ℝ}
    (h : GaussianStageBounds P lam b) (k : ℕ) (t : ℝ) :
    Tendsto (fun N => iteratedDeriv k (gaussianRealStage P lam N) t) atTop
      (𝓝 (iteratedDeriv k (realRestriction (gaussianEntireLimit P lam)) t)) := by
  sorry

theorem GaussianStageBounds.finite_bounds {P : ℕ → Polynomial ℝ} {lam b : ℕ → ℝ}
    (h : GaussianStageBounds P lam b) (N : ℕ) (t : ℝ) :
    |gaussianRealStage P lam N t - t| ≤ 1 / 16 ∧
      (15 : ℝ) / 16 ≤ deriv (gaussianRealStage P lam N) t ∧
      deriv (gaussianRealStage P lam N) t ≤ 17 / 16 := by
  sorry

theorem GaussianStageBounds.limit_bounds {P : ℕ → Polynomial ℝ} {lam b : ℕ → ℝ}
    (h : GaussianStageBounds P lam b) (t : ℝ) :
    |realRestriction (gaussianEntireLimit P lam) t - t| ≤ 1 / 16 ∧
      (15 : ℝ) / 16 ≤ deriv (realRestriction (gaussianEntireLimit P lam)) t ∧
      deriv (realRestriction (gaussianEntireLimit P lam)) t ≤ 17 / 16 := by
  sorry

theorem GaussianStageBounds.real_differentiable {P : ℕ → Polynomial ℝ} {lam b : ℕ → ℝ}
    (h : GaussianStageBounds P lam b) :
    Differentiable ℝ (realRestriction (gaussianEntireLimit P lam)) := by
  sorry

theorem GaussianStageBounds.existsUnique_root {P : ℕ → Polynomial ℝ} {lam b : ℕ → ℝ}
    (h : GaussianStageBounds P lam b) :
    ∃! α : ℝ, realRestriction (gaussianEntireLimit P lam) α = 0 := by
  sorry

/-- The finite tail bound is uniform on the entire real line. -/
theorem GaussianStageBounds.finite_tail_bound {P : ℕ → Polynomial ℝ} {lam b : ℕ → ℝ}
    (h : GaussianStageBounds P lam b) (s N : ℕ) (hN : s ≤ N) (t : ℝ) :
    |gaussianRealStage P lam N t - gaussianRealStage P lam s t| ≤ 2 * b s := by
  sorry

theorem GaussianStageBounds.limit_tail_bound {P : ℕ → Polynomial ℝ} {lam b : ℕ → ℝ}
    (h : GaussianStageBounds P lam b) (s : ℕ) (t : ℝ) :
    |realRestriction (gaussianEntireLimit P lam) t - gaussianRealStage P lam s t| ≤ 2 * b s := by
  sorry

theorem GaussianStageBounds.root_displacement {P : ℕ → Polynomial ℝ} {lam b : ℕ → ℝ}
    (h : GaussianStageBounds P lam b) (s : ℕ) {α a : ℝ}
    (hα : realRestriction (gaussianEntireLimit P lam) α = 0)
    (ha : gaussianRealStage P lam (s + 1) a = 0) : |α - a| ≤ 4 * b (s + 1) := by
  sorry

def gaussianStageOutput {n : ℕ} (A : RealAlgorithm n) (P : ℕ → Polynomial ℝ)
    (lam starts : ℕ → ℝ) (s : ℕ) : ℝ :=
  A.run (gaussianRealStage P lam (s + 1)) (starts s)

/-- Discrete data supplied by the finite adversary. Index `s` records the completed
stage with `s+1` corrections. The exponent can be fixed or vary by stage. -/
structure GaussianAdversarialStages {n : ℕ} (A : RealAlgorithm n)
    (B : ℝ) (exponent : ℕ → ℝ) where
  polynomial : ℕ → Polynomial ℝ
  scale : ℕ → ℝ
  budget : ℕ → ℝ
  epsilon : ℕ → ℝ
  starts : ℕ → ℝ
  roots : ℕ → ℝ
  coefficient : ℕ → ℝ
  bounds : GaussianStageBounds polynomial scale budget
  epsilon_pos : ∀ s, 0 < epsilon s
  epsilon_cap : ∀ s, epsilon s < 1 / ((s : ℝ) + 1)
  epsilon_quarter : ∀ s, epsilon s < 1 / 4
  coefficient_pos : ∀ s, 0 < coefficient s
  stage_root : ∀ s, gaussianRealStage polynomial scale (s + 1) (roots s) = 0
  start_lower : ∀ s, (3 / 4 : ℝ) * epsilon s ≤ starts s - roots s
  start_upper : ∀ s, starts s - roots s ≤ (5 / 4 : ℝ) * epsilon s
  error_bound : ∀ s, coefficient s * epsilon s ^ B ≤
    |gaussianStageOutput A polynomial scale starts s - roots s|
  amplification : ∀ s : ℕ, ((s : ℝ) + 1) * (2 * epsilon s) ^ exponent s ≤
    (coefficient s / 2) * epsilon s ^ B
  next_budget_error : ∀ s, budget (s + 1) ≤
    |gaussianStageOutput A polynomial scale starts s - roots s| / 32
  next_budget_scale : ∀ s, budget (s + 1) ≤ epsilon s / 32
  jets_preserved : ∀ s (j : Fin n) z k,
    A.actualQuery (gaussianRealStage polynomial scale (s + 1)) (starts s) j = .derivative z k →
    ∀ N, s + 1 ≤ N → iteratedDeriv k (gaussianRealStage polynomial scale N) z =
      iteratedDeriv k (gaussianRealStage polynomial scale (s + 1)) z

theorem GaussianAdversarialStages.limit_jet_eq {n : ℕ} {A : RealAlgorithm n}
    {B : ℝ} {exponent : ℕ → ℝ} (D : GaussianAdversarialStages A B exponent)
    (s : ℕ) (j : Fin n) (z : ℝ) (k : ℕ)
    (hquery : A.actualQuery (gaussianRealStage D.polynomial D.scale (s + 1))
      (D.starts s) j = .derivative z k) :
    iteratedDeriv k (realRestriction (gaussianEntireLimit D.polynomial D.scale)) z =
      iteratedDeriv k (gaussianRealStage D.polynomial D.scale (s + 1)) z := by
  sorry

/-- Every adaptive decision and output agrees exactly with the saved finite execution. -/
theorem GaussianAdversarialStages.output_preserved {n : ℕ} {A : RealAlgorithm n}
    {B : ℝ} {exponent : ℕ → ℝ} (D : GaussianAdversarialStages A B exponent) (s : ℕ) :
    A.run (realRestriction (gaussianEntireLimit D.polynomial D.scale)) (D.starts s) =
      gaussianStageOutput A D.polynomial D.scale D.starts s := by
  sorry

theorem GaussianAdversarialStages.relative_root_bounds {n : ℕ} {A : RealAlgorithm n}
    {B : ℝ} {exponent : ℕ → ℝ} (D : GaussianAdversarialStages A B exponent)
    {α : ℝ} (hα : realRestriction (gaussianEntireLimit D.polynomial D.scale) α = 0) (s : ℕ) :
    |α - D.roots s| ≤ D.epsilon s / 8 ∧ |α - D.roots s| ≤
      |gaussianStageOutput A D.polynomial D.scale D.starts s - D.roots s| / 8 := by
  sorry

theorem GaussianAdversarialStages.start_distance_bounds {n : ℕ} {A : RealAlgorithm n}
    {B : ℝ} {exponent : ℕ → ℝ} (D : GaussianAdversarialStages A B exponent)
    {α : ℝ} (hα : realRestriction (gaussianEntireLimit D.polynomial D.scale) α = 0) (s : ℕ) :
    (5 / 8 : ℝ) * D.epsilon s ≤ D.starts s - α ∧
      D.starts s - α ≤ (11 / 8 : ℝ) * D.epsilon s := by
  sorry

theorem GaussianAdversarialStages.starts_ne_root {n : ℕ} {A : RealAlgorithm n}
    {B : ℝ} {exponent : ℕ → ℝ} (D : GaussianAdversarialStages A B exponent)
    {α : ℝ} (hα : realRestriction (gaussianEntireLimit D.polynomial D.scale) α = 0) (s : ℕ) :
    D.starts s ≠ α := by
  sorry

theorem GaussianAdversarialStages.starts_tendsto {n : ℕ} {A : RealAlgorithm n}
    {B : ℝ} {exponent : ℕ → ℝ} (D : GaussianAdversarialStages A B exponent)
    {α : ℝ} (hα : realRestriction (gaussianEntireLimit D.polynomial D.scale) α = 0) :
    Tendsto D.starts atTop (𝓝 α) := by
  sorry

theorem GaussianAdversarialStages.ratio_stage_bound {n : ℕ} {A : RealAlgorithm n}
    {B : ℝ} {exponent : ℕ → ℝ} (D : GaussianAdversarialStages A B exponent)
    (hp : ∀ s, 0 ≤ exponent s) {α : ℝ}
    (hα : realRestriction (gaussianEntireLimit D.polynomial D.scale) α = 0) (s : ℕ) :
    (s : ℝ) + 1 ≤ errorRatio A.run
      (realRestriction (gaussianEntireLimit D.polynomial D.scale)) α (exponent s) (D.starts s) := by
  sorry

/-- The limit is explicitly the Gaussian series. Existence and uniqueness of its real
root, all witness properties, and the full stage ratio estimates are conclusions. -/
theorem GaussianAdversarialStages.assemble {n : ℕ} {A : RealAlgorithm n}
    {B : ℝ} {exponent : ℕ → ℝ} (D : GaussianAdversarialStages A B exponent)
    (hp : ∀ s, 0 ≤ exponent s) :
    ∃ α : ℝ, EntireWitnessData (gaussianEntireLimit D.polynomial D.scale) α D.starts ∧
      ∀ s : ℕ, (s : ℝ) + 1 ≤ errorRatio A.run
        (realRestriction (gaussianEntireLimit D.polynomial D.scale)) α (exponent s) (D.starts s) := by
  sorry

/-- An entire counterexample at a fixed exponent from the discrete stage data. -/
theorem entireCounterexample_of_gaussian_stages {n : ℕ} {A : RealAlgorithm n}
    {B p : ℝ} (D : GaussianAdversarialStages A B (fun _ => p)) (hp : 0 ≤ p) :
    EntireCounterexample A.run p := by
  sorry

/-- One constructed stage sequence with the moving exponents gives the same entire
function and starts for every fixed exponent above B. -/
theorem simultaneousEntireCounterexample_of_gaussian_stages {n : ℕ} {A : RealAlgorithm n}
    {B : ℝ} (D : GaussianAdversarialStages A B (fun s => B + 1 / ((s : ℝ) + 1)))
    (hB : 0 ≤ B) : SimultaneousEntireCounterexample A.run B := by
  sorry

end KungTraub
