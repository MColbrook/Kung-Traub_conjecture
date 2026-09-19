import KungTraub.EntireStages
import KungTraub.EntireLimit
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
  simp [gaussianComplexStage, gaussianRealStage, finiteEntireStage,
    complexGaussianPolynomial_ofReal]

theorem gaussianComplexStage_differentiable (P : ℕ → Polynomial ℝ) (lam : ℕ → ℝ)
    (N : ℕ) : Differentiable ℂ (gaussianComplexStage P lam N) :=
  differentiable_id.add (Differentiable.fun_sum (fun i _ =>
    (complexGaussianPolynomial_differentiable (P i)).const_mul (lam i : ℂ)))

theorem GaussianStageBounds.eventual_disc_bounds {P : ℕ → Polynomial ℝ} {lam b : ℕ → ℝ}
    (h : GaussianStageBounds P lam b) :
    ∀ R : ℝ, 0 < R → ∀ᶠ i : ℕ in atTop,
      ∀ z : ℂ, ‖z‖ ≤ R → ‖(lam i : ℂ) * complexGaussianPolynomial (P i) z‖ ≤ b i := by
  intro R _
  have hcast : Tendsto (fun i : ℕ => (i : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hcast.eventually (eventually_ge_atTop R)] with i hi
  intro z hz
  exact h.disc_bound i z (by linarith)

theorem GaussianStageBounds.locally_uniform_limit {P : ℕ → Polynomial ℝ} {lam b : ℕ → ℝ}
    (h : GaussianStageBounds P lam b) :
    TendstoLocallyUniformly (gaussianComplexStage P lam) (gaussianEntireLimit P lam) atTop := by
  have hsum := tendstoLocallyUniformly_sum_of_disc_bounds
    (summable_budget (fun i => (h.budget_pos i).le) h.budget_half) h.eventual_disc_bounds
  have hid : TendstoUniformly (fun _ : ℕ => (fun z : ℂ => z)) (fun z : ℂ => z) atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    exact Eventually.of_forall (fun _ z => by simpa using hε)
  exact hid.tendstoLocallyUniformly.add hsum

theorem GaussianStageBounds.entire_real_type {P : ℕ → Polynomial ℝ} {lam b : ℕ → ℝ}
    (h : GaussianStageBounds P lam b) : EntireRealType (gaussianEntireLimit P lam) := by
  refine ⟨differentiable_id.add (differentiable_tsum_of_disc_bounds
    (fun i => (complexGaussianPolynomial_differentiable (P i)).const_mul (lam i : ℂ))
    (summable_budget (fun i => (h.budget_pos i).le) h.budget_half) h.eventual_disc_bounds), ?_⟩
  apply im_limit_eq_zero_on_real h.locally_uniform_limit
  intro N t
  rw [gaussianComplexStage_ofReal]
  exact Complex.ofReal_im _

theorem GaussianStageBounds.real_derivative_limit {P : ℕ → Polynomial ℝ} {lam b : ℕ → ℝ}
    (h : GaussianStageBounds P lam b) (k : ℕ) (t : ℝ) :
    Tendsto (fun N => iteratedDeriv k (gaussianRealStage P lam N) t) atTop
      (𝓝 (iteratedDeriv k (realRestriction (gaussianEntireLimit P lam)) t)) := by
  have heq (N : ℕ) : (fun y : ℝ => (gaussianComplexStage P lam N y).re) =
      gaussianRealStage P lam N := by
    funext y
    simp only [gaussianComplexStage_ofReal, Complex.ofReal_re]
  change Tendsto (fun N => iteratedDeriv k (gaussianRealStage P lam N) t) atTop
    (𝓝 (iteratedDeriv k (fun y : ℝ => (gaussianEntireLimit P lam y).re) t))
  simpa only [heq] using tendsto_real_iteratedDeriv
    (gaussianComplexStage_differentiable P lam) h.locally_uniform_limit k t

theorem GaussianStageBounds.finite_bounds {P : ℕ → Polynomial ℝ} {lam b : ℕ → ℝ}
    (h : GaussianStageBounds P lam b) (N : ℕ) (t : ℝ) :
    |gaussianRealStage P lam N t - t| ≤ 1 / 16 ∧
      (15 : ℝ) / 16 ≤ deriv (gaussianRealStage P lam N) t ∧
      deriv (gaussianRealStage P lam N) t ≤ 17 / 16 :=
  finiteEntireStage_budget_bounds
    (fun i t => ((gaussianPolynomial_hasDerivAt (P i) t).const_mul (lam i)).differentiableAt)
    h.value_bound h.deriv_bound (fun i => (h.budget_pos i).le) h.budget_half h.budget_first N t

theorem GaussianStageBounds.limit_bounds {P : ℕ → Polynomial ℝ} {lam b : ℕ → ℝ}
    (h : GaussianStageBounds P lam b) (t : ℝ) :
    |realRestriction (gaussianEntireLimit P lam) t - t| ≤ 1 / 16 ∧
      (15 : ℝ) / 16 ≤ deriv (realRestriction (gaussianEntireLimit P lam)) t ∧
      deriv (realRestriction (gaussianEntireLimit P lam)) t ≤ 17 / 16 := by
  have hvalue : Tendsto (fun N => gaussianRealStage P lam N t) atTop
      (𝓝 (realRestriction (gaussianEntireLimit P lam) t)) := by
    simpa only [iteratedDeriv_zero] using h.real_derivative_limit 0 t
  have hderiv : Tendsto (fun N => deriv (gaussianRealStage P lam N) t) atTop
      (𝓝 (deriv (realRestriction (gaussianEntireLimit P lam)) t)) := by
    simpa only [iteratedDeriv_one] using h.real_derivative_limit 1 t
  refine ⟨le_of_tendsto' ((hvalue.sub_const t).abs) (fun N => (h.finite_bounds N t).1),
    ge_of_tendsto' hderiv (fun N => (h.finite_bounds N t).2.1),
    le_of_tendsto' hderiv (fun N => (h.finite_bounds N t).2.2)⟩

theorem GaussianStageBounds.real_differentiable {P : ℕ → Polynomial ℝ} {lam b : ℕ → ℝ}
    (h : GaussianStageBounds P lam b) :
    Differentiable ℝ (realRestriction (gaussianEntireLimit P lam)) :=
  fun t => (h.entire_real_type.1 (t : ℂ)).hasDerivAt.real_of_complex.differentiableAt

theorem GaussianStageBounds.existsUnique_root {P : ℕ → Polynomial ℝ} {lam b : ℕ → ℝ}
    (h : GaussianStageBounds P lam b) :
    ∃! α : ℝ, realRestriction (gaussianEntireLimit P lam) α = 0 :=
  existsUnique_zero_of_bounded_identity_perturbation h.real_differentiable
    (by norm_num : (0 : ℝ) < 15 / 16) (fun t => (h.limit_bounds t).2.1)
    (fun t => (h.limit_bounds t).1)

/-- The finite tail bound is uniform on the entire real line. -/
theorem GaussianStageBounds.finite_tail_bound {P : ℕ → Polynomial ℝ} {lam b : ℕ → ℝ}
    (h : GaussianStageBounds P lam b) (s N : ℕ) (hN : s ≤ N) (t : ℝ) :
    |gaussianRealStage P lam N t - gaussianRealStage P lam s t| ≤ 2 * b s := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  have heq : gaussianRealStage P lam (s + k) t - gaussianRealStage P lam s t =
      ∑ i ∈ Finset.range k, lam (s + i) * gaussianPolynomial (P (s + i)) t := by
    simp [gaussianRealStage, finiteEntireStage, Finset.sum_range_add]
  rw [heq]
  have hsummable : Summable (fun i => b (s + i)) := by
    exact summable_budget (fun i => (h.budget_pos (s + i)).le)
      (fun i => by simpa only [Nat.add_assoc] using h.budget_half (s + i))
  calc
    |∑ i ∈ Finset.range k, lam (s + i) * gaussianPolynomial (P (s + i)) t| ≤
        ∑ i ∈ Finset.range k, b (s + i) :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun i _ => h.value_bound (s + i) t))
    _ ≤ ∑' i, b (s + i) := hsummable.sum_le_tsum _ (fun i _ => (h.budget_pos (s + i)).le)
    _ ≤ 2 * b s := by simpa only [Nat.add_comm] using
      tsum_budget_tail_le_twice (fun i => (h.budget_pos i).le) h.budget_half s

theorem GaussianStageBounds.limit_tail_bound {P : ℕ → Polynomial ℝ} {lam b : ℕ → ℝ}
    (h : GaussianStageBounds P lam b) (s : ℕ) (t : ℝ) :
    |realRestriction (gaussianEntireLimit P lam) t - gaussianRealStage P lam s t| ≤ 2 * b s := by
  have hvalue : Tendsto (fun N => gaussianRealStage P lam N t) atTop
      (𝓝 (realRestriction (gaussianEntireLimit P lam) t)) := by
    simpa only [iteratedDeriv_zero] using h.real_derivative_limit 0 t
  apply le_of_tendsto ((hvalue.sub_const (gaussianRealStage P lam s t)).abs)
  exact (eventually_ge_atTop s).mono (fun N hN => h.finite_tail_bound s N hN t)

theorem GaussianStageBounds.root_displacement {P : ℕ → Polynomial ℝ} {lam b : ℕ → ℝ}
    (h : GaussianStageBounds P lam b) (s : ℕ) {α a : ℝ}
    (hα : realRestriction (gaussianEntireLimit P lam) α = 0)
    (ha : gaussianRealStage P lam (s + 1) a = 0) : |α - a| ≤ 4 * b (s + 1) := by
  have hv : |realRestriction (gaussianEntireLimit P lam) a| ≤ 2 * b (s + 1) := by
    simpa only [ha, sub_zero] using h.limit_tail_bound (s + 1) a
  have hdist := distance_to_zero_le_value_div h.real_differentiable
    (by norm_num : (0 : ℝ) < 1 / 2)
    (fun t => by have ht := (h.limit_bounds t).2.1; linarith) hα a
  rw [abs_sub_comm] at hdist
  exact hdist.trans (by nlinarith)

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
  apply tendsto_nhds_unique (D.bounds.real_derivative_limit k z)
  apply tendsto_const_nhds.congr'
  exact (eventually_ge_atTop (s + 1)).mono
    (fun N hN => (D.jets_preserved s j z k hquery N hN).symm)

/-- Every adaptive decision and output agrees exactly with the saved finite execution. -/
theorem GaussianAdversarialStages.output_preserved {n : ℕ} {A : RealAlgorithm n}
    {B : ℝ} {exponent : ℕ → ℝ} (D : GaussianAdversarialStages A B exponent) (s : ℕ) :
    A.run (realRestriction (gaussianEntireLimit D.polynomial D.scale)) (D.starts s) =
      gaussianStageOutput A D.polynomial D.scale D.starts s := by
  symm
  apply A.run_eq_of_derivatives_eq
  intro j z k hquery
  exact (D.limit_jet_eq s j z k hquery).symm

theorem GaussianAdversarialStages.relative_root_bounds {n : ℕ} {A : RealAlgorithm n}
    {B : ℝ} {exponent : ℕ → ℝ} (D : GaussianAdversarialStages A B exponent)
    {α : ℝ} (hα : realRestriction (gaussianEntireLimit D.polynomial D.scale) α = 0) (s : ℕ) :
    |α - D.roots s| ≤ D.epsilon s / 8 ∧ |α - D.roots s| ≤
      |gaussianStageOutput A D.polynomial D.scale D.starts s - D.roots s| / 8 := by
  have h := root_displacement_of_budget
    (D.bounds.root_displacement s hα (D.stage_root s))
    (D.next_budget_error s) (D.next_budget_scale s)
  exact ⟨h.2, h.1⟩

theorem GaussianAdversarialStages.start_distance_bounds {n : ℕ} {A : RealAlgorithm n}
    {B : ℝ} {exponent : ℕ → ℝ} (D : GaussianAdversarialStages A B exponent)
    {α : ℝ} (hα : realRestriction (gaussianEntireLimit D.polynomial D.scale) α = 0) (s : ℕ) :
    (5 / 8 : ℝ) * D.epsilon s ≤ D.starts s - α ∧
      D.starts s - α ≤ (11 / 8 : ℝ) * D.epsilon s := by
  have h := D.relative_root_bounds hα s
  have hs := stage_root_error_bounds (D.start_lower s) (D.start_upper s) h.1 h.2
  exact ⟨hs.1, hs.2.1⟩

theorem GaussianAdversarialStages.starts_ne_root {n : ℕ} {A : RealAlgorithm n}
    {B : ℝ} {exponent : ℕ → ℝ} (D : GaussianAdversarialStages A B exponent)
    {α : ℝ} (hα : realRestriction (gaussianEntireLimit D.polynomial D.scale) α = 0) (s : ℕ) :
    D.starts s ≠ α := by
  have h := (D.start_distance_bounds hα s).1
  have he := D.epsilon_pos s
  exact ne_of_gt (by linarith)

theorem GaussianAdversarialStages.starts_tendsto {n : ℕ} {A : RealAlgorithm n}
    {B : ℝ} {exponent : ℕ → ℝ} (D : GaussianAdversarialStages A B exponent)
    {α : ℝ} (hα : realRestriction (gaussianEntireLimit D.polynomial D.scale) α = 0) :
    Tendsto D.starts atTop (𝓝 α) := by
  have heps : Tendsto D.epsilon atTop (𝓝 0) :=
    squeeze_zero (fun s => (D.epsilon_pos s).le) (fun s => (D.epsilon_cap s).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg) (g := fun s => 2 * D.epsilon s)
  · intro s
    have hb := D.start_distance_bounds hα s
    have he := D.epsilon_pos s
    rw [Real.dist_eq, abs_of_pos (by linarith : 0 < D.starts s - α)]
    linarith
  · simpa using heps.const_mul 2

theorem GaussianAdversarialStages.ratio_stage_bound {n : ℕ} {A : RealAlgorithm n}
    {B : ℝ} {exponent : ℕ → ℝ} (D : GaussianAdversarialStages A B exponent)
    (hp : ∀ s, 0 ≤ exponent s) {α : ℝ}
    (hα : realRestriction (gaussianEntireLimit D.polynomial D.scale) α = 0) (s : ℕ) :
    (s : ℝ) + 1 ≤ errorRatio A.run
      (realRestriction (gaussianEntireLimit D.polynomial D.scale)) α (exponent s) (D.starts s) := by
  have ht := D.relative_root_bounds hα s
  have hs := stage_error_ratio_lower_bound (D.epsilon_pos s) (hp s)
    (D.start_lower s) (D.start_upper s) ht.1 ht.2 (D.error_bound s) (D.amplification s)
  simpa only [errorRatio, D.output_preserved s, Real.rpow_eq_pow] using hs.2

/-- The limit is explicitly the Gaussian series. Existence and uniqueness of its real
root, all witness properties, and the full stage ratio estimates are conclusions. -/
theorem GaussianAdversarialStages.assemble {n : ℕ} {A : RealAlgorithm n}
    {B : ℝ} {exponent : ℕ → ℝ} (D : GaussianAdversarialStages A B exponent)
    (hp : ∀ s, 0 ≤ exponent s) :
    ∃ α : ℝ, EntireWitnessData (gaussianEntireLimit D.polynomial D.scale) α D.starts ∧
      ∀ s : ℕ, (s : ℝ) + 1 ≤ errorRatio A.run
        (realRestriction (gaussianEntireLimit D.polynomial D.scale)) α (exponent s) (D.starts s) := by
  obtain ⟨α, hα, hunique⟩ := D.bounds.existsUnique_root
  refine ⟨α, ⟨D.bounds.entire_real_type, ?_, hα, hunique,
    D.starts_tendsto hα, D.starts_ne_root hα⟩, D.ratio_stage_bound hp hα⟩
  intro t
  have h := D.bounds.limit_bounds t
  constructor <;> linarith [h.2.1, h.2.2]

/-- An entire counterexample at a fixed exponent from the discrete stage data. -/
theorem entireCounterexample_of_gaussian_stages {n : ℕ} {A : RealAlgorithm n}
    {B p : ℝ} (D : GaussianAdversarialStages A B (fun _ => p)) (hp : 0 ≤ p) :
    EntireCounterexample A.run p := by
  obtain ⟨α, hwitness, hstage⟩ := D.assemble (fun _ => hp)
  refine ⟨gaussianEntireLimit D.polynomial D.scale, α, D.starts, hwitness, ?_⟩
  apply tendsto_atTop_mono (fun s : ℕ =>
    le_trans (by linarith : (s : ℝ) ≤ (s : ℝ) + 1) (hstage s))
  exact tendsto_natCast_atTop_atTop

/-- One constructed stage sequence with the moving exponents gives the same entire
function and starts for every fixed exponent above B. -/
theorem simultaneousEntireCounterexample_of_gaussian_stages {n : ℕ} {A : RealAlgorithm n}
    {B : ℝ} (D : GaussianAdversarialStages A B (fun s => B + 1 / ((s : ℝ) + 1)))
    (hB : 0 ≤ B) : SimultaneousEntireCounterexample A.run B := by
  have hp : ∀ s : ℕ, 0 ≤ B + 1 / ((s : ℝ) + 1) := fun s => by positivity
  obtain ⟨α, hwitness, hstage⟩ := D.assemble hp
  refine ⟨gaussianEntireLimit D.polynomial D.scale, α, D.starts, hwitness, ?_⟩
  intro p hpB
  apply simultaneous_ratio_divergence
    (fun _ => abs_nonneg _) (fun s => abs_pos.mpr (sub_ne_zero.mpr (D.starts_ne_root hwitness.2.2.1 s)))
    ?_ hstage p hpB
  apply Eventually.of_forall
  intro s
  have hb := D.start_distance_bounds hwitness.2.2.1 s
  have he := D.epsilon_pos s
  have hcap := D.epsilon_quarter s
  rw [abs_of_pos (by linarith : 0 < D.starts s - α)]
  linarith

end KungTraub
