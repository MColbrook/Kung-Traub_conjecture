import KungTraub.DerivativeObservations
import KungTraub.DiagonalEstimates

/-!
# Finite stages of the entire construction

The finite-stage algebra and estimates in Section 4 of Matthew J. Colbrook's
manuscript. The actual polynomial product prescribing
old derivative observations is constructed explicitly. Its corrections preserve
those observations exactly, while finite sums retain the Gaussian-polynomial form.
Budget estimates supply the finite-stage derivative and root bounds.

Polynomial product/divisibility and finite-sum differentiation use mathlib; exact
execution preservation uses the existing `Transcripts` module.
-/

noncomputable section

open scoped BigOperators ContDiff

namespace KungTraub

def pastQueryPolynomial (Z : Finset ℝ) (orders : ℝ → ℕ) : Polynomial ℝ :=
  ∏ z ∈ Z, (Polynomial.X - Polynomial.C z) ^ (orders z + 1)

theorem pastQueryPolynomial_empty (orders : ℝ → ℕ) : pastQueryPolynomial ∅ orders = 1 := by
  simp [pastQueryPolynomial]

theorem pastQueryPolynomial_monic (Z : Finset ℝ) (orders : ℝ → ℕ) :
    (pastQueryPolynomial Z orders).Monic :=
  Polynomial.monic_prod_of_monic Z _ fun z _ => (Polynomial.monic_X_sub_C z).pow _

theorem pastQueryPolynomial_ne_zero (Z : Finset ℝ) (orders : ℝ → ℕ) :
    pastQueryPolynomial Z orders ≠ 0 := (pastQueryPolynomial_monic Z orders).ne_zero

theorem pastQueryPolynomial_factor_dvd {Z : Finset ℝ} (orders : ℝ → ℕ)
    {z : ℝ} (hz : z ∈ Z) :
    (Polynomial.X - Polynomial.C z) ^ (orders z + 1) ∣ pastQueryPolynomial Z orders :=
  Finset.dvd_prod_of_mem _ hz

theorem pastQueryPolynomial_eval_ne_zero {Z : Finset ℝ} (orders : ℝ → ℕ)
    {a : ℝ} (ha : a ∉ Z) : (pastQueryPolynomial Z orders).eval a ≠ 0 := by
  classical
  simp only [pastQueryPolynomial, Polynomial.eval_prod, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  apply Finset.prod_ne_zero_iff.mpr
  intro z hz
  exact pow_ne_zero _ (sub_ne_zero.mpr (fun heq => ha (heq.symm ▸ hz)))

/-- Previously preserved nonzero values exclude the old root from the multiplier's nodes. -/
theorem pastQueryPolynomial_eval_ne_zero_at_root {f : ℝ → ℝ} {Z : Finset ℝ}
    (orders : ℝ → ℕ) {a : ℝ} (hroot : f a = 0) (hvalues : ∀ z ∈ Z, f z ≠ 0) :
    (pastQueryPolynomial Z orders).eval a ≠ 0 := by
  apply pastQueryPolynomial_eval_ne_zero orders
  intro ha
  exact hvalues a ha hroot

theorem pastQuery_weight_ne_zero_at_root {f : ℝ → ℝ} {Z : Finset ℝ}
    (orders : ℝ → ℕ) {a lam : ℝ} (hlam : 0 < lam)
    (hroot : f a = 0) (hvalues : ∀ z ∈ Z, f z ≠ 0) :
    lam * gaussianPolynomial (pastQueryPolynomial Z orders) a ≠ 0 :=
  mul_ne_zero hlam.ne' (gaussianPolynomial_ne_zero
    (pastQueryPolynomial_eval_ne_zero_at_root orders hroot hvalues))

/-- The concrete multiplier annihilates every earlier requested derivative order. -/
theorem pastQuery_gaussian_correction_jet_zero {Z : Finset ℝ} (orders : ℝ → ℕ)
    {z : ℝ} (hz : z ∈ Z) {k : ℕ} (hk : k ≤ orders z)
    (n : ℕ) (lam ε x : ℝ) (u : EuclideanSpace ℝ (Fin (n + 1))) :
    iteratedDeriv k (gaussianCorrection (pastQueryPolynomial Z orders) n lam ε x u) z = 0 :=
  gaussianCorrectionPolynomial_iteratedDeriv_eq_zero (pastQueryPolynomial_factor_dvd orders hz)
    hk n ε x lam u

/-- The actual multiplier has a positive scale chosen before the family parameters,
with global real bounds, the prescribed complex-disc bound and a nonzero old-root value. -/
theorem pastQuery_exists_small_correction {f : ℝ → ℝ} {Z : Finset ℝ}
    (orders : ℝ → ℕ) {a : ℝ} (hroot : f a = 0) (hvalues : ∀ z ∈ Z, f z ≠ 0)
    (n : ℕ) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 < b) :
    ∃ lam > 0, lam * gaussianPolynomial (pastQueryPolynomial Z orders) a ≠ 0 ∧
      GaussianCorrectionSmall (pastQueryPolynomial Z orders) n lam b ∧
      ∀ ε x : ℝ, 0 ≤ ε → ε ≤ 1 → |x| ≤ 1 →
        ∀ u : EuclideanSpace ℝ (Fin (n + 1)), ‖u‖ ≤ 1 →
          ∀ z : ℂ, ‖z‖ ≤ R →
            ‖(lam : ℂ) * complexGaussianPolynomial
              (gaussianCorrectionPolynomial (pastQueryPolynomial Z orders) n ε x u) z‖ ≤ b := by
  obtain ⟨lam, hlam, hbound⟩ :=
    gaussianCorrectionPolynomial_exists_small_scaling (pastQueryPolynomial Z orders) n R hb
  refine ⟨lam, hlam, pastQuery_weight_ne_zero_at_root orders hlam hroot hvalues,
    gaussianCorrectionSmall_of_three_bounds hR hbound, ?_⟩
  intro ε x hε0 hε1 hx u hu z hz
  have h := hbound ε x hε0 hε1 hx u hu 0 0 z hz
  linarith [abs_nonneg (lam * gaussianPolynomial
    (gaussianCorrectionPolynomial (pastQueryPolynomial Z orders) n ε x u) 0),
    abs_nonneg (deriv (fun y => lam * gaussianPolynomial
      (gaussianCorrectionPolynomial (pastQueryPolynomial Z orders) n ε x u) y) 0)]

/-- Adding the correction preserves the old derivatives literally, without approximation. -/
theorem pastQuery_gaussian_correction_preserves_jet {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) {Z : Finset ℝ} (orders : ℝ → ℕ) {z : ℝ}
    (hz : z ∈ Z) {k : ℕ} (hk : k ≤ orders z) (n : ℕ) (lam ε x : ℝ)
    (u : EuclideanSpace ℝ (Fin (n + 1))) :
    iteratedDeriv k (fun t => f t +
      gaussianCorrection (pastQueryPolynomial Z orders) n lam ε x u t) z = iteratedDeriv k f z := by
  have hg : ContDiff ℝ ∞ (gaussianCorrection (pastQueryPolynomial Z orders) n lam ε x u) :=
    contDiff_const.mul (gaussianPolynomial_contDiff _)
  have hkfinite : (k : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  rw [iteratedDeriv_fun_add (hf.contDiffAt.of_le hkfinite) (hg.contDiffAt.of_le hkfinite),
    pastQuery_gaussian_correction_jet_zero orders hz hk, add_zero]

/-- In particular every previously preserved nonzero value remains nonzero. -/
theorem pastQuery_gaussian_correction_preserves_nonzero {f : ℝ → ℝ}
    {Z : Finset ℝ} (orders : ℝ → ℕ) (hvalues : ∀ z ∈ Z, f z ≠ 0)
    (n : ℕ) (lam ε x : ℝ) (u : EuclideanSpace ℝ (Fin (n + 1))) :
    ∀ z ∈ Z, f z + gaussianCorrection (pastQueryPolynomial Z orders) n lam ε x u z ≠ 0 := by
  intro z hz
  have hg := pastQuery_gaussian_correction_jet_zero orders hz (Nat.zero_le (orders z)) n lam ε x u
  simp only [iteratedDeriv_zero] at hg
  simpa only [hg, add_zero] using hvalues z hz

/-- Covering the actual old execution's queries is enough to preserve its complete output. -/
theorem pastQuery_gaussian_correction_preserves_run {slots : ℕ} (A : RealAlgorithm slots)
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {Z : Finset ℝ} (orders : ℝ → ℕ) (start : ℝ)
    (hcover : ∀ j z k, A.actualQuery f start j = .derivative z k → z ∈ Z ∧ k ≤ orders z)
    (n : ℕ) (lam ε x : ℝ) (u : EuclideanSpace ℝ (Fin (n + 1))) :
    A.run f start = A.run (fun t => f t +
      gaussianCorrection (pastQueryPolynomial Z orders) n lam ε x u t) start := by
  apply A.run_eq_of_derivatives_eq
  intro j z k hquery
  obtain ⟨hz, hk⟩ := hcover j z k hquery
  exact (pastQuery_gaussian_correction_preserves_jet hf orders hz hk n lam ε x u).symm

/-- One correction preserves the exact finite-stage Gaussian-polynomial form. -/
theorem gaussian_stage_add_correction (p₀ p : Polynomial ℝ) (n : ℕ)
    (lam ε x : ℝ) (u : EuclideanSpace ℝ (Fin (n + 1))) (t : ℝ) :
    t + gaussianPolynomial p₀ t + gaussianCorrection p n lam ε x u t =
      t + gaussianPolynomial (p₀ + Polynomial.C lam * gaussianCorrectionPolynomial p n ε x u) t := by
  simp [gaussianCorrection, gaussianPolynomial]
  ring

/-- Stage `s` contains precisely corrections `0,...,s-1`; correction zero is paper stage one. -/
def finiteEntireStage (g : ℕ → ℝ → ℝ) (s : ℕ) (t : ℝ) : ℝ :=
  t + ∑ i ∈ Finset.range s, g i t

theorem finiteEntireStage_zero (g : ℕ → ℝ → ℝ) : finiteEntireStage g 0 = id := by
  ext t
  simp [finiteEntireStage]

theorem finiteEntireStage_succ (g : ℕ → ℝ → ℝ) (s : ℕ) (t : ℝ) :
    finiteEntireStage g (s + 1) t = finiteEntireStage g s t + g s t := by
  simp [finiteEntireStage, Finset.sum_range_succ, add_assoc]

theorem finiteEntireStage_gaussian_form (P : ℕ → Polynomial ℝ) (lam : ℕ → ℝ) (s : ℕ) :
    finiteEntireStage (fun i t => lam i * gaussianPolynomial (P i) t) s =
      fun t => t + gaussianPolynomial (∑ i ∈ Finset.range s, Polynomial.C (lam i) * P i) t := by
  ext t
  simp [finiteEntireStage, gaussianPolynomial, Polynomial.eval_finsetSum,
    Finset.mul_sum, mul_assoc, mul_comm]

/-- Every finite Gaussian stage has an actual entire extension agreeing on the real axis. -/
theorem finiteEntireStage_gaussian_entire_extension (P : ℕ → Polynomial ℝ)
    (lam : ℕ → ℝ) (s : ℕ) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ ∀ t : ℝ,
      F (t : ℂ) = (finiteEntireStage (fun i y => lam i * gaussianPolynomial (P i) y) s t : ℂ) := by
  let Q : Polynomial ℝ := ∑ i ∈ Finset.range s, Polynomial.C (lam i) * P i
  refine ⟨fun z => z + complexGaussianPolynomial Q z,
    differentiable_id.add (complexGaussianPolynomial_differentiable Q), ?_⟩
  intro t
  rw [finiteEntireStage_gaussian_form]
  simp only [complexGaussianPolynomial_ofReal, Complex.ofReal_add]
  rfl

theorem finiteEntireStage_hasDerivAt {g : ℕ → ℝ → ℝ}
    (hg : ∀ i, Differentiable ℝ (g i)) (s : ℕ) (t : ℝ) :
    HasDerivAt (finiteEntireStage g s) (1 + ∑ i ∈ Finset.range s, deriv (g i) t) t :=
  (hasDerivAt_id t).fun_add (HasDerivAt.fun_sum (fun i _ => (hg i t).hasDerivAt))

/-- A finite correction sum stays within the sum of its individual value budgets. -/
theorem finiteEntireStage_identity_deviation {g : ℕ → ℝ → ℝ} {b : ℕ → ℝ}
    (hbound : ∀ i t, |g i t| ≤ b i) (s : ℕ) (t : ℝ) :
    |finiteEntireStage g s t - t| ≤ ∑ i ∈ Finset.range s, b i := by
  simp only [finiteEntireStage, add_sub_cancel_left]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => hbound i t))

/-- The derivative remains within the sum of the derivative budgets of one. -/
theorem finiteEntireStage_derivative_deviation {g : ℕ → ℝ → ℝ} {b : ℕ → ℝ}
    (hg : ∀ i, Differentiable ℝ (g i))
    (hbound : ∀ i t, |deriv (g i) t| ≤ b i) (s : ℕ) (t : ℝ) :
    |deriv (finiteEntireStage g s) t - 1| ≤ ∑ i ∈ Finset.range s, b i := by
  rw [(finiteEntireStage_hasDerivAt hg s t).deriv, add_sub_cancel_left]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => hbound i t))

/-- Every finite budget prefix satisfies the same `1/16` bound as the full series. -/
theorem sum_budget_range_le_one_sixteenth {b : ℕ → ℝ} (hpos : ∀ i, 0 ≤ b i)
    (hstep : ∀ i, b (i + 1) ≤ b i / 2) (hfirst : b 0 ≤ 1 / 32) (s : ℕ) :
    (∑ i ∈ Finset.range s, b i) ≤ 1 / 16 :=
  ((summable_budget hpos hstep).sum_le_tsum (Finset.range s) (fun i _ => hpos i)).trans
    (tsum_budget_le_one_sixteenth hpos hstep hfirst)

/-- Exact finite-stage estimates from the manuscript's summable budgets, on all of `ℝ`. -/
theorem finiteEntireStage_budget_bounds {g : ℕ → ℝ → ℝ} {b : ℕ → ℝ}
    (hg : ∀ i, Differentiable ℝ (g i))
    (hvalue : ∀ i t, |g i t| ≤ b i) (hderiv : ∀ i t, |deriv (g i) t| ≤ b i)
    (hpos : ∀ i, 0 ≤ b i) (hstep : ∀ i, b (i + 1) ≤ b i / 2)
    (hfirst : b 0 ≤ 1 / 32) (s : ℕ) (t : ℝ) :
    |finiteEntireStage g s t - t| ≤ 1 / 16 ∧
      (15 : ℝ) / 16 ≤ deriv (finiteEntireStage g s) t ∧
      deriv (finiteEntireStage g s) t ≤ 17 / 16 := by
  have hbudget := sum_budget_range_le_one_sixteenth hpos hstep hfirst s
  refine ⟨(finiteEntireStage_identity_deviation hvalue s t).trans hbudget, ?_⟩
  have hd := abs_le.mp ((finiteEntireStage_derivative_deviation hg hderiv s t).trans hbudget)
  constructor <;> linarith

/-- Every finite stage has one real root; global existence uses its bounded
difference from the identity as well as its positive derivative. -/
theorem finiteEntireStage_existsUnique_root {g : ℕ → ℝ → ℝ} {b : ℕ → ℝ}
    (hg : ∀ i, Differentiable ℝ (g i))
    (hvalue : ∀ i t, |g i t| ≤ b i) (hderiv : ∀ i t, |deriv (g i) t| ≤ b i)
    (hpos : ∀ i, 0 ≤ b i) (hstep : ∀ i, b (i + 1) ≤ b i / 2)
    (hfirst : b 0 ≤ 1 / 32) (s : ℕ) : ∃! a : ℝ, finiteEntireStage g s a = 0 := by
  apply existsUnique_zero_of_bounded_identity_perturbation
    (m := (15 : ℝ) / 16) (B := (1 : ℝ) / 16)
  · exact fun t => (finiteEntireStage_hasDerivAt hg s t).differentiableAt
  · norm_num
  · intro t
    exact (finiteEntireStage_budget_bounds hg hvalue hderiv hpos hstep hfirst s t).2.1
  · intro t
    exact (finiteEntireStage_budget_bounds hg hvalue hderiv hpos hstep hfirst s t).1

/-- The real root stays in the source's central interval, with the stronger bound `1/16`. -/
theorem finiteEntireStage_root_abs_bound {g : ℕ → ℝ → ℝ} {b : ℕ → ℝ}
    (hvalue : ∀ i t, |g i t| ≤ b i)
    (hpos : ∀ i, 0 ≤ b i) (hstep : ∀ i, b (i + 1) ≤ b i / 2)
    (hfirst : b 0 ≤ 1 / 32) (s : ℕ) {a : ℝ} (hroot : finiteEntireStage g s a = 0) :
    |a| ≤ 1 / 16 :=
  abs_zero_le_perturbation_bound (fun t => (finiteEntireStage_identity_deviation hvalue s t).trans
    (sum_budget_range_le_one_sixteenth hpos hstep hfirst s)) hroot

end KungTraub
