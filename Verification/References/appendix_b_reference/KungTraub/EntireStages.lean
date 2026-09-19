import appendix_b_reference.KungTraub.DerivativeObservations
import appendix_b_reference.KungTraub.DiagonalEstimates

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
  sorry

theorem pastQueryPolynomial_monic (Z : Finset ℝ) (orders : ℝ → ℕ) :
    (pastQueryPolynomial Z orders).Monic := by
  sorry

theorem pastQueryPolynomial_ne_zero (Z : Finset ℝ) (orders : ℝ → ℕ) :
    pastQueryPolynomial Z orders ≠ 0 := by
  sorry

theorem pastQueryPolynomial_factor_dvd {Z : Finset ℝ} (orders : ℝ → ℕ)
    {z : ℝ} (hz : z ∈ Z) :
    (Polynomial.X - Polynomial.C z) ^ (orders z + 1) ∣ pastQueryPolynomial Z orders := by
  sorry

theorem pastQueryPolynomial_eval_ne_zero {Z : Finset ℝ} (orders : ℝ → ℕ)
    {a : ℝ} (ha : a ∉ Z) : (pastQueryPolynomial Z orders).eval a ≠ 0 := by
  sorry

/-- Previously preserved nonzero values exclude the old root from the multiplier's nodes. -/
theorem pastQueryPolynomial_eval_ne_zero_at_root {f : ℝ → ℝ} {Z : Finset ℝ}
    (orders : ℝ → ℕ) {a : ℝ} (hroot : f a = 0) (hvalues : ∀ z ∈ Z, f z ≠ 0) :
    (pastQueryPolynomial Z orders).eval a ≠ 0 := by
  sorry

theorem pastQuery_weight_ne_zero_at_root {f : ℝ → ℝ} {Z : Finset ℝ}
    (orders : ℝ → ℕ) {a lam : ℝ} (hlam : 0 < lam)
    (hroot : f a = 0) (hvalues : ∀ z ∈ Z, f z ≠ 0) :
    lam * gaussianPolynomial (pastQueryPolynomial Z orders) a ≠ 0 := by
  sorry

/-- The concrete multiplier annihilates every earlier requested derivative order. -/
theorem pastQuery_gaussian_correction_jet_zero {Z : Finset ℝ} (orders : ℝ → ℕ)
    {z : ℝ} (hz : z ∈ Z) {k : ℕ} (hk : k ≤ orders z)
    (n : ℕ) (lam ε x : ℝ) (u : EuclideanSpace ℝ (Fin (n + 1))) :
    iteratedDeriv k (gaussianCorrection (pastQueryPolynomial Z orders) n lam ε x u) z = 0 := by
  sorry

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
  sorry

/-- Adding the correction preserves the old derivatives literally, without approximation. -/
theorem pastQuery_gaussian_correction_preserves_jet {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) {Z : Finset ℝ} (orders : ℝ → ℕ) {z : ℝ}
    (hz : z ∈ Z) {k : ℕ} (hk : k ≤ orders z) (n : ℕ) (lam ε x : ℝ)
    (u : EuclideanSpace ℝ (Fin (n + 1))) :
    iteratedDeriv k (fun t => f t +
      gaussianCorrection (pastQueryPolynomial Z orders) n lam ε x u t) z = iteratedDeriv k f z := by
  sorry

/-- In particular every previously preserved nonzero value remains nonzero. -/
theorem pastQuery_gaussian_correction_preserves_nonzero {f : ℝ → ℝ}
    {Z : Finset ℝ} (orders : ℝ → ℕ) (hvalues : ∀ z ∈ Z, f z ≠ 0)
    (n : ℕ) (lam ε x : ℝ) (u : EuclideanSpace ℝ (Fin (n + 1))) :
    ∀ z ∈ Z, f z + gaussianCorrection (pastQueryPolynomial Z orders) n lam ε x u z ≠ 0 := by
  sorry

/-- Covering the actual old execution's queries is enough to preserve its complete output. -/
theorem pastQuery_gaussian_correction_preserves_run {slots : ℕ} (A : RealAlgorithm slots)
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {Z : Finset ℝ} (orders : ℝ → ℕ) (start : ℝ)
    (hcover : ∀ j z k, A.actualQuery f start j = .derivative z k → z ∈ Z ∧ k ≤ orders z)
    (n : ℕ) (lam ε x : ℝ) (u : EuclideanSpace ℝ (Fin (n + 1))) :
    A.run f start = A.run (fun t => f t +
      gaussianCorrection (pastQueryPolynomial Z orders) n lam ε x u t) start := by
  sorry

/-- One correction preserves the exact finite-stage Gaussian-polynomial form. -/
theorem gaussian_stage_add_correction (p₀ p : Polynomial ℝ) (n : ℕ)
    (lam ε x : ℝ) (u : EuclideanSpace ℝ (Fin (n + 1))) (t : ℝ) :
    t + gaussianPolynomial p₀ t + gaussianCorrection p n lam ε x u t =
      t + gaussianPolynomial (p₀ + Polynomial.C lam * gaussianCorrectionPolynomial p n ε x u) t := by
  sorry

/-- Stage `s` contains precisely corrections `0,...,s-1`; correction zero is paper stage one. -/
def finiteEntireStage (g : ℕ → ℝ → ℝ) (s : ℕ) (t : ℝ) : ℝ :=
  t + ∑ i ∈ Finset.range s, g i t

theorem finiteEntireStage_zero (g : ℕ → ℝ → ℝ) : finiteEntireStage g 0 = id := by
  sorry

theorem finiteEntireStage_succ (g : ℕ → ℝ → ℝ) (s : ℕ) (t : ℝ) :
    finiteEntireStage g (s + 1) t = finiteEntireStage g s t + g s t := by
  sorry

theorem finiteEntireStage_gaussian_form (P : ℕ → Polynomial ℝ) (lam : ℕ → ℝ) (s : ℕ) :
    finiteEntireStage (fun i t => lam i * gaussianPolynomial (P i) t) s =
      fun t => t + gaussianPolynomial (∑ i ∈ Finset.range s, Polynomial.C (lam i) * P i) t := by
  sorry

/-- Every finite Gaussian stage has an actual entire extension agreeing on the real axis. -/
theorem finiteEntireStage_gaussian_entire_extension (P : ℕ → Polynomial ℝ)
    (lam : ℕ → ℝ) (s : ℕ) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧ ∀ t : ℝ,
      F (t : ℂ) = (finiteEntireStage (fun i y => lam i * gaussianPolynomial (P i) y) s t : ℂ) := by
  sorry

theorem finiteEntireStage_hasDerivAt {g : ℕ → ℝ → ℝ}
    (hg : ∀ i, Differentiable ℝ (g i)) (s : ℕ) (t : ℝ) :
    HasDerivAt (finiteEntireStage g s) (1 + ∑ i ∈ Finset.range s, deriv (g i) t) t := by
  sorry

/-- A finite correction sum stays within the sum of its individual value budgets. -/
theorem finiteEntireStage_identity_deviation {g : ℕ → ℝ → ℝ} {b : ℕ → ℝ}
    (hbound : ∀ i t, |g i t| ≤ b i) (s : ℕ) (t : ℝ) :
    |finiteEntireStage g s t - t| ≤ ∑ i ∈ Finset.range s, b i := by
  sorry

/-- The derivative remains within the sum of the derivative budgets of one. -/
theorem finiteEntireStage_derivative_deviation {g : ℕ → ℝ → ℝ} {b : ℕ → ℝ}
    (hg : ∀ i, Differentiable ℝ (g i))
    (hbound : ∀ i t, |deriv (g i) t| ≤ b i) (s : ℕ) (t : ℝ) :
    |deriv (finiteEntireStage g s) t - 1| ≤ ∑ i ∈ Finset.range s, b i := by
  sorry

/-- Every finite budget prefix satisfies the same `1/16` bound as the full series. -/
theorem sum_budget_range_le_one_sixteenth {b : ℕ → ℝ} (hpos : ∀ i, 0 ≤ b i)
    (hstep : ∀ i, b (i + 1) ≤ b i / 2) (hfirst : b 0 ≤ 1 / 32) (s : ℕ) :
    (∑ i ∈ Finset.range s, b i) ≤ 1 / 16 := by
  sorry

/-- Exact finite-stage estimates from the manuscript's summable budgets, on all of `ℝ`. -/
theorem finiteEntireStage_budget_bounds {g : ℕ → ℝ → ℝ} {b : ℕ → ℝ}
    (hg : ∀ i, Differentiable ℝ (g i))
    (hvalue : ∀ i t, |g i t| ≤ b i) (hderiv : ∀ i t, |deriv (g i) t| ≤ b i)
    (hpos : ∀ i, 0 ≤ b i) (hstep : ∀ i, b (i + 1) ≤ b i / 2)
    (hfirst : b 0 ≤ 1 / 32) (s : ℕ) (t : ℝ) :
    |finiteEntireStage g s t - t| ≤ 1 / 16 ∧
      (15 : ℝ) / 16 ≤ deriv (finiteEntireStage g s) t ∧
      deriv (finiteEntireStage g s) t ≤ 17 / 16 := by
  sorry

/-- Every finite stage has one real root; global existence uses its bounded
difference from the identity as well as its positive derivative. -/
theorem finiteEntireStage_existsUnique_root {g : ℕ → ℝ → ℝ} {b : ℕ → ℝ}
    (hg : ∀ i, Differentiable ℝ (g i))
    (hvalue : ∀ i t, |g i t| ≤ b i) (hderiv : ∀ i t, |deriv (g i) t| ≤ b i)
    (hpos : ∀ i, 0 ≤ b i) (hstep : ∀ i, b (i + 1) ≤ b i / 2)
    (hfirst : b 0 ≤ 1 / 32) (s : ℕ) : ∃! a : ℝ, finiteEntireStage g s a = 0 := by
  sorry

/-- The real root stays in the source's central interval, with the stronger bound `1/16`. -/
theorem finiteEntireStage_root_abs_bound {g : ℕ → ℝ → ℝ} {b : ℕ → ℝ}
    (hvalue : ∀ i t, |g i t| ≤ b i)
    (hpos : ∀ i, 0 ≤ b i) (hstep : ∀ i, b (i + 1) ≤ b i / 2)
    (hfirst : b 0 ≤ 1 / 32) (s : ℕ) {a : ℝ} (hroot : finiteEntireStage g s a = 0) :
    |a| ≤ 1 / 16 := by
  sorry

end KungTraub
