import appendix_b_reference.KungTraub.AffineTranscripts
import appendix_b_reference.KungTraub.EntireFamilies
import Mathlib.Analysis.Calculus.ContDiff.Polynomial

/-!
# Exact affine forms of derivative observations

Derivative observations on the finite affine families in Matthew J. Colbrook's
manuscript, for every derivative order including zero.
The parameter domain is the whole Euclidean coefficient space; no restriction on
the decision rules or the query locations is introduced. The idle query has zero
answer and no location.

Mathlib's iterated-derivative rules for addition, finite sums and constant scalar
multiplication, in the module by Chris Birkbeck and Ruben Van de Velde, supply the
analytic identities. Polynomial smoothness uses Geoffrey Irving's mathlib module.
-/

noncomputable section

open scoped BigOperators ContDiff

namespace KungTraub

def finiteAffineFamily {d : ℕ} (f : ℝ → ℝ) (basis : Fin d → ℝ → ℝ)
    (u : EuclideanSpace ℝ (Fin d)) (t : ℝ) : ℝ :=
  f t + ∑ i : Fin d, u i * basis i t

/-- The linear part of evaluation of a fixed derivative, on the entire coefficient space. -/
def derivativeObservationLinearMap {d : ℕ} (basis : Fin d → ℝ → ℝ) (z : ℝ) (k : ℕ) :
    EuclideanSpace ℝ (Fin d) →ₗ[ℝ] ℝ where
  toFun u := ∑ i : Fin d, u i * iteratedDeriv k (basis i) z
  map_add' u v := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c u := by simp [mul_assoc, Finset.mul_sum]

theorem derivativeObservationLinearMap_apply {d : ℕ} (basis : Fin d → ℝ → ℝ)
    (z : ℝ) (k : ℕ) (u : EuclideanSpace ℝ (Fin d)) :
    derivativeObservationLinearMap basis z k u =
      ∑ i : Fin d, u i * iteratedDeriv k (basis i) z := by
  sorry

/-- Only local differentiability through the requested finite order is needed. -/
theorem iteratedDeriv_finiteAffineFamily {d : ℕ} {f : ℝ → ℝ}
    {basis : Fin d → ℝ → ℝ} (u : EuclideanSpace ℝ (Fin d)) (z : ℝ) (k : ℕ)
    (hf : ContDiffAt ℝ k f z) (hbasis : ∀ i, ContDiffAt ℝ k (basis i) z) :
    iteratedDeriv k (finiteAffineFamily f basis u) z =
      iteratedDeriv k f z + derivativeObservationLinearMap basis z k u := by
  sorry

/-- A real derivative query is represented with its exact order, value and location.
No smoothness is needed to define the affine form; it is needed for its correctness. -/
def derivativeAffineObservation {d : ℕ} (f : ℝ → ℝ) (basis : Fin d → ℝ → ℝ) :
    RealQuery → AffineObservation (EuclideanSpace ℝ (Fin d))
  | .derivative z k =>
      { linear := derivativeObservationLinearMap basis z k
        offset := iteratedDeriv k f z
        location := some z }
  | .idle => { linear := 0, offset := 0, location := none }

theorem derivativeAffineObservation_location {d : ℕ} (f : ℝ → ℝ)
    (basis : Fin d → ℝ → ℝ) (q : RealQuery) :
    (derivativeAffineObservation f basis q).location = q.location := by
  sorry

theorem derivativeAffineObservation_idle_answer {d : ℕ} (f : ℝ → ℝ)
    (basis : Fin d → ℝ → ℝ) (u : EuclideanSpace ℝ (Fin d)) :
    (derivativeAffineObservation f basis .idle).answer u = 0 := by
  sorry

/-- Exact equality with the oracle answer, for all derivative orders and all parameters. -/
theorem derivativeAffineObservation_answer {d : ℕ} {f : ℝ → ℝ}
    {basis : Fin d → ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hbasis : ∀ i, ContDiff ℝ ∞ (basis i)) (q : RealQuery)
    (u : EuclideanSpace ℝ (Fin d)) :
    (derivativeAffineObservation f basis q).answer u = q.answer (finiteAffineFamily f basis u) := by
  sorry

/-- The analytic input class in the manuscript supplies the smoothness hypotheses. -/
theorem derivativeAffineObservation_answer_of_analytic {d : ℕ} {f : ℝ → ℝ}
    {basis : Fin d → ℝ → ℝ} (hf : ∀ t, AnalyticAt ℝ f t)
    (hbasis : ∀ i t, AnalyticAt ℝ (basis i) t) (q : RealQuery)
    (u : EuclideanSpace ℝ (Fin d)) :
    (derivativeAffineObservation f basis q).answer u = q.answer (finiteAffineFamily f basis u) := by
  sorry

/-- A real Gaussian times polynomial is smooth on the whole real line. -/
theorem gaussianPolynomial_contDiff (p : Polynomial ℝ) : ContDiff ℝ ∞ (gaussianPolynomial p) := by
  sorry

/-- Smoothness of the actual Gaussian coefficient functions holds at every order. -/
theorem gaussianCoefficientFunction_contDiff (p : Polynomial ℝ) (n : ℕ)
    (lam ε x : ℝ) (i : Fin (n + 1)) :
    ContDiff ℝ ∞ (gaussianCoefficientFunction p n lam ε x i) := by
  sorry

/-- The abstract affine family agrees exactly with the manuscript's correction family. -/
theorem finiteAffineFamily_gaussian (f : ℝ → ℝ) (p : Polynomial ℝ) (n : ℕ)
    (lam ε x : ℝ) (u : EuclideanSpace ℝ (Fin (n + 1))) :
    finiteAffineFamily f (gaussianCoefficientFunction p n lam ε x) u =
      fun t => f t + gaussianCorrection p n lam ε x u t := by
  sorry

/-- The observation form for the actual Gaussian family, including idle and order zero. -/
theorem gaussian_derivativeAffineObservation_answer {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (p : Polynomial ℝ) (n : ℕ) (lam ε x : ℝ)
    (q : RealQuery) (u : EuclideanSpace ℝ (Fin (n + 1))) :
    (derivativeAffineObservation f (gaussianCoefficientFunction p n lam ε x) q).answer u =
      q.answer (fun t => f t + gaussianCorrection p n lam ε x u t) := by
  sorry

/-- Every finite-stage base function in the manuscript is smooth on the whole real line. -/
theorem gaussian_stage_base_contDiff (p : Polynomial ℝ) :
    ContDiff ℝ ∞ (fun t => t + gaussianPolynomial p t) := by
  sorry

/-- A completely concrete specialization for a finite-stage Gaussian-polynomial base. -/
theorem gaussian_stage_derivativeAffineObservation_answer (p₀ p : Polynomial ℝ)
    (n : ℕ) (lam ε x : ℝ) (q : RealQuery) (u : EuclideanSpace ℝ (Fin (n + 1))) :
    (derivativeAffineObservation (fun t => t + gaussianPolynomial p₀ t)
      (gaussianCoefficientFunction p n lam ε x) q).answer u =
      q.answer (fun t => t + gaussianPolynomial p₀ t + gaussianCorrection p n lam ε x u t) := by
  sorry

end KungTraub
