import appendix_b_reference.KungTraubAppendices.ComplexAffineOracle
import Mathlib.Analysis.Calculus.ContDiff.Polynomial

/-!
# Exact complex affine forms of derivative queries

Adapted from `KungTraub.DerivativeObservations`, over the complex field throughout.
Every natural derivative order and every complex query point is retained. The
parameter domain is the entire complex Euclidean coefficient space. Mathlib's
iterated-derivative rules (Chris Birkbeck and Ruben Van de Velde) and polynomial
smoothness (Geoffrey Irving) provide the analytic identities.
-/

noncomputable section
open scoped BigOperators ContDiff
namespace KungTraubAppendices

def complexFiniteAffineFamily {d : ℕ} (f : ℂ → ℂ) (basis : Fin d → ℂ → ℂ)
    (u : EuclideanSpace ℂ (Fin d)) (t : ℂ) : ℂ :=
  f t + ∑ i : Fin d, u i * basis i t

/-- The linear part of evaluation of a fixed derivative, on the entire coefficient space. -/
def complexDerivativeObservationLinearMap {d : ℕ} (basis : Fin d → ℂ → ℂ) (z : ℂ) (k : ℕ) :
    EuclideanSpace ℂ (Fin d) →ₗ[ℂ] ℂ where
  toFun u := ∑ i : Fin d, u i * iteratedDeriv k (basis i) z
  map_add' u v := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c u := by simp [mul_assoc, Finset.mul_sum]

theorem complexDerivativeObservationLinearMap_apply {d : ℕ} (basis : Fin d → ℂ → ℂ)
    (z : ℂ) (k : ℕ) (u : EuclideanSpace ℂ (Fin d)) :
    complexDerivativeObservationLinearMap basis z k u =
      ∑ i : Fin d, u i * iteratedDeriv k (basis i) z := by
  sorry

/-- Only local differentiability through the requested finite order is needed. -/
theorem iteratedDeriv_complexFiniteAffineFamily {d : ℕ} {f : ℂ → ℂ}
    {basis : Fin d → ℂ → ℂ} (u : EuclideanSpace ℂ (Fin d)) (z : ℂ) (k : ℕ)
    (hf : ContDiffAt ℂ k f z) (hbasis : ∀ i, ContDiffAt ℂ k (basis i) z) :
    iteratedDeriv k (complexFiniteAffineFamily f basis u) z =
      iteratedDeriv k f z + complexDerivativeObservationLinearMap basis z k u := by
  sorry

/-- A complex derivative query is represented with its exact order, value and location.
No smoothness is needed to define the affine form; it is needed for its correctness. -/
def complexDerivativeAffineObservation {d : ℕ} (f : ℂ → ℂ) (basis : Fin d → ℂ → ℂ) :
    ComplexQuery → ComplexAffineObservation (EuclideanSpace ℂ (Fin d))
  | .derivative z k =>
      { linear := complexDerivativeObservationLinearMap basis z k
        offset := iteratedDeriv k f z
        location := some z }
  | .idle => { linear := 0, offset := 0, location := none }

theorem complexDerivativeAffineObservation_location {d : ℕ} (f : ℂ → ℂ)
    (basis : Fin d → ℂ → ℂ) (q : ComplexQuery) :
    (complexDerivativeAffineObservation f basis q).location = q.location := by
  sorry

theorem complexDerivativeAffineObservation_idle_answer {d : ℕ} (f : ℂ → ℂ)
    (basis : Fin d → ℂ → ℂ) (u : EuclideanSpace ℂ (Fin d)) :
    (complexDerivativeAffineObservation f basis .idle).answer u = 0 := by
  sorry

/-- Exact equality with the oracle answer, for all derivative orders and all parameters. -/
theorem complexDerivativeAffineObservation_answer {d : ℕ} {f : ℂ → ℂ}
    {basis : Fin d → ℂ → ℂ} (hf : ContDiff ℂ ∞ f)
    (hbasis : ∀ i, ContDiff ℂ ∞ (basis i)) (q : ComplexQuery)
    (u : EuclideanSpace ℂ (Fin d)) :
    (complexDerivativeAffineObservation f basis q).answer u = q.answer (complexFiniteAffineFamily f basis u) := by
  sorry

/-- The analytic input class in the manuscript supplies the smoothness hypotheses. -/
theorem complexDerivativeAffineObservation_answer_of_analytic {d : ℕ} {f : ℂ → ℂ}
    {basis : Fin d → ℂ → ℂ} (hf : ∀ t, AnalyticAt ℂ f t)
    (hbasis : ∀ i t, AnalyticAt ℂ (basis i) t) (q : ComplexQuery)
    (u : EuclideanSpace ℂ (Fin d)) :
    (complexDerivativeAffineObservation f basis q).answer u = q.answer (complexFiniteAffineFamily f basis u) := by
  sorry

/-- Polynomial bases satisfy the analytic hypotheses at every complex point. -/
theorem complexPolynomialAffineObservation_answer {d : ℕ} (p : Polynomial ℂ)
    (basis : Fin d → Polynomial ℂ) (q : ComplexQuery)
    (u : EuclideanSpace ℂ (Fin d)) :
    (complexDerivativeAffineObservation (fun z => p.eval z)
      (fun i z => (basis i).eval z) q).answer u =
      q.answer (complexFiniteAffineFamily (fun z => p.eval z)
        (fun i z => (basis i).eval z) u) := by
  sorry

/-- The affine execution agrees with the actual derivative oracle on the full family. -/
theorem ComplexAlgorithm.complexFiniteAffineFamily_run {d n : ℕ} (A : ComplexAlgorithm n)
    {f : ℂ → ℂ} {basis : Fin d → ℂ → ℂ} (hf : ContDiff ℂ ∞ f)
    (hbasis : ∀ i, ContDiff ℂ ∞ (basis i)) (u : EuclideanSpace ℂ (Fin d)) (x : ℂ) :
    (A.toAffine (complexDerivativeAffineObservation f basis)).run u x =
      A.run (complexFiniteAffineFamily f basis u) x := by
  sorry

/-- For polynomial families the affine execution preserves the output. -/
theorem ComplexAlgorithm.complexPolynomialFamily_run {d n : ℕ} (A : ComplexAlgorithm n)
    (p : Polynomial ℂ) (basis : Fin d → Polynomial ℂ)
    (u : EuclideanSpace ℂ (Fin d)) (x : ℂ) :
    (A.toAffine (complexDerivativeAffineObservation (fun z => p.eval z)
      (fun i z => (basis i).eval z))).run u x =
      A.run (complexFiniteAffineFamily (fun z => p.eval z)
        (fun i z => (basis i).eval z) u) x := by
  sorry

end KungTraubAppendices
