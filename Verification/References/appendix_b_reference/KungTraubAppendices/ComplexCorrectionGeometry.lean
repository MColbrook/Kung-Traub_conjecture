import appendix_b_reference.KungTraubAppendices.ComplexPolynomialCorrections
import appendix_b_reference.KungTraubAppendices.ComplexEvaluationBounds
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Uniform geometry of the actual polynomial correction

Testing the constant coordinate at scale one bounds the fixed weight. The
scalar derivative bound, tested on all unit complex directions, gives the full
vector Lipschitz bound with exactly K=b and no degree factor. Cauchy--Schwarz
then bounds the correction at the old root by 2*b*epsilon.
-/
noncomputable section
open Polynomial Set
namespace KungTraubAppendices

/-- Uniform value and derivative bounds on the closed unit spatial disc. -/
def ComplexCorrectionSmall (p : Polynomial ℂ) (n : ℕ) (lam b : ℝ) : Prop :=
  ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ x : ℂ, ‖x‖ ≤ 1 →
    ∀ u : EuclideanSpace ℂ (Fin (n + 1)), ‖u‖ ≤ 1 →
      ComplexPolynomialDiscBound (C (lam : ℂ) * complexCorrectionPolynomial p n ε x u) 1 b

/-- The uniform compactness construction supplies this complete parameter-domain bound. -/
theorem exists_complexCorrectionSmall (p : Polynomial ℂ) (n : ℕ) {b : ℝ} (hb : 0 < b) :
    ∃ lam : ℝ, 0 < lam ∧ ComplexCorrectionSmall p n lam b := by
  sorry

/-- Scale one and the first unit coordinate recover the exact fixed weight. -/
theorem complexCorrectionSmall_weight_bound {p : Polynomial ℂ} {n : ℕ} {lam b : ℝ}
    (hsmall : ComplexCorrectionSmall p n lam b) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖(lam : ℂ) * p.eval z‖ ≤ b := by
  sorry

/-- The weighted vector is the bilinear evaluation of the exact scaled correction. -/
theorem scaled_complexCorrectionPolynomial_eval_bilinear (p : Polynomial ℂ) (n : ℕ)
    (lam ε : ℝ) (x z : ℂ) (u : EuclideanSpace ℂ (Fin (n + 1))) :
    (C (lam : ℂ) * complexCorrectionPolynomial p n ε x u).eval z =
      complexBilinearDot u (complexPolynomialEvaluationVector n ε ((lam : ℂ) * p.eval z) (z - x)) := by
  sorry

/-- Uniform directional scalar derivatives bound the actual vector with exactly K=b. -/
theorem complexCorrectionSmall_vector_lipschitz {p : Polynomial ℂ} {n : ℕ} {lam b ε : ℝ}
    (hsmall : ComplexCorrectionSmall p n lam b) (hb : 0 ≤ b)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) {x z t : ℂ}
    (hx : ‖x‖ ≤ 1) (hz : ‖z‖ ≤ 1) (ht : ‖t‖ ≤ 1) :
    ‖complexPolynomialEvaluationVector n ε ((lam : ℂ) * p.eval z) (z - x) -
      complexPolynomialEvaluationVector n ε ((lam : ℂ) * p.eval t) (t - x)‖ ≤ b * ‖z - t‖ := by
  sorry

/-- The full complex unit parameter ball has the old-root perturbation bound. -/
theorem complexCorrectionSmall_at_old_root {p : Polynomial ℂ} {n : ℕ} {lam b ε : ℝ}
    (hsmall : ComplexCorrectionSmall p n lam b) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 4)
    (a : ℂ) (ha : ‖a‖ ≤ 1) (u : EuclideanSpace ℂ (Fin (n + 1))) (hu : ‖u‖ ≤ 1) :
    ‖(C (lam : ℂ) * complexCorrectionPolynomial p n ε (a + (ε : ℂ)) u).eval a‖ ≤
      2 * b * ε := by
  sorry

end KungTraubAppendices
