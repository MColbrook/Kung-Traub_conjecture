import KungTraubAppendices.ComplexPolynomialCorrections
import KungTraubAppendices.ComplexEvaluationBounds
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
  obtain ⟨lam, hlam, hsmall⟩ := complexCorrectionPolynomial_exists_small_scaling p n 1 hb
  refine ⟨lam, hlam, fun ε hε0 hε1 x hx u hu => ?_⟩
  have h := hsmall ε hε0 hε1 x hx u hu
  exact ⟨fun z hz => (h.1 z hz).trans (by linarith),
    fun z hz => (h.2 z hz).trans (by linarith)⟩

/-- Scale one and the first unit coordinate recover the exact fixed weight. -/
theorem complexCorrectionSmall_weight_bound {p : Polynomial ℂ} {n : ℕ} {lam b : ℝ}
    (hsmall : ComplexCorrectionSmall p n lam b) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖(lam : ℂ) * p.eval z‖ ≤ b := by
  let u : EuclideanSpace ℂ (Fin (n + 1)) := PiLp.single 2 0 1
  have hu : ‖u‖ ≤ 1 := by simp [u]
  have h := (hsmall 1 (by norm_num) le_rfl 0 (by simp) u hu).1 z hz
  rw [Polynomial.eval_mul, Polynomial.eval_C, complexCorrectionPolynomial_eval] at h
  simpa [u, mul_assoc] using h

/-- The weighted vector is the bilinear evaluation of the exact scaled correction. -/
theorem scaled_complexCorrectionPolynomial_eval_bilinear (p : Polynomial ℂ) (n : ℕ)
    (lam ε : ℝ) (x z : ℂ) (u : EuclideanSpace ℂ (Fin (n + 1))) :
    (C (lam : ℂ) * complexCorrectionPolynomial p n ε x u).eval z =
      complexBilinearDot u (complexPolynomialEvaluationVector n ε ((lam : ℂ) * p.eval z) (z - x)) := by
  rw [complexPolynomialEvaluationVector_bilinear]
  simp [complexCorrectionPolynomial, mul_assoc]

/-- Uniform directional scalar derivatives bound the actual vector with exactly K=b. -/
theorem complexCorrectionSmall_vector_lipschitz {p : Polynomial ℂ} {n : ℕ} {lam b ε : ℝ}
    (hsmall : ComplexCorrectionSmall p n lam b) (hb : 0 ≤ b)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) {x z t : ℂ}
    (hx : ‖x‖ ≤ 1) (hz : ‖z‖ ≤ 1) (ht : ‖t‖ ≤ 1) :
    ‖complexPolynomialEvaluationVector n ε ((lam : ℂ) * p.eval z) (z - x) -
      complexPolynomialEvaluationVector n ε ((lam : ℂ) * p.eval t) (t - x)‖ ≤ b * ‖z - t‖ := by
  apply norm_le_of_complexBilinearDot_unit_bound _ (mul_nonneg hb (norm_nonneg _))
  intro u hu
  let q := C (lam : ℂ) * complexCorrectionPolynomial p n ε x u
  have hq := hsmall ε hε0 hε1 x hx u hu
  have hmean : ‖q.eval z - q.eval t‖ ≤ b * ‖z - t‖ :=
    (convex_closedBall (0 : ℂ) (1 : ℝ)).norm_image_sub_le_of_norm_deriv_le
      (fun v _ => q.differentiableAt)
      (fun v hv => by rw [q.deriv]; exact hq.2 v (by simpa using hv))
      (by simpa using ht) (by simpa using hz)
  dsimp only [q] at hmean
  rw [scaled_complexCorrectionPolynomial_eval_bilinear,
    scaled_complexCorrectionPolynomial_eval_bilinear] at hmean
  simpa only [complexBilinearDot, PiLp.sub_apply, mul_sub, Finset.sum_sub_distrib] using hmean

/-- The full complex unit parameter ball has the old-root perturbation bound. -/
theorem complexCorrectionSmall_at_old_root {p : Polynomial ℂ} {n : ℕ} {lam b ε : ℝ}
    (hsmall : ComplexCorrectionSmall p n lam b) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 4)
    (a : ℂ) (ha : ‖a‖ ≤ 1) (u : EuclideanSpace ℂ (Fin (n + 1))) (hu : ‖u‖ ≤ 1) :
    ‖(C (lam : ℂ) * complexCorrectionPolynomial p n ε (a + (ε : ℂ)) u).eval a‖ ≤
      2 * b * ε := by
  have hw := complexCorrectionSmall_weight_bound hsmall a ha
  have hb : 0 ≤ b := (norm_nonneg _).trans hw
  rw [scaled_complexCorrectionPolynomial_eval_bilinear,
    show a - (a + (ε : ℂ)) = -(ε : ℂ) by ring]
  have h := norm_complexBilinearDot_le u
    (complexPolynomialEvaluationVector n ε ((lam : ℂ) * p.eval a) (-(ε : ℂ)))
  calc
    _ ≤ ‖complexPolynomialEvaluationVector n ε ((lam : ℂ) * p.eval a) (-(ε : ℂ))‖ :=
      h.trans (by simpa using mul_le_mul_of_nonneg_left hu (norm_nonneg _))
    _ ≤ 2 * ‖(lam : ℂ) * p.eval a‖ * ε :=
      complexPolynomialEvaluationVector_old_root_norm_le n hε0 hε _
    _ ≤ 2 * b * ε := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw (by norm_num)) hε0

end KungTraubAppendices
