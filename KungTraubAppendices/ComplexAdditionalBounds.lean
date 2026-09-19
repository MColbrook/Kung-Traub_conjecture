import KungTraubAppendices.ComplexCorrectionGeometry
import Mathlib.Analysis.Calculus.FDeriv.WithLp

/-!
# Quantitative complex family bounds and exclusion of boundary zeros

The root-vector estimate specializes the dimension-independent geometric sum
in `ComplexEvaluationBounds`. The derivative estimate applies the polynomial
correction to each complex unit direction on the closed spatial disc. It uses
Mathlib's `differentiable_piLp`, `PiLp.hasFDerivAt_apply`, the chain rule and
the derivative of a finite sum.

Closed-disc uniqueness and the interior root bound imply uniqueness on the
open disc and nonvanishing on its boundary.
-/

noncomputable section

open Polynomial
open scoped BigOperators

namespace KungTraubAppendices

/-- A bounded weight and the actual root-distance bound give an explicit O(ε)
constant, uniformly in all complex coefficients and spatial directions. -/
theorem complexPolynomialEvaluationVector_norm_le_scale (n : ℕ) {ε b R : ℝ}
    (hε : 0 ≤ ε) (w s : ℂ) (hw : ‖w‖ ≤ b)
    (hs : ‖s‖ ≤ R * ε) (hhalf : R * ε ≤ 1 / 2) :
    ‖complexPolynomialEvaluationVector n ε w s‖ ≤ b * (1 + 2 * R) * ε := by
  have hb : 0 ≤ b := (norm_nonneg w).trans hw
  calc
    _ ≤ ‖w‖ * (ε + 2 * ‖s‖) :=
      complexPolynomialEvaluationVector_norm_le n hε w s (hs.trans hhalf)
    _ ≤ b * (ε + 2 * ‖s‖) :=
      mul_le_mul_of_nonneg_right hw (by positivity)
    _ ≤ b * (ε + 2 * (R * ε)) :=
      mul_le_mul_of_nonneg_left (by linarith) hb
    _ = b * (1 + 2 * R) * ε := by ring

/-- The preceding estimate for the actual scaled polynomial family, at every
root or other point in the full unit disc satisfying the stated distance bound. -/
theorem complexCorrectionSmall_vector_norm_le_scale {p : Polynomial ℂ} {n : ℕ}
    {lam b ε R : ℝ} (hsmall : ComplexCorrectionSmall p n lam b)
    (hε : 0 ≤ ε) {α x : ℂ} (hα : ‖α‖ ≤ 1)
    (hdistance : ‖α - x‖ ≤ R * ε) (hhalf : R * ε ≤ 1 / 2) :
    ‖complexPolynomialEvaluationVector n ε ((lam : ℂ) * p.eval α) (α - x)‖ ≤
      b * (1 + 2 * R) * ε :=
  complexPolynomialEvaluationVector_norm_le_scale n hε _ _
    (complexCorrectionSmall_weight_bound hsmall α hα) hdistance hhalf

/-- The complete Euclidean evaluation-vector curve is complex differentiable
everywhere, with no restriction on the scale, centre or polynomial. -/
theorem complexPolynomialEvaluationVector_differentiable (p : Polynomial ℂ)
    (n : ℕ) (lam ε : ℝ) (x : ℂ) :
    Differentiable ℂ (fun z : ℂ =>
      complexPolynomialEvaluationVector n ε ((lam : ℂ) * p.eval z) (z - x)) := by
  apply (differentiable_piLp 2).mpr
  intro i
  change Differentiable ℂ (fun z : ℂ =>
    (lam : ℂ) * p.eval z * (if i = 0 then (ε : ℂ) else (z - x) ^ i.val))
  by_cases hi : i = 0
  · simp only [hi, ↓reduceIte]
    exact (p.differentiable.const_mul (lam : ℂ)).mul_const (ε : ℂ)
  · simp only [hi, ↓reduceIte]
    exact (p.differentiable.const_mul (lam : ℂ)).mul
      ((differentiable_id.sub_const x).pow i.val)

/-- A fixed bilinear parameter evaluation commutes with the complex derivative.
The vector is Euclidean and the pairing is bilinear, without conjugating u. -/
theorem hasDerivAt_complexBilinearDot {d : ℕ}
    {v : ℂ → EuclideanSpace ℂ (Fin d)} {z : ℂ}
    (hv : DifferentiableAt ℂ v z) (u : EuclideanSpace ℂ (Fin d)) :
    HasDerivAt (fun t => complexBilinearDot u (v t))
      (complexBilinearDot u (deriv v z)) z := by
  have hcoord (i : Fin d) :
      HasDerivAt (fun t => v t i) ((deriv v z) i) z := by
    have h := (PiLp.hasFDerivAt_apply (𝕜 := ℂ) 2 (v z) i).comp_hasDerivAt z
      hv.hasDerivAt
    exact h
  unfold complexBilinearDot
  exact HasDerivAt.fun_sum (fun i _ => (hcoord i).const_mul (u i))

/-- The actual vector derivative has norm at most b on the closed unit
disc. This includes the boundary and all admissible complex parameters. -/
theorem complexCorrectionSmall_vector_deriv_norm_le {p : Polynomial ℂ} {n : ℕ}
    {lam b ε : ℝ} (hsmall : ComplexCorrectionSmall p n lam b)
    (hb : 0 ≤ b) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    {x z : ℂ} (hx : ‖x‖ ≤ 1) (hz : ‖z‖ ≤ 1) :
    ‖deriv (fun t : ℂ =>
      complexPolynomialEvaluationVector n ε ((lam : ℂ) * p.eval t) (t - x)) z‖ ≤ b := by
  let v : ℂ → EuclideanSpace ℂ (Fin (n + 1)) := fun t =>
    complexPolynomialEvaluationVector n ε ((lam : ℂ) * p.eval t) (t - x)
  have hv : Differentiable ℂ v :=
    complexPolynomialEvaluationVector_differentiable p n lam ε x
  apply norm_le_of_complexBilinearDot_unit_bound _ hb
  intro u hu
  let q := C (lam : ℂ) * complexCorrectionPolynomial p n ε x u
  have hdot := hasDerivAt_complexBilinearDot (hv z) u
  have heq : (fun t => complexBilinearDot u (v t)) = (fun t => q.eval t) := by
    funext t
    exact (scaled_complexCorrectionPolynomial_eval_bilinear p n lam ε x t u).symm
  change ‖complexBilinearDot u (deriv v z)‖ ≤ b
  rw [← hdot.deriv, heq, q.deriv]
  exact (hsmall ε hε0 hε1 x hx u hu).2 z hz

/-- A root in the fixed compact root region, unique in the closed unit disc,
is also the unique root in the open unit disc. -/
theorem existsUnique_root_open_unit_disc {f : ℂ → ℂ} {α : ℂ}
    (hroot : f α = 0) (hα : ‖α‖ ≤ 1 / 16)
    (hunique : ∀ z : ℂ, ‖z‖ ≤ 1 → f z = 0 → z = α) :
    ∃! z : ℂ, ‖z‖ < 1 ∧ f z = 0 := by
  refine ⟨α, ⟨by linarith, hroot⟩, ?_⟩
  intro z hz
  exact hunique z hz.1.le hz.2

/-- Closed-disc uniqueness and the interior root bound exclude boundary zeros. -/
theorem nonzero_on_unit_circle_of_root_bound {f : ℂ → ℂ} {α : ℂ}
    (hα : ‖α‖ ≤ 1 / 16)
    (hunique : ∀ z : ℂ, ‖z‖ ≤ 1 → f z = 0 → z = α) :
    ∀ z : ℂ, ‖z‖ = 1 → f z ≠ 0 := by
  intro z hz hzero
  have heq := hunique z hz.le hzero
  rw [← heq, hz] at hα
  norm_num at hα

end KungTraubAppendices
