import KungTraub.PolynomialSensitivity
import KungTraub.ParameterGeometry
import Mathlib.Algebra.Polynomial.OfFn

/-!
# Real parameter directions from kernel polynomials

The polynomial estimates use complex roots, whereas the parameter balls in the main
proof are real. This module retains that distinction and constructs the actual real
unit direction associated with a real-coefficient polynomial. Coefficient scaling is
explicit, and membership in the real observation kernel is proved.

Polynomial coefficient reconstruction uses Fabrizio Barroero's `Polynomial.ofFn`
API in Mathlib. Euclidean norm and orthogonal-projection estimates use Mathlib
and the already proved `ParameterGeometry` module.
-/

noncomputable section

open Polynomial
open scoped BigOperators

namespace KungTraub

def realCoefficientVector (n : ℕ) (q : Polynomial ℝ) : EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (fun i => q.coeff i.val)

def complexifyEuclidean {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℂ (Fin d) :=
  WithLp.toLp 2 (fun i => (v i : ℂ))

theorem complexifyEuclidean_norm {d : ℕ} (v : EuclideanSpace ℝ (Fin d)) :
    ‖complexifyEuclidean v‖ = ‖v‖ := by
  have hs : ‖complexifyEuclidean v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i _
    simp [complexifyEuclidean]
  nlinarith [norm_nonneg (complexifyEuclidean v), norm_nonneg v]

theorem complexify_realCoefficientVector (n : ℕ) (q : Polynomial ℝ) :
    complexifyEuclidean (realCoefficientVector n q) =
      coefficientVector n (q.map (algebraMap ℝ ℂ)) := by
  ext i
  simp [complexifyEuclidean, realCoefficientVector, coefficientVector, Polynomial.coeff_map]

theorem coefficientVector_map_real_norm (n : ℕ) (q : Polynomial ℝ) :
    ‖coefficientVector n (q.map (algebraMap ℝ ℂ))‖ = ‖realCoefficientVector n q‖ := by
  rw [← complexify_realCoefficientVector, complexifyEuclidean_norm]

def realInverseConstantScale {n : ℕ} (ε : ℝ) (v : EuclideanSpace ℝ (Fin (n + 1))) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (fun i => if i = 0 then v i / ε else v i)

theorem complexify_realInverseConstantScale {n : ℕ} (ε : ℝ)
    (v : EuclideanSpace ℝ (Fin (n + 1))) :
    complexifyEuclidean (realInverseConstantScale ε v) =
      inverseConstantScale ε (complexifyEuclidean v) := by
  ext i
  by_cases hi : i = 0 <;> simp [complexifyEuclidean, realInverseConstantScale, inverseConstantScale, hi]

theorem realInverseConstantScale_norm_pos {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (v : EuclideanSpace ℝ (Fin (n + 1))) (hv : ‖v‖ = 1) :
    0 < ‖realInverseConstantScale ε v‖ := by
  have h := inverseConstantScale_norm_pos hε (complexifyEuclidean v)
    (by rw [complexifyEuclidean_norm, hv])
  rwa [← complexify_realInverseConstantScale, complexifyEuclidean_norm] at h

/-- The exact coefficient scaling of the real parameter family. -/
def realConstantScaleMap (n : ℕ) (ε : ℝ) :
    EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] (Fin (n + 1) → ℝ) where
  toFun u i := if i = 0 then ε * u i else u i
  map_add' u v := by ext i; by_cases hi : i = 0 <;> simp [hi, mul_add]
  map_smul' c u := by ext i; by_cases hi : i = 0 <;> simp [hi, mul_left_comm]

/-- The polynomial giving the parameter direction in the centered variable. -/
def realParameterPolynomialMap (n : ℕ) (ε : ℝ) :
    EuclideanSpace ℝ (Fin (n + 1)) →ₗ[ℝ] Polynomial ℝ :=
  (Polynomial.ofFn (n + 1)).comp (realConstantScaleMap n ε)

theorem realParameterPolynomialMap_inverse_coefficients {n : ℕ} (q : Polynomial ℝ)
    (hdegree : q.natDegree ≤ n) {ε : ℝ} (hε : ε ≠ 0) :
    realParameterPolynomialMap n ε (realInverseConstantScale ε (realCoefficientVector n q)) = q := by
  have heq : realConstantScaleMap n ε
      (realInverseConstantScale ε (realCoefficientVector n q)) = Polynomial.toFn (n + 1) q := by
    funext i
    by_cases hi : i = 0
    · simp [realConstantScaleMap, realInverseConstantScale, realCoefficientVector,
        Polynomial.toFn, hi]
      field_simp
    · simp [realConstantScaleMap, realInverseConstantScale, realCoefficientVector,
        Polynomial.toFn, hi]
  change Polynomial.ofFn (n + 1) _ = q
  rw [heq]
  exact Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega)

def realNormalizedPolynomialDirection {n : ℕ} (q : Polynomial ℝ) (ε : ℝ) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  ‖realInverseConstantScale ε (realCoefficientVector n q)‖⁻¹ •
    realInverseConstantScale ε (realCoefficientVector n q)

theorem realNormalizedPolynomialDirection_norm {n : ℕ} (q : Polynomial ℝ)
    (hnorm : ‖realCoefficientVector n q‖ = 1) {ε : ℝ} (hε : 0 < ε) :
    ‖realNormalizedPolynomialDirection (n := n) q ε‖ = 1 := by
  have hp := realInverseConstantScale_norm_pos hε (realCoefficientVector n q) hnorm
  simp only [realNormalizedPolynomialDirection, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hp)]
  exact inv_mul_cancel₀ hp.ne'

theorem realNormalizedPolynomialDirection_polynomial {n : ℕ} (q : Polynomial ℝ)
    (hdegree : q.natDegree ≤ n) {ε : ℝ} (hε : 0 < ε) :
    realParameterPolynomialMap n ε (realNormalizedPolynomialDirection q ε) =
      ‖realInverseConstantScale ε (realCoefficientVector n q)‖⁻¹ • q := by
  rw [realNormalizedPolynomialDirection, map_smul,
    realParameterPolynomialMap_inverse_coefficients q hdegree hε.ne']

/-- The real normalized direction belongs to the actual common kernel of the
parameter observations induced by all the scalar polynomial functionals. -/
theorem realNormalizedPolynomialDirection_mem_kernel {n j : ℕ}
    (L : ℕ → Polynomial ℝ →ₗ[ℝ] ℝ) (q : Polynomial ℝ) (hdegree : q.natDegree ≤ n)
    (hLq : ∀ i < j, L i q = 0) {ε : ℝ} (hε : 0 < ε) :
    realNormalizedPolynomialDirection q ε ∈
      scalarPrefixKernel (fun i => (L i).comp (realParameterPolynomialMap n ε)) j := by
  rw [mem_scalarPrefixKernel]
  intro i hi
  change L i (realParameterPolynomialMap n ε (realNormalizedPolynomialDirection q ε)) = 0
  rw [realNormalizedPolynomialDirection_polynomial q hdegree hε, map_smul, hLq i hi, smul_zero]

/-- The evaluation vector in the real parameter space, with only the constant
coordinate scaled by `ε`. -/
def realPolynomialEvaluationVector (n : ℕ) (ε w s : ℝ) : EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (fun i => w * (if i = 0 then ε else s ^ i.val))

theorem realPolynomialEvaluationVector_inner {n : ℕ} (ε w s : ℝ)
    (h : EuclideanSpace ℝ (Fin (n + 1))) :
    inner ℝ h (realPolynomialEvaluationVector n ε w s) =
      w * (realParameterPolynomialMap n ε h).eval s := by
  simp only [realPolynomialEvaluationVector, PiLp.inner_apply,
    realParameterPolynomialMap, LinearMap.comp_apply, Polynomial.ofFn_eq_sum_monomial,
    Polynomial.eval_finsetSum, Polynomial.eval_monomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i = 0
  · subst i
    simp [realConstantScaleMap]
    ring
  · simp [realConstantScaleMap, hi]
    ring

theorem realNormalizedPolynomialDirection_value {n : ℕ} (q : Polynomial ℝ)
    (hdegree : q.natDegree ≤ n) {ε : ℝ} (hε : 0 < ε) (w s : ℝ) :
    |inner ℝ (realNormalizedPolynomialDirection (n := n) q ε)
      (realPolynomialEvaluationVector n ε w s)| =
      |w * q.eval s| / ‖realInverseConstantScale ε (realCoefficientVector n q)‖ := by
  rw [realPolynomialEvaluationVector_inner,
    realNormalizedPolynomialDirection_polynomial q hdegree hε, Polynomial.eval_smul]
  simp only [smul_eq_mul, abs_mul, abs_inv, abs_norm]
  ring

/-- The complex coefficient estimate yields the value of an actual real unit direction. -/
theorem realNormalizedPolynomialDirection_lower_bound {n j : ℕ}
    (q : Polynomial ℝ) (hdegree : q.natDegree ≤ n) (hnorm : ‖realCoefficientVector n q‖ = 1)
    (γ : ℕ → ℝ) (hγ : ∀ i < j, 0 < γ i)
    {ε R wmin w s : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 < R)
    (hwmin : 0 < wmin) (hw : wmin ≤ |w|)
    (hs : |s| ≤ R * ε) (hhalf : R * ε ≤ 1 / 2)
    (hvalue : sensitivityPolynomialConstant n γ j * ε ^ orderBound j ≤ |q.eval s|) :
    (wmin * sensitivityPolynomialConstant n γ j / (2 * R + 2)) * ε ^ orderBound j ≤
      |inner ℝ (realNormalizedPolynomialDirection (n := n) q ε)
        (realPolynomialEvaluationVector n ε w s)| := by
  have hden : ‖inverseConstantScale ε (coefficientVector n (q.map (algebraMap ℝ ℂ)))‖ =
      ‖realInverseConstantScale ε (realCoefficientVector n q)‖ := by
    rw [← complexify_realCoefficientVector, ← complexify_realInverseConstantScale,
      complexifyEuclidean_norm]
  have heval : (q.map (algebraMap ℝ ℂ)).eval (s : ℂ) = ((q.eval s : ℝ) : ℂ) := by
    exact Polynomial.eval_map_apply (p := q) (algebraMap ℝ ℂ) s
  have hbound := weighted_polynomial_inverse_scale_lower_bound (q.map (algebraMap ℝ ℂ))
    (Polynomial.natDegree_map_le.trans hdegree)
    (by rw [coefficientVector_map_real_norm, hnorm]) γ hγ (a := (s : ℂ)) (w := (w : ℂ))
    hε hε1 hR hwmin (by simpa using hw) (by simpa using hs) hhalf
    (by simpa only [heval, Complex.norm_real, Real.norm_eq_abs] using hvalue)
  rw [realNormalizedPolynomialDirection_value q hdegree hε]
  simpa only [heval, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs, hden] using hbound

/-- The actual real common-kernel projection has the sensitivity lower bound once
the minimum-degree polynomial value estimate is supplied. -/
theorem real_polynomial_kernel_projected_sensitivity_lower_bound {n j : ℕ}
    (L : ℕ → Polynomial ℝ →ₗ[ℝ] ℝ) (q : Polynomial ℝ) (hdegree : q.natDegree ≤ n)
    (hnorm : ‖realCoefficientVector n q‖ = 1) (hLq : ∀ i < j, L i q = 0)
    (γ : ℕ → ℝ) (hγ : ∀ i < j, 0 < γ i)
    {ε R wmin w s : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 < R)
    (hwmin : 0 < wmin) (hw : wmin ≤ |w|)
    (hs : |s| ≤ R * ε) (hhalf : R * ε ≤ 1 / 2)
    (hvalue : sensitivityPolynomialConstant n γ j * ε ^ orderBound j ≤ |q.eval s|) :
    (wmin * sensitivityPolynomialConstant n γ j / (2 * R + 2)) * ε ^ orderBound j ≤
      ‖(scalarPrefixKernel (fun i => (L i).comp (realParameterPolynomialMap n ε)) j).starProjection
        (realPolynomialEvaluationVector n ε w s)‖ := by
  have hbound := realNormalizedPolynomialDirection_lower_bound q hdegree hnorm γ hγ
    hε hε1 hR hwmin hw hs hhalf hvalue
  have hproj := abs_inner_le_projected_norm_mul _
    (realNormalizedPolynomialDirection_mem_kernel L q hdegree hLq hε)
    (realPolynomialEvaluationVector n ε w s)
  rw [realNormalizedPolynomialDirection_norm q hnorm hε, mul_one] at hproj
  exact hbound.trans hproj

end KungTraub
