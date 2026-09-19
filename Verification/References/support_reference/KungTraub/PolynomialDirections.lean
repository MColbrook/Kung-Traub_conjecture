import support_reference.KungTraub.PolynomialSensitivity
import support_reference.KungTraub.ParameterGeometry
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
  sorry

theorem complexify_realCoefficientVector (n : ℕ) (q : Polynomial ℝ) :
    complexifyEuclidean (realCoefficientVector n q) =
      coefficientVector n (q.map (algebraMap ℝ ℂ)) := by
  sorry

theorem coefficientVector_map_real_norm (n : ℕ) (q : Polynomial ℝ) :
    ‖coefficientVector n (q.map (algebraMap ℝ ℂ))‖ = ‖realCoefficientVector n q‖ := by
  sorry

def realInverseConstantScale {n : ℕ} (ε : ℝ) (v : EuclideanSpace ℝ (Fin (n + 1))) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (fun i => if i = 0 then v i / ε else v i)

theorem complexify_realInverseConstantScale {n : ℕ} (ε : ℝ)
    (v : EuclideanSpace ℝ (Fin (n + 1))) :
    complexifyEuclidean (realInverseConstantScale ε v) =
      inverseConstantScale ε (complexifyEuclidean v) := by
  sorry

theorem realInverseConstantScale_norm_pos {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (v : EuclideanSpace ℝ (Fin (n + 1))) (hv : ‖v‖ = 1) :
    0 < ‖realInverseConstantScale ε v‖ := by
  sorry

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
  sorry

def realNormalizedPolynomialDirection {n : ℕ} (q : Polynomial ℝ) (ε : ℝ) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  ‖realInverseConstantScale ε (realCoefficientVector n q)‖⁻¹ •
    realInverseConstantScale ε (realCoefficientVector n q)

theorem realNormalizedPolynomialDirection_norm {n : ℕ} (q : Polynomial ℝ)
    (hnorm : ‖realCoefficientVector n q‖ = 1) {ε : ℝ} (hε : 0 < ε) :
    ‖realNormalizedPolynomialDirection (n := n) q ε‖ = 1 := by
  sorry

theorem realNormalizedPolynomialDirection_polynomial {n : ℕ} (q : Polynomial ℝ)
    (hdegree : q.natDegree ≤ n) {ε : ℝ} (hε : 0 < ε) :
    realParameterPolynomialMap n ε (realNormalizedPolynomialDirection q ε) =
      ‖realInverseConstantScale ε (realCoefficientVector n q)‖⁻¹ • q := by
  sorry

/-- The real normalized direction belongs to the actual common kernel of the
parameter observations induced by all the scalar polynomial functionals. -/
theorem realNormalizedPolynomialDirection_mem_kernel {n j : ℕ}
    (L : ℕ → Polynomial ℝ →ₗ[ℝ] ℝ) (q : Polynomial ℝ) (hdegree : q.natDegree ≤ n)
    (hLq : ∀ i < j, L i q = 0) {ε : ℝ} (hε : 0 < ε) :
    realNormalizedPolynomialDirection q ε ∈
      scalarPrefixKernel (fun i => (L i).comp (realParameterPolynomialMap n ε)) j := by
  sorry

/-- The evaluation vector in the real parameter space, with only the constant
coordinate scaled by `ε`. -/
def realPolynomialEvaluationVector (n : ℕ) (ε w s : ℝ) : EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (fun i => w * (if i = 0 then ε else s ^ i.val))

theorem realPolynomialEvaluationVector_inner {n : ℕ} (ε w s : ℝ)
    (h : EuclideanSpace ℝ (Fin (n + 1))) :
    inner ℝ h (realPolynomialEvaluationVector n ε w s) =
      w * (realParameterPolynomialMap n ε h).eval s := by
  sorry

theorem realNormalizedPolynomialDirection_value {n : ℕ} (q : Polynomial ℝ)
    (hdegree : q.natDegree ≤ n) {ε : ℝ} (hε : 0 < ε) (w s : ℝ) :
    |inner ℝ (realNormalizedPolynomialDirection (n := n) q ε)
      (realPolynomialEvaluationVector n ε w s)| =
      |w * q.eval s| / ‖realInverseConstantScale ε (realCoefficientVector n q)‖ := by
  sorry

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
  sorry

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
  sorry

end KungTraub
