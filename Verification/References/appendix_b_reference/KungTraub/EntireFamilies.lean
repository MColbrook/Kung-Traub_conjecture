import appendix_b_reference.KungTraub.GaussianBounds
import appendix_b_reference.KungTraub.FiniteRootMotion
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Real roots of the entire correction families

The family estimates in Section 4 of Matthew J. Colbrook's manuscript. The multiplier is fixed before the
scale and coefficient vector. Root existence is proved from a global derivative
lower bound and bounded difference from the identity. The mean-value and
intermediate-value arguments are provided by `RealRoots`; Cauchy–Schwarz and
finite-dimensional Euclidean norm identities are reused from mathlib.
-/

noncomputable section

open Set Filter Topology
open scoped BigOperators

namespace KungTraub

def gaussianCorrection (p : Polynomial ℝ) (n : ℕ) (lam ε x : ℝ)
    (u : EuclideanSpace ℝ (Fin (n + 1))) (t : ℝ) : ℝ :=
  lam * gaussianPolynomial (gaussianCorrectionPolynomial p n ε x u) t

/-- The real part of the uniform correction estimate; the multiplier is outside
all scale, centre and coefficient quantifiers. -/
def GaussianCorrectionSmall (p : Polynomial ℝ) (n : ℕ) (lam b : ℝ) : Prop :=
  ∀ ε x : ℝ, 0 ≤ ε → ε ≤ 1 → |x| ≤ 1 →
    ∀ u : EuclideanSpace ℝ (Fin (n + 1)), ‖u‖ ≤ 1 → ∀ t : ℝ,
      |gaussianCorrection p n lam ε x u t| ≤ b ∧
      |deriv (gaussianCorrection p n lam ε x u) t| ≤ b

theorem gaussianCorrection_hasDerivAt (p : Polynomial ℝ) (n : ℕ) (lam ε x : ℝ)
    (u : EuclideanSpace ℝ (Fin (n + 1))) (t : ℝ) :
    HasDerivAt (gaussianCorrection p n lam ε x u)
      (lam * gaussianPolynomial
        ((gaussianCorrectionPolynomial p n ε x u).derivative -
          Polynomial.C 2 * Polynomial.X * gaussianCorrectionPolynomial p n ε x u) t) t := by
  sorry

/-- Joint three-point bounds imply the separate real bounds when the disc is nonempty. -/
theorem gaussianCorrectionSmall_of_three_bounds {p : Polynomial ℝ} {n : ℕ}
    {lam b R : ℝ} (hR : 0 ≤ R)
    (h : ∀ ε x : ℝ, 0 ≤ ε → ε ≤ 1 → |x| ≤ 1 →
      ∀ u : EuclideanSpace ℝ (Fin (n + 1)), ‖u‖ ≤ 1 →
        ∀ t v : ℝ, ∀ z : ℂ, ‖z‖ ≤ R →
          |lam * gaussianPolynomial (gaussianCorrectionPolynomial p n ε x u) t| +
          |deriv (fun y => lam * gaussianPolynomial
            (gaussianCorrectionPolynomial p n ε x u) y) v| +
          ‖(lam : ℂ) * complexGaussianPolynomial
            (gaussianCorrectionPolynomial p n ε x u) z‖ ≤ b) :
    GaussianCorrectionSmall p n lam b := by
  sorry

/-- The required uniform real estimates have an actual positive multiplier. -/
theorem exists_gaussianCorrectionSmall (p : Polynomial ℝ) (n : ℕ)
    {b : ℝ} (hb : 0 < b) : ∃ lam > 0, GaussianCorrectionSmall p n lam b := by
  sorry

theorem gaussianCorrection_family_derivative_bounds {f : ℝ → ℝ}
    {p : Polynomial ℝ} {n : ℕ} {lam b ε x : ℝ}
    (hf : Differentiable ℝ f)
    (hf' : ∀ t, (15 : ℝ) / 16 ≤ deriv f t ∧ deriv f t ≤ 17 / 16)
    (hsmall : GaussianCorrectionSmall p n lam b) (hb : b ≤ 1 / 16)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hx : |x| ≤ 1)
    (u : EuclideanSpace ℝ (Fin (n + 1))) (hu : ‖u‖ ≤ 1) (t : ℝ) :
    (1 : ℝ) / 2 ≤ deriv (fun y => f y + gaussianCorrection p n lam ε x u y) t ∧
      deriv (fun y => f y + gaussianCorrection p n lam ε x u y) t ≤ 3 / 2 := by
  sorry

/-- Each member of the full Euclidean unit-parameter family has one real root.
Bounded difference from the identity supplies existence as well as uniqueness. -/
theorem gaussianCorrection_family_existsUnique_root {f : ℝ → ℝ}
    {p : Polynomial ℝ} {n : ℕ} {lam b B ε x : ℝ}
    (hf : Differentiable ℝ f)
    (hf' : ∀ t, (15 : ℝ) / 16 ≤ deriv f t ∧ deriv f t ≤ 17 / 16)
    (hidentity : ∀ t, |f t - t| ≤ B)
    (hsmall : GaussianCorrectionSmall p n lam b) (hb : b ≤ 1 / 16)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hx : |x| ≤ 1)
    (u : EuclideanSpace ℝ (Fin (n + 1))) (hu : ‖u‖ ≤ 1) :
    ∃! α : ℝ, f α + gaussianCorrection p n lam ε x u α = 0 := by
  sorry

theorem family_geometric_sum_le_two {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (n : ℕ) :
    (∑ i : Fin n, r ^ i.val) ≤ 2 := by
  sorry

/-- The Cauchy–Schwarz estimate at the old root, with the paper's constant `2`. -/
theorem gaussian_family_bracket_at_old_root_le {n : ℕ} {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 4)
    (u : EuclideanSpace ℝ (Fin (n + 1))) (hu : ‖u‖ ≤ 1) :
    |ε * u 0 + ∑ i : Fin n, u i.succ * (-ε) ^ (i.val + 1)| ≤ 2 * ε := by
  sorry

/-- Testing the constant coefficient at scale one bounds the fixed multiplier itself. -/
theorem gaussianCorrectionSmall_weight_bound {p : Polynomial ℝ} {n : ℕ} {lam b : ℝ}
    (hsmall : GaussianCorrectionSmall p n lam b) (t : ℝ) :
    |lam * gaussianPolynomial p t| ≤ b := by
  sorry

theorem gaussianCorrection_at_old_root_bound {p : Polynomial ℝ} {n : ℕ}
    {lam b ε : ℝ} (hsmall : GaussianCorrectionSmall p n lam b)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 4) (a : ℝ)
    (u : EuclideanSpace ℝ (Fin (n + 1))) (hu : ‖u‖ ≤ 1) :
    |gaussianCorrection p n lam ε (a + ε) u a| ≤ 2 * b * ε := by
  sorry

theorem family_start_in_unit_interval {a ε : ℝ} (ha : |a| ≤ 1 / 4)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 4) : |a + ε| ≤ 1 := by
  sorry

/-- The displacement is derived from the proved derivative and old-root value bounds. -/
theorem gaussianCorrection_root_displacement {f : ℝ → ℝ}
    {p : Polynomial ℝ} {n : ℕ} {lam b ε a α : ℝ}
    (hf : Differentiable ℝ f)
    (hf' : ∀ t, (15 : ℝ) / 16 ≤ deriv f t ∧ deriv f t ≤ 17 / 16)
    (hsmall : GaussianCorrectionSmall p n lam b) (hb : b ≤ 1 / 16)
    (ha : |a| ≤ 1 / 4) (hfa : f a = 0) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 4)
    (u : EuclideanSpace ℝ (Fin (n + 1))) (hu : ‖u‖ ≤ 1)
    (hroot : f α + gaussianCorrection p n lam ε (a + ε) u α = 0) :
    |α - a| ≤ 4 * b * ε := by
  sorry

/-- Exact left and right distances from the starting point, for every family root. -/
theorem gaussianCorrection_root_distance_bounds {f : ℝ → ℝ}
    {p : Polynomial ℝ} {n : ℕ} {lam b ε a α : ℝ}
    (hf : Differentiable ℝ f)
    (hf' : ∀ t, (15 : ℝ) / 16 ≤ deriv f t ∧ deriv f t ≤ 17 / 16)
    (hsmall : GaussianCorrectionSmall p n lam b) (hb : b ≤ 1 / 16)
    (ha : |a| ≤ 1 / 4) (hfa : f a = 0) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 4)
    (u : EuclideanSpace ℝ (Fin (n + 1))) (hu : ‖u‖ ≤ 1)
    (hroot : f α + gaussianCorrection p n lam ε (a + ε) u α = 0) :
    3 * ε / 4 ≤ a + ε - α ∧ a + ε - α ≤ 5 * ε / 4 := by
  sorry

/-- One coherent root function on the full closed Euclidean unit ball, with exact
uniqueness and distance estimates for every parameter. -/
theorem gaussianCorrection_exists_root_family {f : ℝ → ℝ}
    {p : Polynomial ℝ} {n : ℕ} {lam b B ε a : ℝ}
    (hf : Differentiable ℝ f)
    (hf' : ∀ t, (15 : ℝ) / 16 ≤ deriv f t ∧ deriv f t ≤ 17 / 16)
    (hidentity : ∀ t, |f t - t| ≤ B)
    (hsmall : GaussianCorrectionSmall p n lam b) (hb : b ≤ 1 / 16)
    (ha : |a| ≤ 1 / 4) (hfa : f a = 0) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 4) :
    ∃ α : {u : EuclideanSpace ℝ (Fin (n + 1)) // ‖u‖ ≤ 1} → ℝ,
      ∀ u, (f (α u) + gaussianCorrection p n lam ε (a + ε) u.val (α u) = 0) ∧
        (∀ β, f β + gaussianCorrection p n lam ε (a + ε) u.val β = 0 → β = α u) ∧
        |α u - a| ≤ 4 * b * ε ∧
        3 * ε / 4 ≤ a + ε - α u ∧ a + ε - α u ≤ 5 * ε / 4 := by
  sorry

/-- A continuous function nonzero at one point has a uniform positive lower bound
on a fixed neighbourhood of that point. -/
theorem exists_abs_lower_bound_near_nonzero {w : ℝ → ℝ} {a : ℝ}
    (hw : ContinuousAt w a) (hwa : w a ≠ 0) :
    ∃ δ > 0, ∀ t : ℝ, |t - a| < δ → |w a| / 2 ≤ |w t| := by
  sorry

/-- Once the multiplier is fixed and nonzero at the old root, one positive scale
threshold works for every coefficient vector and every corresponding real root. -/
theorem gaussianCorrection_weight_uniformly_away_from_zero {f : ℝ → ℝ}
    {p : Polynomial ℝ} {n : ℕ} {lam b a : ℝ}
    (hf : Differentiable ℝ f)
    (hf' : ∀ t, (15 : ℝ) / 16 ≤ deriv f t ∧ deriv f t ≤ 17 / 16)
    (hsmall : GaussianCorrectionSmall p n lam b) (hb : b ≤ 1 / 16)
    (ha : |a| ≤ 1 / 4) (hfa : f a = 0) (hwa : lam * gaussianPolynomial p a ≠ 0) :
    ∃ η > 0, ∀ ε : ℝ, 0 < ε → ε < η → ε ≤ 1 / 4 →
      ∀ u : EuclideanSpace ℝ (Fin (n + 1)), ‖u‖ ≤ 1 → ∀ α : ℝ,
        f α + gaussianCorrection p n lam ε (a + ε) u α = 0 →
          |lam * gaussianPolynomial p a| / 2 ≤ |lam * gaussianPolynomial p α| := by
  sorry

/-- The family is continuous in its Euclidean coefficient parameter at each real point. -/
theorem gaussianCorrection_continuous_parameter (p : Polynomial ℝ) (n : ℕ)
    (lam ε x t : ℝ) :
    Continuous (fun u : EuclideanSpace ℝ (Fin (n + 1)) => gaussianCorrection p n lam ε x u t) := by
  sorry

/-- The roots selected by uniqueness vary continuously on the full closed unit ball. -/
theorem gaussianCorrection_continuous_roots {f : ℝ → ℝ}
    {p : Polynomial ℝ} {n : ℕ} {lam b ε x : ℝ}
    (hf : Differentiable ℝ f)
    (hf' : ∀ t, (15 : ℝ) / 16 ≤ deriv f t ∧ deriv f t ≤ 17 / 16)
    (hsmall : GaussianCorrectionSmall p n lam b) (hb : b ≤ 1 / 16)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hx : |x| ≤ 1)
    (α : {u : EuclideanSpace ℝ (Fin (n + 1)) // ‖u‖ ≤ 1} → ℝ)
    (hroot : ∀ u, f (α u) + gaussianCorrection p n lam ε x u.val (α u) = 0) :
    Continuous α := by
  sorry

/-- The coefficient functions whose Euclidean vector is used in the finite-scale family. -/
def gaussianCoefficientFunction (p : Polynomial ℝ) (n : ℕ) (lam ε x : ℝ)
    (i : Fin (n + 1)) (t : ℝ) : ℝ :=
  lam * gaussianPolynomial p t * (if i = 0 then ε else (t - x) ^ i.val)

theorem gaussianCoefficientFunction_differentiable (p : Polynomial ℝ) (n : ℕ)
    (lam ε x : ℝ) (i : Fin (n + 1)) :
    Differentiable ℝ (gaussianCoefficientFunction p n lam ε x i) := by
  sorry

theorem gaussianCorrection_eq_sum_coefficients (p : Polynomial ℝ) (n : ℕ)
    (lam ε x : ℝ) (u : EuclideanSpace ℝ (Fin (n + 1))) (t : ℝ) :
    gaussianCorrection p n lam ε x u t =
      ∑ i : Fin (n + 1), u i * gaussianCoefficientFunction p n lam ε x i t := by
  sorry

/-- The derivative of each directional correction is the same directional sum of
the coefficient derivatives. -/
theorem gaussianCorrection_deriv_eq_sum_coefficients (p : Polynomial ℝ) (n : ℕ)
    (lam ε x : ℝ) (u : EuclideanSpace ℝ (Fin (n + 1))) (t : ℝ) :
    deriv (gaussianCorrection p n lam ε x u) t =
      ∑ i : Fin (n + 1), u i * deriv (gaussianCoefficientFunction p n lam ε x i) t := by
  sorry

/-- Euclidean duality: estimates in every unit direction bound the vector norm. -/
theorem norm_le_of_unit_inner_bounds {d : ℕ} {v : EuclideanSpace ℝ (Fin d)} {b : ℝ}
    (h : ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ ≤ 1 → |inner ℝ u v| ≤ b) : ‖v‖ ≤ b := by
  sorry

/-- The exact Euclidean bound on the tuple of first derivatives of the coefficient
functions follows from the uniform directional correction bound. -/
theorem gaussianCorrection_coefficient_derivative_norm_bound {p : Polynomial ℝ} {n : ℕ}
    {lam b ε x : ℝ} (hsmall : GaussianCorrectionSmall p n lam b)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hx : |x| ≤ 1) (t : ℝ) :
    ‖WithLp.toLp 2 (fun i : Fin (n + 1) =>
      deriv (gaussianCoefficientFunction p n lam ε x i) t)‖ ≤ b := by
  sorry

/-- The coordinate derivatives are the actual derivative of the Euclidean-valued
coefficient function, via the continuous linear equivalence with a finite product. -/
theorem gaussianCoefficientVector_hasDerivAt (p : Polynomial ℝ) (n : ℕ)
    (lam ε x t : ℝ) :
    HasDerivAt (fun y => WithLp.toLp 2 (fun i : Fin (n + 1) =>
      gaussianCoefficientFunction p n lam ε x i y))
      (WithLp.toLp 2 (fun i : Fin (n + 1) =>
        deriv (gaussianCoefficientFunction p n lam ε x i) t)) t := by
  sorry

/-- The vector derivative bound required by the finite-scale family, with the
Euclidean norm and the same constant as the scalar directional bounds. -/
theorem gaussianCorrection_vector_derivative_norm_bound {p : Polynomial ℝ} {n : ℕ}
    {lam b ε x : ℝ} (hsmall : GaussianCorrectionSmall p n lam b)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hx : |x| ≤ 1) (t : ℝ) :
    ‖deriv (fun y => WithLp.toLp 2 (fun i : Fin (n + 1) =>
      gaussianCoefficientFunction p n lam ε x i y)) t‖ ≤ b := by
  sorry

end KungTraub
