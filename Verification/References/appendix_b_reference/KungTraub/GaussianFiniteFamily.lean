import appendix_b_reference.KungTraub.FiniteFamilyGeometry
import appendix_b_reference.KungTraub.EntireFamilies

/-!
# Instantiating the finite family with Gaussian corrections

All analytic fields in `FiniteRootFamily` are derived here. The multiplier and
positive scale threshold precede the parameter and scale choices. The constants
are m=1/2, M=3/2, R=5/4, w_*=|w(a)|/2 and K=b, uniformly in the scale.
-/

noncomputable section
open Set
open scoped InnerProductSpace

namespace KungTraub

theorem gaussianCorrection_eq_parameter_inner (p : Polynomial ℝ) (n : ℕ)
    (lam ε x : ℝ) (u : EuclideanSpace ℝ (Fin (n + 1))) (t : ℝ) :
    gaussianCorrection p n lam ε x u t =
      ⟪u, realPolynomialEvaluationVector n ε (lam * gaussianPolynomial p t) (t - x)⟫_ℝ := by
  sorry

theorem gaussianCoefficientVector_lipschitz {p : Polynomial ℝ} {n : ℕ}
    {lam b ε x : ℝ} (hsmall : GaussianCorrectionSmall p n lam b)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hx : |x| ≤ 1) (s t : ℝ) :
    ‖realPolynomialEvaluationVector n ε (lam * gaussianPolynomial p s) (s - x) -
      realPolynomialEvaluationVector n ε (lam * gaussianPolynomial p t) (t - x)‖ ≤
      b * |s - t| := by
  sorry

theorem gaussianCorrection_exists_finiteRootFamily {f : ℝ → ℝ}
    {p : Polynomial ℝ} {n : ℕ} {lam b B a : ℝ}
    (hf : Differentiable ℝ f)
    (hf' : ∀ t, (15 : ℝ) / 16 ≤ deriv f t ∧ deriv f t ≤ 17 / 16)
    (hidentity : ∀ t, |f t - t| ≤ B)
    (hsmall : GaussianCorrectionSmall p n lam b) (hb : b ≤ 1 / 16)
    (ha : |a| ≤ 1 / 4) (hfa : f a = 0) (hwa : lam * gaussianPolynomial p a ≠ 0) :
    ∃ η > 0, ∀ ε : ℝ, 0 < ε → ε < η →
      ∃ D : FiniteRootFamily n ε (a + ε) (1 / 2) (3 / 2) (5 / 4)
          (|lam * gaussianPolynomial p a| / 2) b,
        (∀ u t, D.function u t = f t + gaussianCorrection p n lam ε (a + ε) u t) ∧
        D.weight = (fun t => lam * gaussianPolynomial p t) ∧ D.interval = univ := by
  sorry

end KungTraub
