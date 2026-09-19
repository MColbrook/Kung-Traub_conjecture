import appendix_reference.KungTraubAppendices.ExponentialInverse
import appendix_reference.KungTraubAppendices.HermiteDividedDifference
import appendix_reference.KungTraubAppendices.HermiteOrderConstants
import appendix_reference.KungTraubAppendices.SharpnessElementary
import Mathlib.Topology.Algebra.Monoid

/-!
# One analytic sharpness step for the observed Hermite polynomial

Source: Appendix A of Matthew J. Colbrook's manuscript. The polynomial receives
only the observed values of `exp x - 1`, the earlier points and the reciprocal
of the derivative at the first point. The exact Hermite remainder, the logarithm
coefficient limit, and Mathlib's continuous derivative-valued slope supply the
step. The exponent product reuses `mul_prod_pow_two`.

The step uses the earlier point asymptotics and eventual injectivity.
-/

noncomputable section

open Set Filter Polynomial
open scoped Topology BigOperators

namespace KungTraubAppendices

/-- The single derivative datum in the exponential observation method. -/
theorem deriv_exp_sub_one (x : ℝ) :
    deriv (fun t : ℝ => Real.exp t - 1) x = Real.exp x := by
  sorry

/-- The derivative of the analytic inverse equals the reciprocal of the
one observed derivative; no additional observation is involved. -/
theorem deriv_log_one_add_at_exp_sub_one (x : ℝ) :
    deriv (fun t : ℝ => Real.log (1 + t)) (Real.exp x - 1) =
      (deriv (fun t : ℝ => Real.exp t - 1) x)⁻¹ := by
  sorry

/-- The actual data polynomial, as a function of the earlier real points. -/
def exponentialHermitePolynomial {j : ℕ} (points : Fin (j + 1) → ℝ) : ℝ[X] :=
  hermiteWithDerivative Finset.univ (fun i => Real.exp (points i) - 1) points 0
    ((deriv (fun t : ℝ => Real.exp t - 1) (points 0))⁻¹)

/-- The exact signed remainder, expressed as an extra initial factor
times the product over all observed values. -/
theorem exponentialHermitePolynomial_zero (j : ℕ) (points : Fin (j + 1) → ℝ)
    (hpoints : Function.Injective points) :
    (exponentialHermitePolynomial points).eval 0 =
      (-1 : ℝ) ^ (j + 1) *
        confluentDividedDifference (fun t : ℝ => Real.log (1 + t))
          (0 :: (Real.exp (points 0) - 1) ::
            List.ofFn (fun i => Real.exp (points i) - 1)) *
        (Real.exp (points 0) - 1) * ∏ i, (Real.exp (points i) - 1) := by
  sorry

/-- A finite normalized power limit forces the point itself to approach zero. -/
theorem tendsto_zero_of_normalized_pow {k : ℕ} (hk : 0 < k)
    (y : ℝ → ℝ) (c : ℝ)
    (hy : Tendsto (fun x => y x / x ^ k) (𝓝[≠] (0 : ℝ)) (𝓝 c)) :
    Tendsto y (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  sorry

/-- Exponentiation preserves the leading normalized point coefficient.
Derivative-valued slopes include zero points, at zero as well. -/
theorem exp_sub_one_normalized_tendsto {k : ℕ} (hk : 0 < k)
    (y : ℝ → ℝ) (c : ℝ)
    (hy : Tendsto (fun x => y x / x ^ k) (𝓝[≠] (0 : ℝ)) (𝓝 c)) :
    Tendsto (fun x => (Real.exp (y x) - 1) / x ^ k)
      (𝓝[≠] (0 : ℝ)) (𝓝 c) := by
  sorry

/-- Normalizing the extra first factor and every indexed factor gives the
exact doubled exponent, including the singleton stage. -/
theorem normalized_hermite_product (j : ℕ) (v : Fin (j + 1) → ℝ) (x : ℝ) :
    v 0 * (∏ i, v i) / x ^ (2 ^ (j + 1)) =
      (v 0 / x) * ∏ i, (v i / x ^ (2 ^ i.val)) := by
  sorry

/-- One analytic step gives the next exact coefficient. Eventual
injectivity and all earlier asymptotics remain explicit hypotheses. -/
theorem exponentialHermiteStep_tendsto (j : ℕ)
    (points : ℝ → Fin (j + 1) → ℝ)
    (hinj : ∀ᶠ x in 𝓝[≠] (0 : ℝ), Function.Injective (points x))
    (hpoints : ∀ i, Tendsto (fun x => points x i / x ^ (2 ^ i.val))
      (𝓝[≠] (0 : ℝ)) (𝓝 (sharpnessCoefficient i.val))) :
    Tendsto (fun x => (exponentialHermitePolynomial (points x)).eval 0 /
      x ^ (2 ^ (j + 1))) (𝓝[≠] (0 : ℝ)) (𝓝 (sharpnessCoefficient (j + 1))) := by
  sorry

end KungTraubAppendices
