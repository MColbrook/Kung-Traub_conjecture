import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Analytic
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Tactic

/-!
# Gaussian times polynomial corrections

Bounds for the correction functions in Section 4 of Matthew J. Colbrook's
*Adversarial Wronskians: A proof of the Kung–Traub conjecture*.

The Gaussian decay theorem is due to David Loeffler in mathlib's Gaussian Poisson
summation module. Boundedness of continuous functions vanishing at infinity uses
Jireh Loreaux's `ZeroAtInftyContinuousMap.isBounded_range`. The derivative formula
uses the polynomial differentiation API of Sébastien Gouëzel and Eric Wieser; jet
vanishing uses Michail Karatarakis's `iteratedDeriv_mul_pow_sub_of_analytic`.
The remaining algebra, shift estimates and uniform scaling assemble those results
for the manuscript's precise domains.
-/

noncomputable section

open Filter Topology

namespace KungTraub

def gaussianPolynomial (p : Polynomial ℝ) (t : ℝ) : ℝ :=
  Real.exp (-(t ^ 2)) * p.eval t

def complexGaussianPolynomial (p : Polynomial ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-(z ^ 2)) * (p.map Complex.ofRealHom).eval z

/-- Every Gaussian times a real polynomial tends to zero at both ends of the real line. -/
theorem gaussianPolynomial_tendsto_zero (p : Polynomial ℝ) :
    Tendsto (gaussianPolynomial p) (cocompact ℝ) (𝓝 0) := by
  sorry

/-- Gaussian times polynomial is continuously defined on the full real line. -/
theorem gaussianPolynomial_continuous (p : Polynomial ℝ) :
    Continuous (gaussianPolynomial p) := by
  sorry

/-- There is a positive global bound; no bounded real domain is imposed. -/
theorem gaussianPolynomial_exists_bound (p : Polynomial ℝ) :
    ∃ C > 0, ∀ t : ℝ, |gaussianPolynomial p t| ≤ C := by
  sorry

/-- Differentiation preserves the Gaussian times polynomial form. -/
theorem gaussianPolynomial_hasDerivAt (p : Polynomial ℝ) (t : ℝ) :
    HasDerivAt (gaussianPolynomial p)
      (gaussianPolynomial (p.derivative - Polynomial.C 2 * Polynomial.X * p) t) t := by
  sorry

/-- The first derivative also vanishes at both ends of the real line. -/
theorem gaussianPolynomial_deriv_tendsto_zero (p : Polynomial ℝ) :
    Tendsto (deriv (gaussianPolynomial p)) (cocompact ℝ) (𝓝 0) := by
  sorry

/-- One positive constant bounds the sum of the function and its derivative globally. -/
theorem gaussianPolynomial_exists_C1_bound (p : Polynomial ℝ) :
    ∃ C > 0, ∀ t : ℝ, |gaussianPolynomial p t| + |deriv (gaussianPolynomial p) t| ≤ C := by
  sorry

/-- The complex extension is entire. -/
theorem complexGaussianPolynomial_differentiable (p : Polynomial ℝ) :
    Differentiable ℂ (complexGaussianPolynomial p) := by
  sorry

/-- Every fixed closed complex disc admits a finite positive bound. -/
theorem complexGaussianPolynomial_exists_disc_bound (p : Polynomial ℝ) (R : ℝ) :
    ∃ C > 0, ∀ z : ℂ, ‖z‖ ≤ R → ‖complexGaussianPolynomial p z‖ ≤ C := by
  sorry

/-- The entire extension agrees with the real function on the real axis. -/
theorem complexGaussianPolynomial_ofReal (p : Polynomial ℝ) (t : ℝ) :
    complexGaussianPolynomial p (t : ℂ) = (gaussianPolynomial p t : ℂ) := by
  sorry

/-- A prescribed linear factor of multiplicity `k + 1` annihilates the `k`th observation. -/
theorem gaussianPolynomial_iteratedDeriv_eq_zero {p : Polynomial ℝ} {a : ℝ} {k : ℕ}
    (hdiv : (Polynomial.X - Polynomial.C a) ^ (k + 1) ∣ p) :
    iteratedDeriv k (gaussianPolynomial p) a = 0 := by
  sorry

/-- A positive scalar reduces all three relevant bounds simultaneously. The two real
arguments are independent, as required for a sum of separate supremum bounds. -/
theorem gaussianPolynomial_exists_small_scaling (p : Polynomial ℝ) (R : ℝ)
    {b : ℝ} (hb : 0 < b) :
    ∃ lam > 0, ∀ t v : ℝ, ∀ z : ℂ, ‖z‖ ≤ R →
      |lam * gaussianPolynomial p t| +
        |deriv (fun y => lam * gaussianPolynomial p y) v| +
        ‖(lam : ℂ) * complexGaussianPolynomial p z‖ ≤ b := by
  sorry

/-- The three estimates attached to one polynomial, with independent real arguments. -/
def GaussianBound (p : Polynomial ℝ) (R C : ℝ) : Prop :=
  (∀ t : ℝ, |gaussianPolynomial p t| ≤ C) ∧
  (∀ t : ℝ, |deriv (gaussianPolynomial p) t| ≤ C) ∧
  (∀ z : ℂ, ‖z‖ ≤ R → ‖complexGaussianPolynomial p z‖ ≤ C)

theorem gaussianPolynomial_exists_common_bound (p : Polynomial ℝ) (R : ℝ) :
    ∃ C > 0, GaussianBound p R C := by
  sorry

theorem gaussianBound_add {p q : Polynomial ℝ} {R C D : ℝ}
    (hp : GaussianBound p R C) (hq : GaussianBound q R D) :
    GaussianBound (p + q) R (C + D) := by
  sorry

theorem gaussianBound_C_mul {p : Polynomial ℝ} {R C a : ℝ}
    (hp : GaussianBound p R C) (ha : |a| ≤ 1) :
    GaussianBound (Polynomial.C a * p) R C := by
  sorry

/-- Shifting a bounded-degree polynomial factor through every centre in `[-1,1]`
admits one bound on the whole real line and the chosen complex disc. -/
theorem gaussianPolynomial_exists_shift_bound (p : Polynomial ℝ) (R : ℝ) (k : ℕ) :
    ∃ C > 0, ∀ x : ℝ, |x| ≤ 1 →
      GaussianBound (p * (Polynomial.X - Polynomial.C x) ^ k) R C := by
  sorry

theorem gaussianBound_sum {ι : Type*} (s : Finset ι) (p : ι → Polynomial ℝ)
    (C : ι → ℝ) (R : ℝ) (h : ∀ i ∈ s, GaussianBound (p i) R (C i)) :
    GaussianBound (∑ i ∈ s, p i) R (∑ i ∈ s, C i) := by
  sorry

/-- The polynomial part of the manuscript's real correction, before the common scalar.
Only the coefficient `u 0` is multiplied by the scale `ε`. -/
def gaussianCorrectionPolynomial (p : Polynomial ℝ) (n : ℕ) (ε x : ℝ)
    (u : Fin (n + 1) → ℝ) : Polynomial ℝ :=
  ∑ i : Fin (n + 1), Polynomial.C (if i = 0 then ε * u i else u i) *
    (p * (Polynomial.X - Polynomial.C x) ^ i.val)

/-- Evaluation gives exactly the correction family used in Section 4. -/
theorem gaussianCorrectionPolynomial_eval (p : Polynomial ℝ) (n : ℕ) (ε x : ℝ)
    (u : Fin (n + 1) → ℝ) (t : ℝ) :
    gaussianPolynomial (gaussianCorrectionPolynomial p n ε x u) t =
      Real.exp (-(t ^ 2)) * p.eval t *
        (ε * u 0 + ∑ i : Fin n, u i.succ * (t - x) ^ (i.val + 1)) := by
  sorry

/-- The coefficient box contains the Euclidean unit ball and gives one bound for all
scales and all starting points in the manuscript's specified intervals. -/
theorem gaussianCorrectionPolynomial_exists_uniform_bound (p : Polynomial ℝ) (n : ℕ)
    (R : ℝ) :
    ∃ C > 0, ∀ ε x : ℝ, 0 ≤ ε → ε ≤ 1 → |x| ≤ 1 →
      ∀ u : Fin (n + 1) → ℝ, (∀ i, |u i| ≤ 1) →
        GaussianBound (gaussianCorrectionPolynomial p n ε x u) R C := by
  sorry

/-- The common bound implies a bound after multiplying by any nonnegative scalar. -/
theorem gaussianBound_scaled_estimate {p : Polynomial ℝ} {R C lam : ℝ}
    (hp : GaussianBound p R C) (hlam : 0 ≤ lam)
    (t v : ℝ) (z : ℂ) (hz : ‖z‖ ≤ R) :
    |lam * gaussianPolynomial p t| +
      |deriv (fun y => lam * gaussianPolynomial p y) v| +
      ‖(lam : ℂ) * complexGaussianPolynomial p z‖ ≤ 3 * lam * C := by
  sorry

/-- One positive multiplier works for every scale, centre and Euclidean unit coefficient
vector. The real line is unrestricted and the complex-disc radius is arbitrary. -/
theorem gaussianCorrectionPolynomial_exists_small_scaling (p : Polynomial ℝ) (n : ℕ)
    (R : ℝ) {b : ℝ} (hb : 0 < b) :
    ∃ lam > 0, ∀ ε x : ℝ, 0 ≤ ε → ε ≤ 1 → |x| ≤ 1 →
      ∀ u : EuclideanSpace ℝ (Fin (n + 1)), ‖u‖ ≤ 1 →
        ∀ t v : ℝ, ∀ z : ℂ, ‖z‖ ≤ R →
          |lam * gaussianPolynomial (gaussianCorrectionPolynomial p n ε x u) t| +
          |deriv (fun y => lam * gaussianPolynomial
            (gaussianCorrectionPolynomial p n ε x u) y) v| +
          ‖(lam : ℂ) * complexGaussianPolynomial
            (gaussianCorrectionPolynomial p n ε x u) z‖ ≤ b := by
  sorry

/-- The Gaussian introduces no additional real zero. -/
theorem gaussianPolynomial_ne_zero {p : Polynomial ℝ} {t : ℝ} (hp : p.eval t ≠ 0) :
    gaussianPolynomial p t ≠ 0 := by
  sorry

/-- Every correction retains the polynomial factor prescribing earlier observations. -/
theorem gaussianCorrectionPolynomial_dvd (p : Polynomial ℝ) (n : ℕ) (ε x : ℝ)
    (u : Fin (n + 1) → ℝ) : p ∣ gaussianCorrectionPolynomial p n ε x u := by
  sorry

/-- All requested orders up to the prescribed multiplicity vanish, for every choice
of the correction parameters and every real scalar. -/
theorem gaussianCorrectionPolynomial_iteratedDeriv_eq_zero {p : Polynomial ℝ}
    {a : ℝ} {m k : ℕ} (hdiv : (Polynomial.X - Polynomial.C a) ^ (m + 1) ∣ p)
    (hk : k ≤ m) (n : ℕ) (ε x lam : ℝ) (u : Fin (n + 1) → ℝ) :
    iteratedDeriv k (fun t => lam * gaussianPolynomial
      (gaussianCorrectionPolynomial p n ε x u) t) a = 0 := by
  sorry

end KungTraub
