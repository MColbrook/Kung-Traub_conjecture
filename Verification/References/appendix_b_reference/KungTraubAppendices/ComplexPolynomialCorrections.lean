import appendix_b_reference.KungTraubAppendices.ComplexPolynomialInformation
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.Algebra.Polynomial

/-!
# Uniformly small complex polynomial corrections

The fixed polynomial factor is preserved throughout. Compactness is used only
for the continuous value and derivative of each shifted polynomial basis term,
with the shift ranging over the full closed unit disc. Finite sums and coordinate
norm bounds then give uniform control over the full Euclidean coefficient ball
and every real scale in [0,1]. One positive multiplier is chosen before all of
these parameters. Both suprema in Appendix B are controlled in their sum.

The compact-image boundedness argument uses Mathlib. Finite coefficient
reconstruction is reused from `ComplexPolynomialInformation`; the basis-bound
proof follows `KungTraub.GaussianBounds` for polynomial corrections.
-/

noncomputable section

open KungTraub Polynomial Set
open scoped BigOperators

namespace KungTraubAppendices

/-- The unscaled correction, with the exact polynomial factor prescribing old jets. -/
def complexCorrectionPolynomial (p : Polynomial ℂ) (n : ℕ) (ε : ℝ) (x : ℂ)
    (u : EuclideanSpace ℂ (Fin (n + 1))) : Polynomial ℂ :=
  p * (complexParameterPolynomialMap n ε u).comp (X - C x)

/-- Finite basis expansion of the exact centered parameter polynomial. -/
theorem complexCorrectionPolynomial_eq_sum (p : Polynomial ℂ) (n : ℕ) (ε : ℝ) (x : ℂ)
    (u : EuclideanSpace ℂ (Fin (n + 1))) :
    complexCorrectionPolynomial p n ε x u =
      ∑ i : Fin (n + 1), C (if i = 0 then (ε : ℂ) * u i else u i) *
        (p * (X - C x) ^ i.val) := by
  sorry

/-- Evaluation is exactly the family bracket from Appendix B. -/
theorem complexCorrectionPolynomial_eval (p : Polynomial ℂ) (n : ℕ) (ε : ℝ) (x : ℂ)
    (u : EuclideanSpace ℂ (Fin (n + 1))) (z : ℂ) :
    (complexCorrectionPolynomial p n ε x u).eval z = p.eval z *
      ((ε : ℂ) * u 0 + ∑ i : Fin n, u i.succ * (z - x) ^ (i.val + 1)) := by
  sorry

/-- Every correction retains the original polynomial factor. -/
theorem complexCorrectionPolynomial_dvd (p : Polynomial ℂ) (n : ℕ) (ε : ℝ) (x : ℂ)
    (u : EuclideanSpace ℂ (Fin (n + 1))) : p ∣ complexCorrectionPolynomial p n ε x u := by
  sorry

/-- Separate full-disc value and unit-disc derivative bounds with one finite constant. -/
def ComplexPolynomialDiscBound (p : Polynomial ℂ) (R C : ℝ) : Prop :=
  (∀ z : ℂ, ‖z‖ ≤ R → ‖p.eval z‖ ≤ C) ∧
    ∀ t : ℂ, ‖t‖ ≤ 1 → ‖p.derivative.eval t‖ ≤ C

/-- Joint continuity of a shifted polynomial basis value in both complex variables. -/
theorem continuous_shiftedPolynomial_eval (p : Polynomial ℂ) (k : ℕ) :
    Continuous (fun v : ℂ × ℂ => (p * (X - C v.1) ^ k).eval v.2) := by
  sorry

/-- Joint continuity includes the derivative, including the k=0 basis term. -/
theorem continuous_shiftedPolynomial_derivative_eval (p : Polynomial ℂ) (k : ℕ) :
    Continuous (fun v : ℂ × ℂ => (p * (X - C v.1) ^ k).derivative.eval v.2) := by
  sorry

/-- Compactness gives a bound uniform in the complex unit-disc shift and an arbitrary disc. -/
theorem exists_uniform_complex_pair_disc_bound (F : ℂ × ℂ → ℂ) (hF : Continuous F) (R : ℝ) :
    ∃ C > 0, ∀ x : ℂ, ‖x‖ ≤ 1 → ∀ z : ℂ, ‖z‖ ≤ R → ‖F (x, z)‖ ≤ C := by
  sorry

/-- One finite bound works for all unit-disc shifts of each fixed polynomial basis term. -/
theorem shiftedPolynomial_exists_disc_bound (p : Polynomial ℂ) (R : ℝ) (k : ℕ) :
    ∃ B > 0, ∀ x : ℂ, ‖x‖ ≤ 1 → ComplexPolynomialDiscBound (p * (X - C x) ^ k) R B := by
  sorry

/-- A complex coefficient of modulus at most one preserves the common bound. -/
theorem complexPolynomialDiscBound_C_mul {p : Polynomial ℂ} {R B : ℝ} {c : ℂ}
    (hp : ComplexPolynomialDiscBound p R B) (hc : ‖c‖ ≤ 1) :
    ComplexPolynomialDiscBound (C c * p) R B := by
  sorry

/-- Finite sums preserve the sum of the separate value and derivative bounds. -/
theorem complexPolynomialDiscBound_sum {ι : Type*} (s : Finset ι) (p : ι → Polynomial ℂ)
    (B : ι → ℝ) (R : ℝ) (h : ∀ i ∈ s, ComplexPolynomialDiscBound (p i) R (B i)) :
    ComplexPolynomialDiscBound (∑ i ∈ s, p i) R (∑ i ∈ s, B i) := by
  sorry

/-- The full coefficient ball and all scales in [0,1] share one finite bound,
chosen before the scale, complex center, and parameter vector. -/
theorem complexCorrectionPolynomial_exists_uniform_bound (p : Polynomial ℂ) (n : ℕ) (R : ℝ) :
    ∃ B > 0, ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ x : ℂ, ‖x‖ ≤ 1 →
      ∀ u : EuclideanSpace ℂ (Fin (n + 1)), ‖u‖ ≤ 1 →
        ComplexPolynomialDiscBound (complexCorrectionPolynomial p n ε x u) R B := by
  sorry

/-- A nonnegative multiplier scales the two bounds by the same scalar. -/
theorem complexPolynomialDiscBound_scaled {p : Polynomial ℂ} {R B lam : ℝ}
    (hp : ComplexPolynomialDiscBound p R B) (hlam : 0 ≤ lam) :
    ComplexPolynomialDiscBound (C (lam : ℂ) * p) R (lam * B) := by
  sorry

/-- The original factor remains after choosing any multiplier. -/
theorem scaled_complexCorrectionPolynomial_dvd (p : Polynomial ℂ) (n : ℕ)
    (ε lam : ℝ) (x : ℂ) (u : EuclideanSpace ℂ (Fin (n + 1))) :
    p ∣ C (lam : ℂ) * complexCorrectionPolynomial p n ε x u := by
  sorry

/-- One positive multiplier makes each of the two separate full-disc bounds at most b/2. -/
theorem complexCorrectionPolynomial_exists_small_scaling (p : Polynomial ℂ) (n : ℕ)
    (R : ℝ) {b : ℝ} (hb : 0 < b) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ x : ℂ, ‖x‖ ≤ 1 →
      ∀ u : EuclideanSpace ℂ (Fin (n + 1)), ‖u‖ ≤ 1 →
        ComplexPolynomialDiscBound (C (lam : ℂ) * complexCorrectionPolynomial p n ε x u) R (b / 2) := by
  sorry

/-- The actual sum of the value supremum and derivative supremum is controlled.
Both domains are the full closed discs; the multiplier precedes every parameter choice. -/
theorem complexCorrectionPolynomial_exists_small_sup_sum (p : Polynomial ℂ) (n : ℕ)
    {R b : ℝ} (hR : 1 ≤ R) (hb : 0 < b) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ x : ℂ, ‖x‖ ≤ 1 →
      ∀ u : EuclideanSpace ℂ (Fin (n + 1)), ‖u‖ ≤ 1 →
        let q := C (lam : ℂ) * complexCorrectionPolynomial p n ε x u
        sSup ((fun z : ℂ => ‖q.eval z‖) '' Metric.closedBall (0 : ℂ) R) +
          sSup ((fun t : ℂ => ‖deriv (fun z => q.eval z) t‖) '' Metric.closedBall (0 : ℂ) 1) ≤ b := by
  sorry

end KungTraubAppendices
