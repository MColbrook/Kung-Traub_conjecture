import appendix_b_reference.KungTraubAppendices.ComplexPolynomialSensitivity

/-!
# Dimension-independent bounds for the complex evaluation vector

The squared Euclidean norm is a finite geometric sum, bounded using
`KungTraub.sum_powers_le_two`. The old-root estimate follows the corresponding
Gaussian-family estimate over the complex coefficient space. A maximizing
complex direction gives the dual characterization on each subspace.
-/

noncomputable section

open KungTraub
open scoped BigOperators

namespace KungTraubAppendices

/-- The exact square of the actual complex evaluation-vector norm. -/
theorem complexPolynomialEvaluationVector_norm_sq (n : ℕ) {ε : ℝ}
    (hε : 0 ≤ ε) (w s : ℂ) :
    ‖complexPolynomialEvaluationVector n ε w s‖ ^ 2 =
      ‖w‖ ^ 2 * (ε ^ 2 + ‖s‖ ^ 2 * ∑ i : Fin n, (‖s‖ ^ 2) ^ i.val) := by
  sorry

/-- The full half-disc has a uniform squared-norm bound, independently of n. -/
theorem complexPolynomialEvaluationVector_norm_sq_le (n : ℕ) {ε : ℝ}
    (hε : 0 ≤ ε) (w s : ℂ) (hs : ‖s‖ ≤ 1 / 2) :
    ‖complexPolynomialEvaluationVector n ε w s‖ ^ 2 ≤
      ‖w‖ ^ 2 * (ε ^ 2 + 2 * ‖s‖ ^ 2) := by
  sorry

/-- The O(epsilon + distance) bound holds on the complete complex half-disc. -/
theorem complexPolynomialEvaluationVector_norm_le (n : ℕ) {ε : ℝ}
    (hε : 0 ≤ ε) (w s : ℂ) (hs : ‖s‖ ≤ 1 / 2) :
    ‖complexPolynomialEvaluationVector n ε w s‖ ≤ ‖w‖ * (ε + 2 * ‖s‖) := by
  sorry

/-- At the old root the geometric-square sum gives the sharper factor three. -/
theorem complexPolynomialEvaluationVector_old_root_norm_sq_le (n : ℕ) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 4) (w : ℂ) :
    ‖complexPolynomialEvaluationVector n ε w (-(ε : ℂ))‖ ^ 2 ≤
      3 * ‖w‖ ^ 2 * ε ^ 2 := by
  sorry

/-- The actual weighted vector at the old root has norm at most 2*|w|*epsilon. -/
theorem complexPolynomialEvaluationVector_old_root_norm_le (n : ℕ) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 4) (w : ℂ) :
    ‖complexPolynomialEvaluationVector n ε w (-(ε : ℂ))‖ ≤ 2 * ‖w‖ * ε := by
  sorry

/-- The actual parameter polynomial bracket is small at the old root for every
complex coefficient vector in the complete closed Euclidean unit ball. -/
theorem complexParameterPolynomialMap_old_root_bound {n : ℕ} {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 4)
    (u : EuclideanSpace ℂ (Fin (n + 1))) (hu : ‖u‖ ≤ 1) :
    ‖(complexParameterPolynomialMap n ε u).eval (-(ε : ℂ))‖ ≤ 2 * ε := by
  sorry

/-- Expanded form of the same polynomial bracket. -/
theorem complex_family_bracket_at_old_root_le {n : ℕ} {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 4)
    (u : EuclideanSpace ℂ (Fin (n + 1))) (hu : ‖u‖ ≤ 1) :
    ‖(ε : ℂ) * u 0 + ∑ i : Fin n, u i.succ * (-(ε : ℂ)) ^ (i.val + 1)‖ ≤ 2 * ε := by
  sorry

/-- Bounds on all unit complex bilinear evaluations bound the full Euclidean
vector norm. The estimate includes the zero vector. -/
theorem norm_le_of_complexBilinearDot_unit_bound {d : ℕ}
    (v : EuclideanSpace ℂ (Fin d)) {b : ℝ} (hb : 0 ≤ b)
    (hbound : ∀ u : EuclideanSpace ℂ (Fin d), ‖u‖ ≤ 1 →
      ‖complexBilinearDot u v‖ ≤ b) : ‖v‖ ≤ b := by
  sorry

end KungTraubAppendices
