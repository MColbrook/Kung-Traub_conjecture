import KungTraubAppendices.ComplexPolynomialSensitivity

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
  have hterm (i : Fin n) : (‖s‖ ^ (i.val + 1)) ^ 2 =
      ‖s‖ ^ 2 * (‖s‖ ^ 2) ^ i.val := by
    rw [← pow_mul, Nat.mul_comm (i.val + 1) 2, pow_mul, pow_succ]
    ring
  rw [EuclideanSpace.norm_sq_eq]
  change (∑ i : Fin (n + 1), ‖w * (if i = 0 then (ε : ℂ) else s ^ i.val)‖ ^ 2) = _
  rw [Fin.sum_univ_succ]
  simp only [↓reduceIte, Fin.succ_ne_zero, Fin.val_succ, norm_mul, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hε, mul_pow, hterm]
  simp only [mul_add, Finset.mul_sum, mul_assoc]

/-- The full half-disc has a uniform squared-norm bound, independently of n. -/
theorem complexPolynomialEvaluationVector_norm_sq_le (n : ℕ) {ε : ℝ}
    (hε : 0 ≤ ε) (w s : ℂ) (hs : ‖s‖ ≤ 1 / 2) :
    ‖complexPolynomialEvaluationVector n ε w s‖ ^ 2 ≤
      ‖w‖ ^ 2 * (ε ^ 2 + 2 * ‖s‖ ^ 2) := by
  have hsum : (∑ i : Fin n, (‖s‖ ^ 2) ^ i.val) ≤ 2 := by
    rw [Fin.sum_univ_eq_sum_range]
    exact sum_powers_le_two (sq_nonneg ‖s‖) (by nlinarith [norm_nonneg s]) n
  rw [complexPolynomialEvaluationVector_norm_sq n hε w s]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg ‖w‖)
  have h := mul_le_mul_of_nonneg_left hsum (sq_nonneg ‖s‖)
  linarith

/-- The O(epsilon + distance) bound holds on the complete complex half-disc. -/
theorem complexPolynomialEvaluationVector_norm_le (n : ℕ) {ε : ℝ}
    (hε : 0 ≤ ε) (w s : ℂ) (hs : ‖s‖ ≤ 1 / 2) :
    ‖complexPolynomialEvaluationVector n ε w s‖ ≤ ‖w‖ * (ε + 2 * ‖s‖) := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  calc
    ‖complexPolynomialEvaluationVector n ε w s‖ ^ 2 ≤
        ‖w‖ ^ 2 * (ε ^ 2 + 2 * ‖s‖ ^ 2) :=
      complexPolynomialEvaluationVector_norm_sq_le n hε w s hs
    _ ≤ ‖w‖ ^ 2 * (ε + 2 * ‖s‖) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg ‖w‖)
      nlinarith [mul_nonneg hε (norm_nonneg s)]
    _ = (‖w‖ * (ε + 2 * ‖s‖)) ^ 2 := by ring

/-- At the old root the geometric-square sum gives the sharper factor three. -/
theorem complexPolynomialEvaluationVector_old_root_norm_sq_le (n : ℕ) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 4) (w : ℂ) :
    ‖complexPolynomialEvaluationVector n ε w (-(ε : ℂ))‖ ^ 2 ≤
      3 * ‖w‖ ^ 2 * ε ^ 2 := by
  have hnorm : ‖-(ε : ℂ)‖ = ε := by
    simp only [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hε0]
  have hhalf : ‖-(ε : ℂ)‖ ≤ 1 / 2 := by rw [hnorm]; linarith
  have h := complexPolynomialEvaluationVector_norm_sq_le n hε0 w (-(ε : ℂ)) hhalf
  rw [hnorm] at h
  nlinarith

/-- The actual weighted vector at the old root has norm at most 2*|w|*epsilon. -/
theorem complexPolynomialEvaluationVector_old_root_norm_le (n : ℕ) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 4) (w : ℂ) :
    ‖complexPolynomialEvaluationVector n ε w (-(ε : ℂ))‖ ≤ 2 * ‖w‖ * ε := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  have h := complexPolynomialEvaluationVector_old_root_norm_sq_le n hε0 hε w
  have hp := mul_nonneg (sq_nonneg ‖w‖) (sq_nonneg ε)
  nlinarith

/-- The actual parameter polynomial bracket is small at the old root for every
complex coefficient vector in the complete closed Euclidean unit ball. -/
theorem complexParameterPolynomialMap_old_root_bound {n : ℕ} {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 4)
    (u : EuclideanSpace ℂ (Fin (n + 1))) (hu : ‖u‖ ≤ 1) :
    ‖(complexParameterPolynomialMap n ε u).eval (-(ε : ℂ))‖ ≤ 2 * ε := by
  have hv : ‖complexPolynomialEvaluationVector n ε 1 (-(ε : ℂ))‖ ≤ 2 * ε := by
    simpa only [norm_one, mul_one] using
      complexPolynomialEvaluationVector_old_root_norm_le n hε0 hε (1 : ℂ)
  have h := norm_complexBilinearDot_le u
    (complexPolynomialEvaluationVector n ε 1 (-(ε : ℂ)))
  rw [complexPolynomialEvaluationVector_bilinear, one_mul] at h
  exact h.trans ((mul_le_mul_of_nonneg_left hu (norm_nonneg _)).trans
    (by simpa only [mul_one] using hv))

/-- Expanded form of the same polynomial bracket. -/
theorem complex_family_bracket_at_old_root_le {n : ℕ} {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 4)
    (u : EuclideanSpace ℂ (Fin (n + 1))) (hu : ‖u‖ ≤ 1) :
    ‖(ε : ℂ) * u 0 + ∑ i : Fin n, u i.succ * (-(ε : ℂ)) ^ (i.val + 1)‖ ≤ 2 * ε := by
  have h := complexParameterPolynomialMap_old_root_bound hε0 hε u hu
  have heval : (complexParameterPolynomialMap n ε u).eval (-(ε : ℂ)) =
      (ε : ℂ) * u 0 + ∑ i : Fin n, u i.succ * (-(ε : ℂ)) ^ (i.val + 1) := by
    rw [← one_mul ((complexParameterPolynomialMap n ε u).eval (-(ε : ℂ))),
      ← complexPolynomialEvaluationVector_bilinear]
    simp [complexBilinearDot, complexPolynomialEvaluationVector, Fin.sum_univ_succ, mul_comm]
  simpa only [heval] using h

/-- Bounds on all unit complex bilinear evaluations bound the full Euclidean
vector norm. The estimate includes the zero vector. -/
theorem norm_le_of_complexBilinearDot_unit_bound {d : ℕ}
    (v : EuclideanSpace ℂ (Fin d)) {b : ℝ} (hb : 0 ≤ b)
    (hbound : ∀ u : EuclideanSpace ℂ (Fin d), ‖u‖ ≤ 1 →
      ‖complexBilinearDot u v‖ ≤ b) : ‖v‖ ≤ b := by
  by_cases hv : v = 0
  · simpa only [hv, norm_zero] using hb
  have htop : (⊤ : Submodule ℂ (EuclideanSpace ℂ (Fin d))).starProjection
      (complexConjVector v) = complexConjVector v :=
    Submodule.starProjection_eq_self_iff.mpr (by trivial)
  have hpos : 0 < ‖(⊤ : Submodule ℂ (EuclideanSpace ℂ (Fin d))).starProjection
      (complexConjVector v)‖ := by
    rw [htop, norm_complexConjVector]
    exact norm_pos_iff.mpr hv
  obtain ⟨u, _, hu, hdot⟩ :=
    exists_complex_unit_direction_attaining_projected_norm ⊤ v hpos
  have h := hbound u hu.le
  rw [hdot, htop, norm_complexConjVector, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg v)] at h
  exact h

end KungTraubAppendices
