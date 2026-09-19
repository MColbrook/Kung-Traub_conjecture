import KungTraubAppendices.ComplexPolynomialInformation
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
  simp only [complexCorrectionPolynomial, complexParameterPolynomialMap, LinearMap.comp_apply,
    polynomialOfCoefficientsLinearMap_apply, polynomialOfCoefficients, Polynomial.sum_comp,
    Polynomial.monomial_comp, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change p * (C (if i = 0 then (ε : ℂ) * u i else u i) * (X - C x) ^ i.val) = _
  ring

/-- Evaluation is exactly the family bracket from Appendix B. -/
theorem complexCorrectionPolynomial_eval (p : Polynomial ℂ) (n : ℕ) (ε : ℝ) (x : ℂ)
    (u : EuclideanSpace ℂ (Fin (n + 1))) (z : ℂ) :
    (complexCorrectionPolynomial p n ε x u).eval z = p.eval z *
      ((ε : ℂ) * u 0 + ∑ i : Fin n, u i.succ * (z - x) ^ (i.val + 1)) := by
  rw [complexCorrectionPolynomial_eq_sum, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Fin.sum_univ_succ,
    ↓reduceIte, pow_zero, mul_one, Fin.succ_ne_zero, Fin.val_succ, Fin.val_zero]
  simp only [mul_add, Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro i _
    ring

/-- Every correction retains the original polynomial factor. -/
theorem complexCorrectionPolynomial_dvd (p : Polynomial ℂ) (n : ℕ) (ε : ℝ) (x : ℂ)
    (u : EuclideanSpace ℂ (Fin (n + 1))) : p ∣ complexCorrectionPolynomial p n ε x u :=
  dvd_mul_right _ _

/-- Separate full-disc value and unit-disc derivative bounds with one finite constant. -/
def ComplexPolynomialDiscBound (p : Polynomial ℂ) (R C : ℝ) : Prop :=
  (∀ z : ℂ, ‖z‖ ≤ R → ‖p.eval z‖ ≤ C) ∧
    ∀ t : ℂ, ‖t‖ ≤ 1 → ‖p.derivative.eval t‖ ≤ C

/-- Joint continuity of a shifted polynomial basis value in both complex variables. -/
theorem continuous_shiftedPolynomial_eval (p : Polynomial ℂ) (k : ℕ) :
    Continuous (fun v : ℂ × ℂ => (p * (X - C v.1) ^ k).eval v.2) := by
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C]
  fun_prop

/-- Joint continuity includes the derivative, including the k=0 basis term. -/
theorem continuous_shiftedPolynomial_derivative_eval (p : Polynomial ℂ) (k : ℕ) :
    Continuous (fun v : ℂ × ℂ => (p * (X - C v.1) ^ k).derivative.eval v.2) := by
  simp only [Polynomial.derivative_mul, Polynomial.derivative_pow, Polynomial.derivative_sub,
    Polynomial.derivative_X, Polynomial.derivative_C, sub_zero, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_one]
  fun_prop

/-- Compactness gives a bound uniform in the complex unit-disc shift and an arbitrary disc. -/
theorem exists_uniform_complex_pair_disc_bound (F : ℂ × ℂ → ℂ) (hF : Continuous F) (R : ℝ) :
    ∃ C > 0, ∀ x : ℂ, ‖x‖ ≤ 1 → ∀ z : ℂ, ‖z‖ ≤ R → ‖F (x, z)‖ ≤ C := by
  have hcompact := ((isCompact_closedBall (0 : ℂ) 1).prod
    (isCompact_closedBall (0 : ℂ) R)).image hF
  obtain ⟨C, hC, hbound⟩ := hcompact.isBounded.exists_pos_norm_le
  refine ⟨C, hC, fun x hx z hz => hbound _ ?_⟩
  exact ⟨(x, z), ⟨by simpa using hx, by simpa using hz⟩, rfl⟩

/-- One finite bound works for all unit-disc shifts of each fixed polynomial basis term. -/
theorem shiftedPolynomial_exists_disc_bound (p : Polynomial ℂ) (R : ℝ) (k : ℕ) :
    ∃ B > 0, ∀ x : ℂ, ‖x‖ ≤ 1 → ComplexPolynomialDiscBound (p * (X - C x) ^ k) R B := by
  obtain ⟨A, hA, ha⟩ := exists_uniform_complex_pair_disc_bound _
    (continuous_shiftedPolynomial_eval p k) R
  obtain ⟨B, hB, hb⟩ := exists_uniform_complex_pair_disc_bound _
    (continuous_shiftedPolynomial_derivative_eval p k) 1
  refine ⟨A + B, by positivity, fun x hx => ⟨?_, ?_⟩⟩
  · intro z hz
    exact (ha x hx z hz).trans (by linarith)
  · intro t ht
    exact (hb x hx t ht).trans (by linarith)

/-- A complex coefficient of modulus at most one preserves the common bound. -/
theorem complexPolynomialDiscBound_C_mul {p : Polynomial ℂ} {R B : ℝ} {c : ℂ}
    (hp : ComplexPolynomialDiscBound p R B) (hc : ‖c‖ ≤ 1) :
    ComplexPolynomialDiscBound (C c * p) R B := by
  constructor
  · intro z hz
    simpa only [Polynomial.eval_mul, Polynomial.eval_C, norm_mul, one_mul] using
      (mul_le_mul_of_nonneg_right hc (norm_nonneg (p.eval z))).trans (by simpa using hp.1 z hz)
  · intro t ht
    simpa only [Polynomial.derivative_C_mul, Polynomial.eval_mul, Polynomial.eval_C,
      norm_mul, one_mul] using
      (mul_le_mul_of_nonneg_right hc (norm_nonneg (p.derivative.eval t))).trans
        (by simpa using hp.2 t ht)

/-- Finite sums preserve the sum of the separate value and derivative bounds. -/
theorem complexPolynomialDiscBound_sum {ι : Type*} (s : Finset ι) (p : ι → Polynomial ℂ)
    (B : ι → ℝ) (R : ℝ) (h : ∀ i ∈ s, ComplexPolynomialDiscBound (p i) R (B i)) :
    ComplexPolynomialDiscBound (∑ i ∈ s, p i) R (∑ i ∈ s, B i) := by
  constructor
  · intro z hz
    rw [Polynomial.eval_finsetSum]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i hi => (h i hi).1 z hz))
  · intro t ht
    rw [Polynomial.derivative_sum, Polynomial.eval_finsetSum]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i hi => (h i hi).2 t ht))

/-- The full coefficient ball and all scales in [0,1] share one finite bound,
chosen before the scale, complex center, and parameter vector. -/
theorem complexCorrectionPolynomial_exists_uniform_bound (p : Polynomial ℂ) (n : ℕ) (R : ℝ) :
    ∃ B > 0, ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ x : ℂ, ‖x‖ ≤ 1 →
      ∀ u : EuclideanSpace ℂ (Fin (n + 1)), ‖u‖ ≤ 1 →
        ComplexPolynomialDiscBound (complexCorrectionPolynomial p n ε x u) R B := by
  classical
  choose B hB hbound using fun i : Fin (n + 1) => shiftedPolynomial_exists_disc_bound p R i.val
  refine ⟨∑ i, B i, Finset.sum_pos (fun i _ => hB i) Finset.univ_nonempty,
    fun ε hε0 hε1 x hx u hu => ?_⟩
  rw [complexCorrectionPolynomial_eq_sum]
  apply complexPolynomialDiscBound_sum
  intro i _
  apply complexPolynomialDiscBound_C_mul (hbound i x hx)
  have hui : ‖u i‖ ≤ 1 := (PiLp.norm_apply_le u i).trans hu
  split_ifs
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hε0]
    exact (mul_le_mul hε1 hui (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  · exact hui

/-- A nonnegative multiplier scales the two bounds by the same scalar. -/
theorem complexPolynomialDiscBound_scaled {p : Polynomial ℂ} {R B lam : ℝ}
    (hp : ComplexPolynomialDiscBound p R B) (hlam : 0 ≤ lam) :
    ComplexPolynomialDiscBound (C (lam : ℂ) * p) R (lam * B) := by
  constructor
  · intro z hz
    simpa only [Polynomial.eval_mul, Polynomial.eval_C, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hlam] using mul_le_mul_of_nonneg_left (hp.1 z hz) hlam
  · intro t ht
    simpa only [Polynomial.derivative_C_mul, Polynomial.eval_mul, Polynomial.eval_C,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlam] using
      mul_le_mul_of_nonneg_left (hp.2 t ht) hlam

/-- The original factor remains after choosing any multiplier. -/
theorem scaled_complexCorrectionPolynomial_dvd (p : Polynomial ℂ) (n : ℕ)
    (ε lam : ℝ) (x : ℂ) (u : EuclideanSpace ℂ (Fin (n + 1))) :
    p ∣ C (lam : ℂ) * complexCorrectionPolynomial p n ε x u :=
  (complexCorrectionPolynomial_dvd p n ε x u).trans (dvd_mul_left _ _)

/-- One positive multiplier makes each of the two separate full-disc bounds at most b/2. -/
theorem complexCorrectionPolynomial_exists_small_scaling (p : Polynomial ℂ) (n : ℕ)
    (R : ℝ) {b : ℝ} (hb : 0 < b) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ x : ℂ, ‖x‖ ≤ 1 →
      ∀ u : EuclideanSpace ℂ (Fin (n + 1)), ‖u‖ ≤ 1 →
        ComplexPolynomialDiscBound (C (lam : ℂ) * complexCorrectionPolynomial p n ε x u) R (b / 2) := by
  obtain ⟨B, hB, hbound⟩ := complexCorrectionPolynomial_exists_uniform_bound p n R
  let lam := b / (2 * B)
  have hlam : 0 < lam := div_pos hb (by positivity)
  refine ⟨lam, hlam, fun ε hε0 hε1 x hx u hu => ?_⟩
  have h := complexPolynomialDiscBound_scaled (hbound ε hε0 hε1 x hx u hu) hlam.le
  have heq : lam * B = b / 2 := by dsimp [lam]; field_simp
  simpa only [heq] using h

/-- The actual sum of the value supremum and derivative supremum is controlled.
Both domains are the full closed discs; the multiplier precedes every parameter choice. -/
theorem complexCorrectionPolynomial_exists_small_sup_sum (p : Polynomial ℂ) (n : ℕ)
    {R b : ℝ} (hR : 1 ≤ R) (hb : 0 < b) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ x : ℂ, ‖x‖ ≤ 1 →
      ∀ u : EuclideanSpace ℂ (Fin (n + 1)), ‖u‖ ≤ 1 →
        let q := C (lam : ℂ) * complexCorrectionPolynomial p n ε x u
        sSup ((fun z : ℂ => ‖q.eval z‖) '' Metric.closedBall (0 : ℂ) R) +
          sSup ((fun t : ℂ => ‖deriv (fun z => q.eval z) t‖) '' Metric.closedBall (0 : ℂ) 1) ≤ b := by
  obtain ⟨lam, hlam, hbound⟩ := complexCorrectionPolynomial_exists_small_scaling p n R hb
  refine ⟨lam, hlam, fun ε hε0 hε1 x hx u hu => ?_⟩
  let q := C (lam : ℂ) * complexCorrectionPolynomial p n ε x u
  have hq : ComplexPolynomialDiscBound q R (b / 2) := hbound ε hε0 hε1 x hx u hu
  have hneR : (Metric.closedBall (0 : ℂ) R).Nonempty :=
    ⟨0, by simp; linarith⟩
  have hne1 : (Metric.closedBall (0 : ℂ) 1).Nonempty := ⟨0, by simp⟩
  have hv : sSup ((fun z : ℂ => ‖q.eval z‖) '' Metric.closedBall (0 : ℂ) R) ≤ b / 2 := by
    apply csSup_le (hneR.image _)
    rintro v ⟨z, hz, rfl⟩
    exact hq.1 z (by simpa using hz)
  have hd : sSup ((fun t : ℂ => ‖deriv (fun z => q.eval z) t‖) ''
      Metric.closedBall (0 : ℂ) 1) ≤ b / 2 := by
    apply csSup_le (hne1.image _)
    rintro v ⟨t, ht, rfl⟩
    change ‖deriv (fun z => q.eval z) t‖ ≤ b / 2
    rw [q.deriv]
    exact hq.2 t (by simpa using ht)
  dsimp only
  change _ + _ ≤ b
  linarith

end KungTraubAppendices
