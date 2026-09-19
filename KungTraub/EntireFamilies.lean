import KungTraub.GaussianBounds
import KungTraub.FiniteRootMotion
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
          Polynomial.C 2 * Polynomial.X * gaussianCorrectionPolynomial p n ε x u) t) t :=
  (gaussianPolynomial_hasDerivAt _ t).const_mul lam

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
  intro ε x hε0 hε1 hx u hu t
  have hh := h ε x hε0 hε1 hx u hu t t 0 (by simpa using hR)
  change |gaussianCorrection p n lam ε x u t| +
    |deriv (gaussianCorrection p n lam ε x u) t| + _ ≤ b at hh
  constructor <;> linarith [abs_nonneg (gaussianCorrection p n lam ε x u t),
    abs_nonneg (deriv (gaussianCorrection p n lam ε x u) t),
    norm_nonneg ((lam : ℂ) * complexGaussianPolynomial
      (gaussianCorrectionPolynomial p n ε x u) 0)]

/-- The required uniform real estimates have an actual positive multiplier. -/
theorem exists_gaussianCorrectionSmall (p : Polynomial ℝ) (n : ℕ)
    {b : ℝ} (hb : 0 < b) : ∃ lam > 0, GaussianCorrectionSmall p n lam b := by
  obtain ⟨lam, hlam, h⟩ := gaussianCorrectionPolynomial_exists_small_scaling p n 0 hb
  exact ⟨lam, hlam, gaussianCorrectionSmall_of_three_bounds le_rfl h⟩

theorem gaussianCorrection_family_derivative_bounds {f : ℝ → ℝ}
    {p : Polynomial ℝ} {n : ℕ} {lam b ε x : ℝ}
    (hf : Differentiable ℝ f)
    (hf' : ∀ t, (15 : ℝ) / 16 ≤ deriv f t ∧ deriv f t ≤ 17 / 16)
    (hsmall : GaussianCorrectionSmall p n lam b) (hb : b ≤ 1 / 16)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hx : |x| ≤ 1)
    (u : EuclideanSpace ℝ (Fin (n + 1))) (hu : ‖u‖ ≤ 1) (t : ℝ) :
    (1 : ℝ) / 2 ≤ deriv (fun y => f y + gaussianCorrection p n lam ε x u y) t ∧
      deriv (fun y => f y + gaussianCorrection p n lam ε x u y) t ≤ 3 / 2 := by
  rw [deriv_fun_add (hf t) (gaussianCorrection_hasDerivAt p n lam ε x u t).differentiableAt]
  have hg := abs_le.mp (hsmall ε x hε0 hε1 hx u hu t).2
  have ht := hf' t
  constructor <;> linarith

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
  apply existsUnique_zero_of_bounded_identity_perturbation
    (m := (1 : ℝ) / 2) (B := B + b)
  · exact hf.add (fun t => (gaussianCorrection_hasDerivAt p n lam ε x u t).differentiableAt)
  · norm_num
  · intro t
    exact (gaussianCorrection_family_derivative_bounds hf hf' hsmall hb hε0 hε1 hx u hu t).1
  · intro t
    calc
      |f t + gaussianCorrection p n lam ε x u t - t| =
          |(f t - t) + gaussianCorrection p n lam ε x u t| := by congr 1; ring
      _ ≤ |f t - t| + |gaussianCorrection p n lam ε x u t| := abs_add_le _ _
      _ ≤ B + b := add_le_add (hidentity t) (hsmall ε x hε0 hε1 hx u hu t).1

theorem family_geometric_sum_le_two {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) (n : ℕ) :
    (∑ i : Fin n, r ^ i.val) ≤ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, Fin.val_succ, pow_succ]
    rw [← Finset.sum_mul]
    nlinarith

/-- The Cauchy–Schwarz estimate at the old root, with the paper's constant `2`. -/
theorem gaussian_family_bracket_at_old_root_le {n : ℕ} {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 4)
    (u : EuclideanSpace ℝ (Fin (n + 1))) (hu : ‖u‖ ≤ 1) :
    |ε * u 0 + ∑ i : Fin n, u i.succ * (-ε) ^ (i.val + 1)| ≤ 2 * ε := by
  let v : EuclideanSpace ℝ (Fin (n + 1)) :=
    WithLp.toLp 2 (fun i => if i = 0 then ε else (-ε) ^ i.val)
  have hvnorm : ‖v‖ ≤ 2 * ε := by
    have hterm (i : Fin n) : ((-ε) ^ (i.val + 1)) ^ 2 = ε ^ 2 * (ε ^ 2) ^ i.val := by
      rw [← pow_mul, Nat.mul_comm (i.val + 1) 2, pow_mul, neg_sq, pow_succ]
      ring
    have hs := family_geometric_sum_le_two (sq_nonneg ε) (by nlinarith : ε ^ 2 ≤ 1 / 2) n
    have hv : ‖v‖ ^ 2 = ε ^ 2 + ε ^ 2 * ∑ i : Fin n, (ε ^ 2) ^ i.val := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp only [v, Fin.sum_univ_succ, ↓reduceIte, Fin.succ_ne_zero,
        Fin.val_succ, hterm]
      rw [Finset.mul_sum]
    have hbound := mul_le_mul_of_nonneg_left hs (sq_nonneg ε)
    nlinarith [norm_nonneg v]
  have hinner := (abs_real_inner_le_norm u v).trans
    (mul_le_mul hu hvnorm (norm_nonneg v) zero_le_one)
  simpa [PiLp.inner_apply, v, Fin.sum_univ_succ, mul_comm] using hinner

/-- Testing the constant coefficient at scale one bounds the fixed multiplier itself. -/
theorem gaussianCorrectionSmall_weight_bound {p : Polynomial ℝ} {n : ℕ} {lam b : ℝ}
    (hsmall : GaussianCorrectionSmall p n lam b) (t : ℝ) :
    |lam * gaussianPolynomial p t| ≤ b := by
  let u : EuclideanSpace ℝ (Fin (n + 1)) := PiLp.single 2 0 1
  have hu : ‖u‖ ≤ 1 := by simp [u]
  have h := (hsmall 1 0 (by norm_num) le_rfl (by norm_num) u hu t).1
  rw [gaussianCorrection, gaussianCorrectionPolynomial_eval] at h
  simpa [u, gaussianPolynomial, mul_assoc] using h

theorem gaussianCorrection_at_old_root_bound {p : Polynomial ℝ} {n : ℕ}
    {lam b ε : ℝ} (hsmall : GaussianCorrectionSmall p n lam b)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 4) (a : ℝ)
    (u : EuclideanSpace ℝ (Fin (n + 1))) (hu : ‖u‖ ≤ 1) :
    |gaussianCorrection p n lam ε (a + ε) u a| ≤ 2 * b * ε := by
  have hw := gaussianCorrectionSmall_weight_bound hsmall a
  have hb0 : 0 ≤ b := (abs_nonneg _).trans hw
  have hc := gaussian_family_bracket_at_old_root_le hε0 hε u hu
  rw [gaussianCorrection, gaussianCorrectionPolynomial_eval,
    show a - (a + ε) = -ε by ring]
  calc
    |lam * (Real.exp (-(a ^ 2)) * p.eval a *
        (ε * u 0 + ∑ i : Fin n, u i.succ * (-ε) ^ (i.val + 1)))| =
        |lam * gaussianPolynomial p a| *
          |ε * u 0 + ∑ i : Fin n, u i.succ * (-ε) ^ (i.val + 1)| := by
      simp [gaussianPolynomial, abs_mul, mul_assoc]
    _ ≤ b * (2 * ε) := mul_le_mul hw hc (abs_nonneg _) hb0
    _ = 2 * b * ε := by ring

theorem family_start_in_unit_interval {a ε : ℝ} (ha : |a| ≤ 1 / 4)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 4) : |a + ε| ≤ 1 := by
  have h := abs_add_le a ε
  rw [abs_of_nonneg hε0] at h
  linarith

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
  have hx := family_start_in_unit_interval ha hε0 hε
  have hdiff : Differentiable ℝ (fun y => f y + gaussianCorrection p n lam ε (a + ε) u y) :=
    hf.add (fun t => (gaussianCorrection_hasDerivAt p n lam ε (a + ε) u t).differentiableAt)
  have hd := distance_to_zero_le_value_div (m := (1 : ℝ) / 2) hdiff (by norm_num)
    (fun t => (gaussianCorrection_family_derivative_bounds hf hf' hsmall hb hε0
      (by linarith) hx u hu t).1) hroot a
  have hg := gaussianCorrection_at_old_root_bound hsmall hε0 hε a u hu
  rw [hfa, zero_add, abs_sub_comm a α] at hd
  norm_num [div_eq_mul_inv] at hd
  linarith

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
  have hd := abs_le.mp (gaussianCorrection_root_displacement hf hf' hsmall hb ha hfa hε0 hε u hu hroot)
  have hbudget := mul_le_mul_of_nonneg_right hb hε0
  constructor <;> nlinarith

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
  classical
  have hex (u : {u : EuclideanSpace ℝ (Fin (n + 1)) // ‖u‖ ≤ 1}) :
      ∃! α, f α + gaussianCorrection p n lam ε (a + ε) u.val α = 0 :=
    gaussianCorrection_family_existsUnique_root hf hf' hidentity hsmall hb hε0
      (by linarith) (family_start_in_unit_interval ha hε0 hε) u.val u.property
  choose α hroot huniq using hex
  refine ⟨α, fun u => ⟨hroot u, huniq u, ?_, ?_⟩⟩
  · exact gaussianCorrection_root_displacement hf hf' hsmall hb ha hfa hε0 hε
      u.val u.property (hroot u)
  · exact gaussianCorrection_root_distance_bounds hf hf' hsmall hb ha hfa hε0 hε
      u.val u.property (hroot u)

/-- A continuous function nonzero at one point has a uniform positive lower bound
on a fixed neighbourhood of that point. -/
theorem exists_abs_lower_bound_near_nonzero {w : ℝ → ℝ} {a : ℝ}
    (hw : ContinuousAt w a) (hwa : w a ≠ 0) :
    ∃ δ > 0, ∀ t : ℝ, |t - a| < δ → |w a| / 2 ≤ |w t| := by
  have hpos : 0 < |w a| / 2 := by positivity
  obtain ⟨δ, hδ, hnear⟩ := Metric.continuousAt_iff.mp hw (|w a| / 2) hpos
  refine ⟨δ, hδ, fun t ht => ?_⟩
  have hdist := hnear (by simpa only [Real.dist_eq] using ht)
  rw [Real.dist_eq] at hdist
  have htriangle : |w a| ≤ |w a - w t| + |w t| := by
    simpa using abs_add_le (w a - w t) (w t)
  rw [abs_sub_comm] at htriangle
  linarith

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
  obtain ⟨δ, hδ, hnear⟩ := exists_abs_lower_bound_near_nonzero
    ((gaussianPolynomial_continuous p).const_mul lam).continuousAt hwa
  refine ⟨δ, hδ, fun ε hε0 hεδ hε u hu α hroot => hnear α ?_⟩
  have hd := gaussianCorrection_root_displacement hf hf' hsmall hb ha hfa hε0.le hε u hu hroot
  have hbudget := mul_le_mul_of_nonneg_right hb hε0.le
  nlinarith

/-- The family is continuous in its Euclidean coefficient parameter at each real point. -/
theorem gaussianCorrection_continuous_parameter (p : Polynomial ℝ) (n : ℕ)
    (lam ε x t : ℝ) :
    Continuous (fun u : EuclideanSpace ℝ (Fin (n + 1)) => gaussianCorrection p n lam ε x u t) := by
  simp_rw [gaussianCorrection, gaussianCorrectionPolynomial_eval]
  fun_prop

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
  apply continuous_roots_of_uniform_derivative_lower_bound (J := univ) convex_univ
    (m := (1 : ℝ) / 2) (by norm_num)
  · intro u
    exact (hf.add (fun t => (gaussianCorrection_hasDerivAt p n lam ε x u.val t).differentiableAt)).continuous.continuousOn
  · intro u
    exact (hf.add (fun t => (gaussianCorrection_hasDerivAt p n lam ε x u.val t).differentiableAt)).differentiableOn
  · intro u t _
    exact (gaussianCorrection_family_derivative_bounds hf hf' hsmall hb hε0 hε1 hx u.val u.property t).1
  · exact hroot
  · exact fun _ => mem_univ _
  · intro t _
    exact continuous_const.add ((gaussianCorrection_continuous_parameter p n lam ε x t).comp continuous_subtype_val)

/-- The coefficient functions whose Euclidean vector is used in the finite-scale family. -/
def gaussianCoefficientFunction (p : Polynomial ℝ) (n : ℕ) (lam ε x : ℝ)
    (i : Fin (n + 1)) (t : ℝ) : ℝ :=
  lam * gaussianPolynomial p t * (if i = 0 then ε else (t - x) ^ i.val)

theorem gaussianCoefficientFunction_differentiable (p : Polynomial ℝ) (n : ℕ)
    (lam ε x : ℝ) (i : Fin (n + 1)) :
    Differentiable ℝ (gaussianCoefficientFunction p n lam ε x i) := by
  unfold gaussianCoefficientFunction
  split_ifs <;> unfold gaussianPolynomial <;> fun_prop

theorem gaussianCorrection_eq_sum_coefficients (p : Polynomial ℝ) (n : ℕ)
    (lam ε x : ℝ) (u : EuclideanSpace ℝ (Fin (n + 1))) (t : ℝ) :
    gaussianCorrection p n lam ε x u t =
      ∑ i : Fin (n + 1), u i * gaussianCoefficientFunction p n lam ε x i t := by
  simp only [gaussianCorrection, gaussianCorrectionPolynomial, gaussianPolynomial,
    Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Finset.mul_sum,
    gaussianCoefficientFunction]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with hi
  · subst i
    simp
    ring
  · ring

/-- The derivative of each directional correction is the same directional sum of
the coefficient derivatives. -/
theorem gaussianCorrection_deriv_eq_sum_coefficients (p : Polynomial ℝ) (n : ℕ)
    (lam ε x : ℝ) (u : EuclideanSpace ℝ (Fin (n + 1))) (t : ℝ) :
    deriv (gaussianCorrection p n lam ε x u) t =
      ∑ i : Fin (n + 1), u i * deriv (gaussianCoefficientFunction p n lam ε x i) t := by
  have heq : gaussianCorrection p n lam ε x u =
      fun y => ∑ i : Fin (n + 1), u i * gaussianCoefficientFunction p n lam ε x i y :=
    funext fun y => gaussianCorrection_eq_sum_coefficients p n lam ε x u y
  rw [heq]
  exact (HasDerivAt.fun_sum (fun i _ =>
    ((gaussianCoefficientFunction_differentiable p n lam ε x i t).hasDerivAt).const_mul (u i))).deriv

/-- Euclidean duality: estimates in every unit direction bound the vector norm. -/
theorem norm_le_of_unit_inner_bounds {d : ℕ} {v : EuclideanSpace ℝ (Fin d)} {b : ℝ}
    (h : ∀ u : EuclideanSpace ℝ (Fin d), ‖u‖ ≤ 1 → |inner ℝ u v| ≤ b) : ‖v‖ ≤ b := by
  by_cases hv : v = 0
  · subst v
    simpa using h 0 (by simp)
  · have hnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hu : ‖‖v‖⁻¹ • v‖ ≤ 1 := by
      simp [norm_smul, hnorm.ne']
    have hh := h (‖v‖⁻¹ • v) hu
    rw [real_inner_smul_self_left] at hh
    have heq : ‖v‖⁻¹ * (‖v‖ * ‖v‖) = ‖v‖ := by field_simp
    simpa only [heq, abs_of_nonneg (norm_nonneg v)] using hh

/-- The exact Euclidean bound on the tuple of first derivatives of the coefficient
functions follows from the uniform directional correction bound. -/
theorem gaussianCorrection_coefficient_derivative_norm_bound {p : Polynomial ℝ} {n : ℕ}
    {lam b ε x : ℝ} (hsmall : GaussianCorrectionSmall p n lam b)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hx : |x| ≤ 1) (t : ℝ) :
    ‖WithLp.toLp 2 (fun i : Fin (n + 1) =>
      deriv (gaussianCoefficientFunction p n lam ε x i) t)‖ ≤ b := by
  apply norm_le_of_unit_inner_bounds
  intro u hu
  have h := (hsmall ε x hε0 hε1 hx u hu t).2
  rw [gaussianCorrection_deriv_eq_sum_coefficients] at h
  simpa [PiLp.inner_apply, mul_comm] using h

/-- The coordinate derivatives are the actual derivative of the Euclidean-valued
coefficient function, via the continuous linear equivalence with a finite product. -/
theorem gaussianCoefficientVector_hasDerivAt (p : Polynomial ℝ) (n : ℕ)
    (lam ε x t : ℝ) :
    HasDerivAt (fun y => WithLp.toLp 2 (fun i : Fin (n + 1) =>
      gaussianCoefficientFunction p n lam ε x i y))
      (WithLp.toLp 2 (fun i : Fin (n + 1) =>
        deriv (gaussianCoefficientFunction p n lam ε x i) t)) t := by
  have hcoords : HasDerivAt (fun y (i : Fin (n + 1)) =>
      gaussianCoefficientFunction p n lam ε x i y)
      (fun i => deriv (gaussianCoefficientFunction p n lam ε x i) t) t :=
    hasDerivAt_pi.mpr fun i => (gaussianCoefficientFunction_differentiable p n lam ε x i t).hasDerivAt
  exact ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 1) => ℝ)).symm.toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt t hcoords

/-- The vector derivative bound required by the finite-scale family, with the
Euclidean norm and the same constant as the scalar directional bounds. -/
theorem gaussianCorrection_vector_derivative_norm_bound {p : Polynomial ℝ} {n : ℕ}
    {lam b ε x : ℝ} (hsmall : GaussianCorrectionSmall p n lam b)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hx : |x| ≤ 1) (t : ℝ) :
    ‖deriv (fun y => WithLp.toLp 2 (fun i : Fin (n + 1) =>
      gaussianCoefficientFunction p n lam ε x i y)) t‖ ≤ b := by
  rw [(gaussianCoefficientVector_hasDerivAt p n lam ε x t).deriv]
  exact gaussianCorrection_coefficient_derivative_norm_bound hsmall hε0 hε1 hx t

end KungTraub
