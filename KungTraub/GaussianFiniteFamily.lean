import KungTraub.FiniteFamilyGeometry
import KungTraub.EntireFamilies

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
  rw [gaussianCorrection_eq_sum_coefficients]
  simp [PiLp.inner_apply, realPolynomialEvaluationVector, gaussianCoefficientFunction, mul_comm]

theorem gaussianCoefficientVector_lipschitz {p : Polynomial ℝ} {n : ℕ}
    {lam b ε x : ℝ} (hsmall : GaussianCorrectionSmall p n lam b)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hx : |x| ≤ 1) (s t : ℝ) :
    ‖realPolynomialEvaluationVector n ε (lam * gaussianPolynomial p s) (s - x) -
      realPolynomialEvaluationVector n ε (lam * gaussianPolynomial p t) (t - x)‖ ≤
      b * |s - t| := by
  let v : ℝ → EuclideanSpace ℝ (Fin (n + 1)) :=
    fun y => realPolynomialEvaluationVector n ε (lam * gaussianPolynomial p y) (y - x)
  have hdiff (y : ℝ) : DifferentiableAt ℝ v y :=
    (gaussianCoefficientVector_hasDerivAt p n lam ε x y).differentiableAt
  have hbound (y : ℝ) : ‖deriv v y‖ ≤ b :=
    gaussianCorrection_vector_derivative_norm_bound hsmall hε0 hε1 hx y
  simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_deriv_le
    (s := univ) (fun y _ => hdiff y) (fun y _ => hbound y) convex_univ
    (mem_univ t) (mem_univ s)

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
  classical
  obtain ⟨η, hη, hweight⟩ := gaussianCorrection_weight_uniformly_away_from_zero
    hf hf' hsmall hb ha hfa hwa
  refine ⟨min η (1 / 4), lt_min hη (by norm_num), ?_⟩
  intro ε hε hεη
  have hεquarter : ε ≤ 1 / 4 := (lt_of_lt_of_le hεη (min_le_right _ _)).le
  have hεsmall : ε < η := lt_of_lt_of_le hεη (min_le_left _ _)
  have hε1 : ε ≤ 1 := by linarith
  have hx := family_start_in_unit_interval ha hε.le hεquarter
  obtain ⟨roots, hroots⟩ := gaussianCorrection_exists_root_family hf hf' hidentity
    hsmall hb ha hfa hε.le hεquarter
  let root : EuclideanSpace ℝ (Fin (n + 1)) → ℝ :=
    fun u => if hu : ‖u‖ ≤ 1 then roots ⟨u, hu⟩ else a
  have hroot (u : EuclideanSpace ℝ (Fin (n + 1))) (hu : ‖u‖ ≤ 1) :
      root u = roots ⟨u, hu⟩ := dif_pos hu
  let F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ → ℝ :=
    fun u t => f t + gaussianCorrection p n lam ε (a + ε) u t
  have hdiff (u : EuclideanSpace ℝ (Fin (n + 1))) : Differentiable ℝ (F u) :=
    hf.add (fun t => (gaussianCorrection_hasDerivAt p n lam ε (a + ε) u t).differentiableAt)
  have hzero (u : EuclideanSpace ℝ (Fin (n + 1))) (hu : ‖u‖ ≤ 1) : F u (root u) = 0 := by
    rw [hroot u hu]
    exact (hroots ⟨u, hu⟩).1
  let D : FiniteRootFamily n ε (a + ε) (1 / 2) (3 / 2) (5 / 4)
      (|lam * gaussianPolynomial p a| / 2) b := {
    function := F
    root := root
    weight := fun t => lam * gaussianPolynomial p t
    interval := univ
    convex := convex_univ
    continuous := fun u _ => (hdiff u).continuous.continuousOn
    differentiable := fun u _ => (hdiff u).differentiableOn
    lower := fun u hu t _ =>
      (gaussianCorrection_family_derivative_bounds hf hf' hsmall hb hε.le hε1 hx u hu t).1
    upper := fun u hu t _ =>
      (gaussianCorrection_family_derivative_bounds hf hf' hsmall hb hε.le hε1 hx u hu t).2
    is_root := hzero
    root_mem := fun u _ => mem_univ (root u)
    affine := by
      intro u _ t _
      dsimp [F]
      rw [gaussianCorrection_eq_parameter_inner, gaussianCorrection_eq_parameter_inner,
        inner_zero_left, add_zero]
    root_distance := by
      intro u hu
      rw [hroot u hu, abs_sub_comm, abs_of_nonneg (by
        have h := (hroots ⟨u, hu⟩).2.2.2.1
        linarith)]
      have h := (hroots ⟨u, hu⟩).2.2.2.2
      linarith
    weight_lower := fun u hu => hweight ε hε hεsmall hεquarter u hu (root u) (hzero u hu)
    vector_lipschitz := fun s _ t _ => gaussianCoefficientVector_lipschitz hsmall hε.le hε1 hx s t
  }
  exact ⟨D, fun _ _ => rfl, rfl, rfl⟩

end KungTraub
