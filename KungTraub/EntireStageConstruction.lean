import KungTraub.EntireWitnessAssembly
import KungTraub.GaussianFiniteFamily
import KungTraub.FiniteAdversary

/-!
# Constructing the discrete entire stages

The discrete construction in Section 4 of Matthew J. Colbrook's manuscript.
The next Gaussian correction is selected using the proved finite adversary.
Its analytic bounds, actual output error, new-query avoidance and exact old
observations follow from the finite-stage estimates.
-/

noncomputable section
open scoped BigOperators ContDiff

namespace KungTraub

def gaussianUpdatedFunction (P : Polynomial ℝ) (lam : ℝ) (Q : Polynomial ℝ) (t : ℝ) : ℝ :=
  t + gaussianPolynomial P t + lam * gaussianPolynomial Q t

theorem gaussianPolynomial_C_mul (lam : ℝ) (Q : Polynomial ℝ) (t : ℝ) :
    gaussianPolynomial (Polynomial.C lam * Q) t = lam * gaussianPolynomial Q t := by
  simp [gaussianPolynomial]
  ring

theorem complexGaussianPolynomial_C_mul (lam : ℝ) (Q : Polynomial ℝ) (z : ℂ) :
    complexGaussianPolynomial (Polynomial.C lam * Q) z =
      (lam : ℂ) * complexGaussianPolynomial Q z := by
  simp [complexGaussianPolynomial]
  ring

theorem gaussianUpdatedFunction_eq_base (P : Polynomial ℝ) (lam : ℝ) (Q : Polynomial ℝ) :
    gaussianUpdatedFunction P lam Q =
      fun t => t + gaussianPolynomial (P + Polynomial.C lam * Q) t := by
  funext t
  simp [gaussianUpdatedFunction, gaussianPolynomial]
  ring

/-- The data and invariants of one correction. The exponent B is a parameter
for both scalar and grouped observations. -/
structure GaussianStageChoice {n : ℕ} (A : RealAlgorithm n) (P : Polynomial ℝ)
    (Z : Finset ℝ) (orders : ℝ → ℕ) (a b R B p : ℝ) (s : ℕ) where
  polynomial : Polynomial ℝ
  multiplier : ℝ
  epsilon : ℝ
  root : ℝ
  coefficient : ℝ
  multiplier_pos : 0 < multiplier
  epsilon_pos : 0 < epsilon
  epsilon_cap : epsilon < 1 / ((s : ℝ) + 1)
  epsilon_quarter : epsilon < 1 / 4
  coefficient_pos : 0 < coefficient
  value_bound : ∀ t, |multiplier * gaussianPolynomial polynomial t| ≤ b
  deriv_bound : ∀ t, |deriv (fun y => multiplier * gaussianPolynomial polynomial y) t| ≤ b
  disc_bound : ∀ z : ℂ, ‖z‖ ≤ R → ‖(multiplier : ℂ) * complexGaussianPolynomial polynomial z‖ ≤ b
  is_root : gaussianUpdatedFunction P multiplier polynomial root = 0
  start_lower : (3 / 4 : ℝ) * epsilon ≤ a + epsilon - root
  start_upper : a + epsilon - root ≤ (5 / 4 : ℝ) * epsilon
  error_bound : coefficient * epsilon ^ B ≤
    |A.run (gaussianUpdatedFunction P multiplier polynomial) (a + epsilon) - root|
  amplification : ((s : ℝ) + 1) * (2 * epsilon) ^ p ≤ (coefficient / 2) * epsilon ^ B
  old_jets : ∀ z ∈ Z, ∀ k : ℕ, k ≤ orders z →
    iteratedDeriv k (gaussianUpdatedFunction P multiplier polynomial) z =
      iteratedDeriv k (fun t => t + gaussianPolynomial P t) z
  old_values : ∀ z ∈ Z, gaussianUpdatedFunction P multiplier polynomial z ≠ 0
  new_values : ∀ (j : Fin n) z k,
    A.actualQuery (gaussianUpdatedFunction P multiplier polynomial) (a + epsilon) j =
      .derivative z k → gaussianUpdatedFunction P multiplier polynomial z ≠ 0

theorem GaussianStageChoice.error_pos {n : ℕ} {A : RealAlgorithm n} {P : Polynomial ℝ}
    {Z : Finset ℝ} {orders : ℝ → ℕ} {a b R B p : ℝ} {s : ℕ}
    (D : GaussianStageChoice A P Z orders a b R B p s) :
    0 < |A.run (gaussianUpdatedFunction P D.multiplier D.polynomial) (a + D.epsilon) - D.root| :=
  (mul_pos D.coefficient_pos (Real.rpow_pos_of_pos D.epsilon_pos B)).trans_le D.error_bound

theorem GaussianStageChoice.exists_next_budget {n : ℕ} {A : RealAlgorithm n}
    {P : Polynomial ℝ} {Z : Finset ℝ} {orders : ℝ → ℕ} {a b R B p : ℝ} {s : ℕ}
    (D : GaussianStageChoice A P Z orders a b R B p s) (hb : 0 < b) :
    ∃ next : ℝ, 0 < next ∧ next ≤ b / 2 ∧
      next ≤ |A.run (gaussianUpdatedFunction P D.multiplier D.polynomial)
        (a + D.epsilon) - D.root| / 32 ∧ next ≤ D.epsilon / 32 :=
  KungTraub.exists_next_budget hb D.error_pos D.epsilon_pos

/-- The finite adversary supplies a next stage for every finite Gaussian
history satisfying the analytic bounds and having nonzero values at its old nodes.
The multiplier, root-family threshold and positive error coefficient precede epsilon. -/
theorem exists_gaussianStageChoice {n : ℕ} (A : RealAlgorithm n) (hn : 0 < n)
    (P : Polynomial ℝ) (Z : Finset ℝ) (orders : ℝ → ℕ) {a b R p : ℝ}
    (hbase : ∀ t : ℝ, |(t + gaussianPolynomial P t) - t| ≤ 1 / 16 ∧
      (15 : ℝ) / 16 ≤ deriv (fun y => y + gaussianPolynomial P y) t ∧
      deriv (fun y => y + gaussianPolynomial P y) t ≤ 17 / 16)
    (ha : |a| ≤ 1 / 4) (hroot : a + gaussianPolynomial P a = 0)
    (hold : ∀ z ∈ Z, z + gaussianPolynomial P z ≠ 0)
    (hb : 0 < b) (hbsmall : b ≤ 1 / 16) (hR : 0 ≤ R)
    (hp : (orderBound n : ℝ) < p) (s : ℕ) :
    Nonempty (GaussianStageChoice A P Z orders a b R (orderBound n : ℝ) p s) := by
  let f : ℝ → ℝ := fun t => t + gaussianPolynomial P t
  let W := pastQueryPolynomial Z orders
  have hf : Differentiable ℝ f := fun t =>
    ((hasDerivAt_id t).add (gaussianPolynomial_hasDerivAt P t)).differentiableAt
  have hf' : ∀ t, (15 : ℝ) / 16 ≤ deriv f t ∧ deriv f t ≤ 17 / 16 :=
    fun t => (hbase t).2
  obtain ⟨lam, hlam, hwa, hsmall, hdisc⟩ :=
    pastQuery_exists_small_correction (f := f) (Z := Z) orders hroot hold n hR hb
  let wmin := |lam * gaussianPolynomial W a| / 2
  have hwmin : 0 < wmin := div_pos (abs_pos.mpr hwa) (by norm_num)
  let c := finiteScaleErrorConstant n (1 / 2) (3 / 2) (5 / 4) wmin b
  have hc : 0 < c := finiteScaleErrorConstant_pos n
    (by norm_num) (by norm_num) (by norm_num) hwmin hb.le
  obtain ⟨η, hη, hfamily⟩ := gaussianCorrection_exists_finiteRootFamily hf hf'
    (fun t => (hbase t).1) hsmall hbsmall ha hroot hwa
  obtain ⟨ε, hε, hεη, hεcap, hεquarter, hamp⟩ := exists_stage_scale hp hc hη s
  have hε1 : ε ≤ 1 := by linarith
  have hx := family_start_in_unit_interval ha hε.le hεquarter.le
  obtain ⟨D, hfunction, _, _⟩ := hfamily ε hε hεη
  let F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ → ℝ :=
    fun u t => t + gaussianPolynomial P t + gaussianCorrection W n lam ε (a + ε) u t
  let observe := derivativeAffineObservation f (gaussianCoefficientFunction W n lam ε (a + ε))
  have hanswer (u : EuclideanSpace ℝ (Fin (n + 1))) (q : RealQuery) :
      (observe q).answer u = q.answer (F u) :=
    gaussian_stage_derivativeAffineObservation_answer P W n lam ε (a + ε) q u
  have hlocation (q : RealQuery) : (observe q).location = q.location :=
    derivativeAffineObservation_location f _ q
  have hrun (u : EuclideanSpace ℝ (Fin (n + 1))) :
      (A.toAffine observe).run u (a + ε) = A.run (F u) (a + ε) :=
    A.toAffine_run_eq observe (hanswer u) (a + ε)
  obtain ⟨u, hu, herror, hqueries⟩ := D.finite_adversary hn
    (by norm_num) (by norm_num) (by norm_num) hwmin hb.le hε hε1
    (by linarith : (5 : ℝ) / 4 * ε ≤ 1 / 2) (A.toAffine observe)
  rw [hrun u] at herror
  let Q := gaussianCorrectionPolynomial W n ε (a + ε) u
  have hF : F u = gaussianUpdatedFunction P lam Q := rfl
  have hnewroot : F u (D.root u) = 0 := by
    simpa only [hfunction] using D.is_root u hu
  have hdist := gaussianCorrection_root_distance_bounds hf hf' hsmall hbsmall ha hroot
    hε.le hεquarter.le u hu hnewroot
  have hnewlower : ∀ t, (1 : ℝ) / 2 ≤ deriv (F u) t :=
    fun t => (gaussianCorrection_family_derivative_bounds hf hf' hsmall hbsmall
      hε.le hε1 hx u hu t).1
  have hmono : StrictMono (F u) := strictMono_of_uniform_derivative_lower_bound
    (by norm_num : (0 : ℝ) < 1 / 2) hnewlower
  refine ⟨{
    polynomial := Q
    multiplier := lam
    epsilon := ε
    root := D.root u
    coefficient := c
    multiplier_pos := hlam
    epsilon_pos := hε
    epsilon_cap := hεcap
    epsilon_quarter := hεquarter
    coefficient_pos := hc
    value_bound := fun t => (hsmall ε (a + ε) hε.le hε1 hx u hu t).1
    deriv_bound := fun t => (hsmall ε (a + ε) hε.le hε1 hx u hu t).2
    disc_bound := fun z hz => hdisc ε (a + ε) hε.le hε1 hx u hu z hz
    is_root := hnewroot
    start_lower := by linarith [hdist.1]
    start_upper := by linarith [hdist.2]
    error_bound := by simpa only [Real.rpow_natCast, hF, c, wmin, W] using herror
    amplification := hamp
    old_jets := ?_
    old_values := ?_
    new_values := ?_
  }⟩
  · intro z hz k hk
    exact pastQuery_gaussian_correction_preserves_jet
      (gaussian_stage_base_contDiff P) orders hz hk n lam ε (a + ε) u
  · exact pastQuery_gaussian_correction_preserves_nonzero orders hold n lam ε (a + ε) u
  · intro j z k hquery hz
    have hloc : ((A.toAffine observe).actualObservation u (a + ε) j).location = some z := by
      rw [A.toAffine_actual_location_eq observe (hanswer u) hlocation (a + ε) j, hF, hquery]
      rfl
    exact hqueries j z hloc (hmono.injective (hnewroot.trans hz.symm))

end KungTraub
