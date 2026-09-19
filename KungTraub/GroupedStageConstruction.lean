import KungTraub.EntireStageSequence
import KungTraub.GroupedFiniteAdversary
import KungTraub.GroupedFlattening

/-!
# Gaussian stage construction for prescribed groups

The actual grouped finite adversary supplies the next Gaussian correction
with the exact grouped product exponent. Flattening is used only to feed the
proved generic history recursion: actual outputs and derivative queries are
transferred by the exact flattening equalities.
-/

noncomputable section
open scoped BigOperators ContDiff
namespace KungTraub

theorem exists_grouped_gaussianStageChoice {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedRealAlgorithm sizes) (hk : 0 < k) (hsizes : ∀ i, 0 < sizes i)
    (P : Polynomial ℝ) (Z : Finset ℝ) (orders : ℝ → ℕ) {a b R p : ℝ}
    (hbase : ∀ t : ℝ, |(t + gaussianPolynomial P t) - t| ≤ 1 / 16 ∧
      (15 : ℝ) / 16 ≤ deriv (fun y => y + gaussianPolynomial P y) t ∧
      deriv (fun y => y + gaussianPolynomial P y) t ≤ 17 / 16)
    (ha : |a| ≤ 1 / 4) (hroot : a + gaussianPolynomial P a = 0)
    (hold : ∀ z ∈ Z, z + gaussianPolynomial P z ≠ 0)
    (hb : 0 < b) (hbsmall : b ≤ 1 / 16) (hR : 0 ≤ R)
    (hp : (groupedOrderBound sizes : ℝ) < p) (s : ℕ) :
    Nonempty (GaussianStageChoice A.flatten P Z orders a b R (groupedOrderBound sizes : ℝ) p s) := by
  let n := groupedObservationCount sizes
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
  let c := groupedFiniteScaleErrorConstant sizes (1 / 2) (3 / 2) (5 / 4) wmin b
  have hc : 0 < c := groupedFiniteScaleErrorConstant_pos sizes
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
  obtain ⟨u, hu, herror, hqueries⟩ := D.grouped_finite_adversary sizes hk hsizes
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
    error_bound := by simpa only [A.flatten_run_eq, groupedStageExponent_eq_groupedOrderBound,
      Real.rpow_natCast, hF, c, wmin, W] using herror
    amplification := hamp
    old_jets := ?_
    old_values := ?_
    new_values := ?_
  }⟩
  · intro z hz k hk
    exact pastQuery_gaussian_correction_preserves_jet
      (gaussian_stage_base_contDiff P) orders hz hk n lam ε (a + ε) u
  · exact pastQuery_gaussian_correction_preserves_nonzero orders hold n lam ε (a + ε) u
  · intro t z ord hquery hz
    rw [A.flatten_actualQuery] at hquery
    let pair := (groupSlotEquiv sizes).symm t
    have hloc : ((A.toAffine observe).actualObservations u (a + ε) pair.1 pair.2).location = some z := by
      rw [A.toAffine_actual_location_eq observe (hanswer u) hlocation (a + ε) pair.1 pair.2, hF]
      exact congrArg RealQuery.location hquery
    exact hqueries pair.1 pair.2 z hloc (hmono.injective (hnewroot.trans hz.symm))


/-- Every stage exponent above the exact grouped bound admits the concrete
Gaussian extension required by the generic history construction. -/
theorem grouped_gaussianStageExtensionAvailable {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedRealAlgorithm sizes) (hk : 0 < k) (hsizes : ∀ i, 0 < sizes i)
    (exponent : ℕ → ℝ) (hp : ∀ s, (groupedOrderBound sizes : ℝ) < exponent s) :
    GaussianStageExtensionAvailable A.flatten (groupedOrderBound sizes : ℝ) exponent := by
  intro s P Z orders a b hbase ha hroot hold hb hbsmall
  exact exists_grouped_gaussianStageChoice A hk hsizes P Z orders hbase ha hroot hold hb hbsmall
    (by positivity) (hp s) s

end KungTraub

