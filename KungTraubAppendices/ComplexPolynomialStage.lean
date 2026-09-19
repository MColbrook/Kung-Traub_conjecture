import KungTraubAppendices.ComplexCorrectionGeometry
import KungTraubAppendices.ComplexPolynomialFamilyRoots
import KungTraubAppendices.ComplexCorrectionObservations
import KungTraubAppendices.ComplexPreservingFactor
import KungTraubAppendices.ComplexFiniteAdversary
import KungTraub.DiagonalEstimates

/-!
# Complex polynomial families and one adversarial stage

Near-identity polynomial bounds, the preserving factor and the finite adversary
give one stage. The multiplier, common family threshold and positive error
constant are chosen before epsilon. Estimates hold on the closed unit spatial
disc and the complex Euclidean unit parameter ball.

The construction follows `KungTraub.GaussianFiniteFamily` and
`KungTraub.EntireStageConstruction`, using their real scale-selection lemma.
Root existence follows from the contraction argument in `ComplexRoots`.
-/

noncomputable section

open Polynomial Set KungTraub
open scoped BigOperators

namespace KungTraubAppendices

/-- A fixed nonzero continuous complex weight is uniformly bounded away from
zero in one neighbourhood, independently of the eventual family parameter. -/
theorem exists_complex_weight_lower_bound {w : ℂ → ℂ} {a : ℂ}
    (hw : ContinuousAt w a) (hwa : w a ≠ 0) :
    ∃ δ > 0, ∀ t : ℂ, ‖t - a‖ < δ → ‖w a‖ / 2 ≤ ‖w t‖ := by
  have hpos : 0 < ‖w a‖ / 2 := div_pos (norm_pos_iff.mpr hwa) (by norm_num)
  obtain ⟨δ, hδ, hnear⟩ := Metric.continuousAt_iff.mp hw (‖w a‖ / 2) hpos
  refine ⟨δ, hδ, fun t ht => ?_⟩
  have hdist := hnear (by simpa only [dist_eq_norm] using ht)
  rw [dist_eq_norm] at hdist
  have htriangle : ‖w a‖ ≤ ‖w t - w a‖ + ‖w t‖ := by
    have h := norm_sub_le (w t) (w t - w a)
    simpa only [sub_sub_cancel, add_comm] using h
  linarith

/-- The actual polynomial family has a common scale threshold, with
constants fixed before epsilon. -/
theorem complexPolynomialCorrection_exists_finiteRootFamily
    {f p : Polynomial ℂ} {n : ℕ} {lam b B : ℝ} {a : ℂ}
    (hf : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖f.eval z - z‖ ≤ B ∧ ‖f.derivative.eval z - 1‖ ≤ B)
    (hsmall : ComplexCorrectionSmall p n lam b) (hb : 0 ≤ b) (hbsmall : b ≤ 1 / 32)
    (hbudget : B + b ≤ 1 / 16) (ha : ‖a‖ ≤ 1 / 16) (hfa : f.eval a = 0)
    (hwa : (lam : ℂ) * p.eval a ≠ 0) :
    ∃ η > 0, ∀ ε : ℝ, 0 < ε → ε < η →
      ∃ D : ComplexFiniteRootFamily n ε (a + (ε : ℂ)) (1 / 2) (3 / 2) (5 / 4)
          (‖(lam : ℂ) * p.eval a‖ / 2) b,
        (∀ u z, D.function u z =
          (f + C (lam : ℂ) * complexCorrectionPolynomial p n ε (a + (ε : ℂ)) u).eval z) ∧
        D.weight = (fun z => (lam : ℂ) * p.eval z) ∧
        D.domain = Metric.closedBall (0 : ℂ) 1 ∧
        ∀ u, ‖u‖ ≤ 1 →
          ‖D.root u‖ ≤ (1 / 16 : ℝ) ∧
          SimpleComplexRoot (D.function u) (D.root u) ∧
          (∀ z : ℂ, ‖z‖ ≤ 1 → D.function u z = 0 → z = D.root u) ∧
          ‖D.root u - a‖ ≤ 4 * b * ε ∧
          (3 / 4 : ℝ) * ε ≤ ‖a + (ε : ℂ) - D.root u‖ := by
  classical
  have hw : ContinuousAt (fun z : ℂ => (lam : ℂ) * p.eval z) a := by fun_prop
  obtain ⟨δ, hδ, hweight⟩ := exists_complex_weight_lower_bound hw hwa
  refine ⟨min δ (1 / 4), lt_min hδ (by norm_num), ?_⟩
  intro ε hε hεη
  have hεδ : ε < δ := hεη.trans_le (min_le_left _ _)
  have hεquarter : ε ≤ 1 / 4 := (hεη.trans_le (min_le_right _ _)).le
  have hεone : ε ≤ 1 := by linarith
  have hεnorm : ‖(ε : ℂ)‖ = ε := by
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
  let x : ℂ := a + (ε : ℂ)
  have hx : ‖x‖ ≤ 1 := by
    have h := norm_add_le a (ε : ℂ)
    rw [hεnorm] at h
    dsimp only [x]
    linarith
  have haone : ‖a‖ ≤ 1 := ha.trans (by norm_num)
  let q : EuclideanSpace ℂ (Fin (n + 1)) → Polynomial ℂ :=
    fun u => C (lam : ℂ) * complexCorrectionPolynomial p n ε x u
  have hq (u : EuclideanSpace ℂ (Fin (n + 1))) (hu : ‖u‖ ≤ 1) :
      ComplexPolynomialDiscBound (q u) 1 b := hsmall ε hε.le hεone x hx u hu
  obtain ⟨root, hroot⟩ := exists_complexPolynomialCorrectionFamily_roots f p n lam ε x hf hq hbudget
  have hrootnorm (u : EuclideanSpace ℂ (Fin (n + 1))) (hu : ‖u‖ ≤ 1) :
      ‖root u‖ ≤ (1 / 16 : ℝ) := (hroot u hu).1
  have hzero (u : EuclideanSpace ℂ (Fin (n + 1))) (hu : ‖u‖ ≤ 1) :
      (f + q u).eval (root u) = 0 := (hroot u hu).2.1.1
  have hshift (u : EuclideanSpace ℂ (Fin (n + 1))) (hu : ‖u‖ ≤ 1) :
      ‖root u - a‖ ≤ 4 * b * ε := by
    have hspatial := (complexPolynomial_add_spatial_bounds f (q u) hf (hq u hu) hbudget
      ((hrootnorm u hu).trans (by norm_num)) haone).1
    rw [hzero u hu, Polynomial.eval_add, hfa, zero_add, zero_sub, norm_neg] at hspatial
    have hold := complexCorrectionSmall_at_old_root hsmall hε.le hεquarter a haone u hu
    change ‖(q u).eval a‖ ≤ 2 * b * ε at hold
    linarith
  have hshiftquarter (u : EuclideanSpace ℂ (Fin (n + 1))) (hu : ‖u‖ ≤ 1) :
      ‖root u - a‖ ≤ ε / 4 := by
    have hbε := mul_le_mul_of_nonneg_right hbsmall hε.le
    linarith [hshift u hu]
  have hstart (u : EuclideanSpace ℂ (Fin (n + 1))) (hu : ‖u‖ ≤ 1) :
      (3 / 4 : ℝ) * ε ≤ ‖x - root u‖ ∧ ‖root u - x‖ ≤ (5 / 4 : ℝ) * ε := by
    have hxa : ‖x - a‖ = ε := by simpa only [x, add_sub_cancel_left] using hεnorm
    have htriangle := norm_sub_le (x - root u) (a - root u)
    have hupper := norm_add_le (root u - a) (a - x)
    have hnorm : ‖a - root u‖ = ‖root u - a‖ := norm_sub_rev _ _
    have hax : ‖a - x‖ = ε := by rw [norm_sub_rev, hxa]
    have heq : x - root u - (a - root u) = x - a := by ring
    have heq' : (root u - a) + (a - x) = root u - x := by ring
    rw [heq, hxa, hnorm] at htriangle
    rw [heq', hax] at hupper
    constructor <;> linarith [hshiftquarter u hu]
  have hweightroot (u : EuclideanSpace ℂ (Fin (n + 1))) (hu : ‖u‖ ≤ 1) :
      ‖(lam : ℂ) * p.eval a‖ / 2 ≤ ‖(lam : ℂ) * p.eval (root u)‖ := by
    apply hweight
    exact lt_of_le_of_lt (hshiftquarter u hu) (by linarith)
  have hvector (u : EuclideanSpace ℂ (Fin (n + 1))) (hu : ‖u‖ ≤ 1) :
      ‖complexPolynomialEvaluationVector n ε ((lam : ℂ) * p.eval (root u)) (root u - x)‖ ≤ 1 := by
    have hd := (hstart u hu).2
    have hh : ‖root u - x‖ ≤ 1 / 2 := by linarith
    have hwbound := complexCorrectionSmall_weight_bound hsmall (root u)
      ((hrootnorm u hu).trans (by norm_num))
    calc
      _ ≤ ‖(lam : ℂ) * p.eval (root u)‖ * (ε + 2 * ‖root u - x‖) :=
        complexPolynomialEvaluationVector_norm_le n hε.le _ _ hh
      _ ≤ b * 1 := mul_le_mul hwbound (by linarith) (by positivity) hb
      _ ≤ 1 := by linarith
  let D : ComplexFiniteRootFamily n ε x (1 / 2) (3 / 2) (5 / 4)
      (‖(lam : ℂ) * p.eval a‖ / 2) b := {
    function := fun u z => (f + q u).eval z
    root := root
    weight := fun z => (lam : ℂ) * p.eval z
    domain := Metric.closedBall (0 : ℂ) 1
    lower := by
      intro u hu z hz t ht
      exact (complexPolynomial_add_spatial_bounds f (q u) hf (hq u hu) hbudget
        (by simpa using hz) (by simpa using ht)).1
    upper := by
      intro u hu z hz t ht
      exact (complexPolynomial_add_spatial_bounds f (q u) hf (hq u hu) hbudget
        (by simpa using hz) (by simpa using ht)).2
    is_root := hzero
    root_mem := fun u hu => by simpa using (hrootnorm u hu).trans (by norm_num : (1 / 16 : ℝ) ≤ 1)
    affine := by
      intro u hu t ht
      simp only [Polynomial.eval_add]
      rw [show (q u).eval t = complexBilinearDot u
          (complexPolynomialEvaluationVector n ε ((lam : ℂ) * p.eval t) (t - x)) from
        scaled_complexCorrectionPolynomial_eval_bilinear p n lam ε x t u]
      have hqzero : (q 0).eval t = 0 := by
        rw [show (q 0).eval t = complexBilinearDot 0
            (complexPolynomialEvaluationVector n ε ((lam : ℂ) * p.eval t) (t - x)) from
          scaled_complexCorrectionPolynomial_eval_bilinear p n lam ε x t 0]
        simp [complexBilinearDot]
      rw [hqzero, add_zero]
    root_distance := fun u hu => (hstart u hu).2
    weight_lower := hweightroot
    vector_lipschitz := by
      intro z hz t ht
      exact complexCorrectionSmall_vector_lipschitz hsmall hb hε.le hεone hx
        (by simpa using hz) (by simpa using ht)
    geometric_containment := by
      intro u hu t ht
      have hdist : ‖t - root u‖ ≤ (1 / 12 : ℝ) := by
        have h := Metric.mem_closedBall.mp ht
        rw [dist_eq_norm, complexInitialRadius_concrete hb hbsmall] at h
        have hv := hvector u hu
        norm_num at h
        linarith
      have htriangle := norm_add_le (t - root u) (root u)
      rw [sub_add_cancel] at htriangle
      have htone : ‖t‖ ≤ 1 := by linarith [hrootnorm u hu]
      simpa using htone
  }
  refine ⟨D, fun _ _ => rfl, rfl, rfl, ?_⟩
  intro u hu
  exact ⟨hrootnorm u hu, (hroot u hu).2.1, (hroot u hu).2.2,
    hshift u hu, (hstart u hu).1⟩

/-- The selected correction absorbs the positive real multiplier into one
polynomial. Saved derivative jets are preserved at all complex locations;
nonzero values are required and retained only inside the closed unit disc. -/
structure ComplexPolynomialStageChoice {n : ℕ} (A : ComplexAlgorithm n)
    (f : Polynomial ℂ) (Q : Finset ComplexQuery) (a : ℂ) (b R B p : ℝ) (s : ℕ) where
  correction : Polynomial ℂ
  epsilon : ℝ
  root : ℂ
  coefficient : ℝ
  epsilon_pos : 0 < epsilon
  epsilon_cap : epsilon < 1 / ((s : ℝ) + 1)
  epsilon_quarter : epsilon < 1 / 4
  coefficient_pos : 0 < coefficient
  preserving_factor : complexPreservingFactor Q ∣ correction
  disc_bound : ComplexPolynomialDiscBound correction R (b / 2)
  sup_sum_bound :
    sSup ((fun z : ℂ => ‖correction.eval z‖) '' Metric.closedBall (0 : ℂ) R) +
      sSup ((fun z : ℂ => ‖deriv (fun t => correction.eval t) z‖) '' Metric.closedBall (0 : ℂ) 1) ≤ b
  root_bound : ‖root‖ ≤ (1 / 16 : ℝ)
  simple_root : SimpleComplexRoot (fun z => (f + correction).eval z) root
  unique_root : ∀ z : ℂ, ‖z‖ ≤ 1 → (f + correction).eval z = 0 → z = root
  root_shift : ‖root - a‖ ≤ 4 * b * epsilon
  start_lower : (3 / 4 : ℝ) * epsilon ≤ ‖a + (epsilon : ℂ) - root‖
  start_upper : ‖a + (epsilon : ℂ) - root‖ ≤ (5 / 4 : ℝ) * epsilon
  error_bound : coefficient * epsilon ^ B ≤
    ‖A.run (fun z => (f + correction).eval z) (a + (epsilon : ℂ)) - root‖
  amplification : ((s : ℝ) + 1) * (2 * epsilon) ^ p ≤ (coefficient / 2) * epsilon ^ B
  old_jets : ∀ z k, ComplexQuery.derivative z k ∈ Q →
    iteratedDeriv k (fun t => (f + correction).eval t) z = iteratedDeriv k (fun t => f.eval t) z
  old_values : ∀ z ∈ complexQueryNodes Q, ‖z‖ ≤ 1 → (f + correction).eval z ≠ 0
  new_root_avoidance : ∀ (j : Fin n) z k,
    A.actualQuery (fun t => (f + correction).eval t) (a + (epsilon : ℂ)) j =
      .derivative z k → root ≠ z
  new_values : ∀ (j : Fin n) z k,
    A.actualQuery (fun t => (f + correction).eval t) (a + (epsilon : ℂ)) j =
      .derivative z k → ‖z‖ ≤ 1 → (f + correction).eval z ≠ 0

/-- Every actual finite polynomial history with the budget margin extends
by a stage. The common threshold and error constant do not depend on epsilon. -/
theorem exists_complexPolynomialStageChoice {n : ℕ} (A : ComplexAlgorithm n) (hn : 0 < n)
    (f : Polynomial ℂ) (Q : Finset ComplexQuery) {a : ℂ} {b R B p : ℝ}
    (hf : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖f.eval z - z‖ ≤ B ∧ ‖f.derivative.eval z - 1‖ ≤ B)
    (ha : ‖a‖ ≤ 1 / 16) (hroot : f.eval a = 0)
    (hold : ∀ z ∈ complexQueryNodes Q, ‖z‖ ≤ 1 → f.eval z ≠ 0)
    (hb : 0 < b) (hbsmall : b ≤ 1 / 32) (hbudget : B + b ≤ 1 / 16)
    (hR : 1 ≤ R) (hp : (orderBound n : ℝ) < p) (s : ℕ) :
    Nonempty (ComplexPolynomialStageChoice A f Q a b R (orderBound n : ℝ) p s) := by
  classical
  let W := complexPreservingFactor Q
  have havoid : ∀ z ∈ complexQueryNodes Q, z ≠ a := by
    intro z hz hza
    subst z
    exact hold a hz (ha.trans (by norm_num)) hroot
  obtain ⟨lam, hlam, hbound⟩ := complexCorrectionPolynomial_exists_small_scaling W n R hb
  have hsmall : ComplexCorrectionSmall W n lam b := by
    intro ε hε0 hε1 x hx u hu
    have h := hbound ε hε0 hε1 x hx u hu
    exact ⟨fun z hz => (h.1 z (hz.trans hR)).trans (by linarith),
      fun z hz => (h.2 z hz).trans (by linarith)⟩
  have hwa : (lam : ℂ) * W.eval a ≠ 0 :=
    complexPreservingFactor_scaled_eval_ne_zero hlam havoid
  let wmin := ‖(lam : ℂ) * W.eval a‖ / 2
  have hwmin : 0 < wmin := div_pos (norm_pos_iff.mpr hwa) (by norm_num)
  let c := complexFiniteScaleErrorConstant n (1 / 2) (3 / 2) (5 / 4) wmin b
  have hc : 0 < c := complexFiniteScaleErrorConstant_pos n
    (by norm_num) (by norm_num) (by norm_num) hwmin hb.le
  obtain ⟨η, hη, hfamily⟩ := complexPolynomialCorrection_exists_finiteRootFamily
    hf hsmall hb.le hbsmall hbudget ha hroot hwa
  obtain ⟨ε, hε, hεη, hεcap, hεquarter, hamp⟩ := exists_stage_scale hp hc hη s
  have hεone : ε ≤ 1 := by linarith
  let x : ℂ := a + (ε : ℂ)
  have hx : ‖x‖ ≤ 1 := by
    have h := norm_add_le a (ε : ℂ)
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε] at h
    dsimp only [x]
    linarith
  obtain ⟨D, hfunction, _, _, hroots⟩ := hfamily ε hε hεη
  let observe := complexDerivativeAffineObservation (fun z => f.eval z)
    (fun i z => (complexCorrectionPolynomialBasis W n lam ε x i).eval z)
  obtain ⟨u, hu, herror, hqueries⟩ := D.finite_adversary hn
    (by norm_num) (by norm_num) (by norm_num) hwmin hb.le hε hεone
    (by linarith : (5 : ℝ) / 4 * ε ≤ 1 / 2) (A.toAffine observe)
  have hrun := A.complexCorrectionFamily_run f W n lam ε x x u
  change (A.toAffine observe).run u x = _ at hrun
  rw [hrun] at herror
  let q := C (lam : ℂ) * complexCorrectionPolynomial W n ε x u
  have hq : ComplexPolynomialDiscBound q R (b / 2) := hbound ε hε.le hεone x hx u hu
  have hfun : D.function u = (fun z => (f + q).eval z) := funext (hfunction u)
  have hsimple : SimpleComplexRoot (fun z => (f + q).eval z) (D.root u) := by
    simpa only [hfun] using (hroots u hu).2.1
  have hunique : ∀ z : ℂ, ‖z‖ ≤ 1 → (f + q).eval z = 0 → z = D.root u := by
    simpa only [hfun] using (hroots u hu).2.2.1
  have hnewavoid : ∀ (j : Fin n) z k,
      A.actualQuery (fun t => (f + q).eval t) x j = .derivative z k → D.root u ≠ z := by
    intro j z k hquery
    apply hqueries j z
    have hloc := A.complexCorrectionFamily_actual_location f W n lam ε x x u j
    change ((A.toAffine observe).actualObservation u x j).location = _ at hloc
    rw [hloc, hquery]
    rfl
  refine ⟨{
    correction := q
    epsilon := ε
    root := D.root u
    coefficient := c
    epsilon_pos := hε
    epsilon_cap := hεcap
    epsilon_quarter := hεquarter
    coefficient_pos := hc
    preserving_factor := scaled_complexCorrectionPolynomial_dvd W n ε lam x u
    disc_bound := hq
    sup_sum_bound := ?_
    root_bound := (hroots u hu).1
    simple_root := hsimple
    unique_root := hunique
    root_shift := (hroots u hu).2.2.2.1
    start_lower := (hroots u hu).2.2.2.2
    start_upper := by simpa only [norm_sub_rev] using D.root_distance u hu
    error_bound := by simpa only [Real.rpow_natCast, c, wmin, q, x] using herror
    amplification := hamp
    old_jets := ?_
    old_values := ?_
    new_root_avoidance := hnewavoid
    new_values := ?_
  }⟩
  · have hneR : (Metric.closedBall (0 : ℂ) R).Nonempty := ⟨0, by simp; linarith⟩
    have hne1 : (Metric.closedBall (0 : ℂ) 1).Nonempty := ⟨0, by simp⟩
    have hv : sSup ((fun z : ℂ => ‖q.eval z‖) '' Metric.closedBall (0 : ℂ) R) ≤ b / 2 := by
      apply csSup_le (hneR.image _)
      rintro v ⟨z, hz, rfl⟩
      exact hq.1 z (by simpa using hz)
    have hd : sSup ((fun z : ℂ => ‖deriv (fun t => q.eval t) z‖) ''
        Metric.closedBall (0 : ℂ) 1) ≤ b / 2 := by
      apply csSup_le (hne1.image _)
      rintro v ⟨z, hz, rfl⟩
      change ‖deriv (fun t => q.eval t) z‖ ≤ b / 2
      rw [q.deriv]
      exact hq.2 z (by simpa using hz)
    linarith
  · intro z k hquery
    have hfcont : ContDiffAt ℂ k (fun t => f.eval t) z :=
      (AnalyticOnNhd.eval_polynomial f z (mem_univ z)).contDiffAt
    have hdiv : (X - C z) ^ (k + 1) ∣ W := complexPreservingFactor_query_dvd hquery
    have h := complexCorrectionPolynomial_preserves_jet hfcont hdiv le_rfl n ε lam x u
    simpa only [Polynomial.eval_add] using h
  · intro z hz hzone
    have hzdiv := complexPreservingFactor_factor_dvd hz
    have hzjet := scaled_complexCorrectionPolynomial_jet_zero hzdiv (Nat.zero_le _) n ε lam x u
    have hqzero : q.eval z = 0 := by simpa only [iteratedDeriv_zero] using hzjet
    simpa only [Polynomial.eval_add, hqzero, add_zero] using hold z hz hzone
  · intro j z k hquery hzone hzero
    exact hnewavoid j z k hquery (hunique z hzone hzero).symm

/-- The stage error is strictly positive, so the next geometric budget can also
satisfy the exact positive error and scale caps. -/
theorem ComplexPolynomialStageChoice.error_pos {n : ℕ} {A : ComplexAlgorithm n}
    {f : Polynomial ℂ} {Q : Finset ComplexQuery} {a : ℂ} {b R B p : ℝ} {s : ℕ}
    (D : ComplexPolynomialStageChoice A f Q a b R B p s) :
    0 < ‖A.run (fun z => (f + D.correction).eval z) (a + (D.epsilon : ℂ)) - D.root‖ :=
  (mul_pos D.coefficient_pos (Real.rpow_pos_of_pos D.epsilon_pos B)).trans_le D.error_bound

/-- The exact budget extension follows from the derived stage error. -/
theorem ComplexPolynomialStageChoice.exists_next_budget {n : ℕ} {A : ComplexAlgorithm n}
    {f : Polynomial ℂ} {Q : Finset ComplexQuery} {a : ℂ} {b R B p : ℝ} {s : ℕ}
    (D : ComplexPolynomialStageChoice A f Q a b R B p s) (hb : 0 < b) :
    ∃ next : ℝ, 0 < next ∧ next ≤ b / 2 ∧
      next ≤ ‖A.run (fun z => (f + D.correction).eval z) (a + (D.epsilon : ℂ)) - D.root‖ / 32 ∧
      next ≤ D.epsilon / 32 :=
  KungTraub.exists_next_budget hb D.error_pos D.epsilon_pos

end KungTraubAppendices
