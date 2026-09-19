import KungTraub.FiniteFamilyGeometry
import KungTraub.FiniteStageConstants
import KungTraub.AdaptiveForbiddenSets
import KungTraub.AffinePolynomialSensitivity

/-!
# The finite-scale adaptive adversary

The induction constructs actual parameter balls. Their invariants contain the
proved polynomial forbidden sets, and the sensitivity estimate is obtained from
their avoidance. All constants below depend only on the degree and analytic
family bounds, before the algorithm, scale and transcript are chosen.
-/

noncomputable section

namespace KungTraub

def finiteScaleContraction (n : ℕ) (m M K : ℝ) : ℝ :=
  adversaryRadiusFactor m M (1 + K / (2 * m)) (forbiddenWronskianCountBound n)

def finiteScaleErrorConstant (n : ℕ) (m M R wmin K : ℝ) : ℝ :=
  let θ := finiteScaleContraction n m M K
  finiteStageRadius θ n *
    (finiteStageState n (forbiddenWronskianCountBound n) M R wmin θ n).2 / (2 * M)

theorem finiteScaleContraction_pos (n : ℕ) {m M K : ℝ}
    (hm : 0 < m) (hM : 0 < M) (hK : 0 ≤ K) : 0 < finiteScaleContraction n m M K :=
  adversaryRadiusFactor_pos hm hM (by positivity)

theorem finiteScaleErrorConstant_pos (n : ℕ) {m M R wmin K : ℝ}
    (hm : 0 < m) (hM : 0 < M) (hR : 0 < R) (hwmin : 0 < wmin) (hK : 0 ≤ K) :
    0 < finiteScaleErrorConstant n m M R wmin K :=
  finiteStage_final_error_constant_pos n _ hM hR hwmin (finiteScaleContraction_pos n hm hM hK)

theorem FiniteRootFamily.initial_sensitivity_at {n : ℕ} {ε x m M R wmin K : ℝ}
    (D : FiniteRootFamily n ε x m M R wmin K)
    (A : AffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) n)
    (u : EuclideanSpace ℝ (Fin (n + 1))) (hu : ‖u‖ ≤ 1) (hε : 0 ≤ ε) :
    wmin * ε ≤ ‖(A.direction u x 0).starProjection (D.vector (D.root u))‖ := by
  have hw := D.weight_lower u hu
  have hcoord := PiLp.norm_apply_le (D.vector (D.root u)) (0 : Fin (n + 1))
  have heval : ‖D.vector (D.root u) (0 : Fin (n + 1))‖ = |D.weight (D.root u)| * ε := by
    simp [FiniteRootFamily.vector, realPolynomialEvaluationVector, abs_of_nonneg hε]
  rw [heval] at hcoord
  have hdir : A.direction u x 0 = ⊤ := scalarPrefixKernel_zero _
  rw [hdir, Submodule.starProjection_eq_self_iff.mpr
    (show D.vector (D.root u) ∈ (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin (n + 1)))) by trivial)]
  exact (mul_le_mul_of_nonneg_right hw hε).trans hcoord

theorem FiniteRootFamily.finite_adversary {n : ℕ} (_hn : 0 < n)
    {ε x m M R wmin K : ℝ} (D : FiniteRootFamily n ε x m M R wmin K)
    (hm : 0 < m) (hM : 0 < M) (hR : 0 < R) (hwmin : 0 < wmin) (hK : 0 ≤ K)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hhalf : R * ε ≤ 1 / 2)
    (A : AffineAlgorithm (EuclideanSpace ℝ (Fin (n + 1))) n) :
    ∃ u : EuclideanSpace ℝ (Fin (n + 1)), ‖u‖ ≤ 1 ∧
      finiteScaleErrorConstant n m M R wmin K * ε ^ orderBound n ≤ |A.run u x - D.root u| ∧
      ∀ i : Fin n, ∀ z : ℝ, (A.actualObservation u x i).location = some z → D.root u ≠ z := by
  let H := forbiddenWronskianCountBound n
  let θ := finiteScaleContraction n m M K
  let r := finiteStageRadius θ
  let coeff := fun j => (finiteStageState n H M R wmin θ j).2
  let γ := finiteStageGamma n H M R wmin θ
  have hθ : 0 < θ := finiteScaleContraction_pos n hm hM hK
  have hθhalf : θ ≤ 1 / 2 := adversaryRadiusFactor_le_half _ _ _ _
  have hr (j : ℕ) : 0 < r j := finiteStageRadius_pos hθ j
  have hr1 (j : ℕ) : r j ≤ 1 :=
    (finiteStageRadius_le_half hθ.le (by linarith : θ ≤ 1) j).trans (by norm_num)
  have hc (j : ℕ) : 0 < coeff j := (finiteStageState_pos n H hM hR hwmin hθ j).2
  have hγ (j : ℕ) : 0 < γ j := finiteStageGamma_pos n H hM hR hwmin hθ j
  have hcformula (j : ℕ) : coeff (j + 1) =
      wmin * sensitivityPolynomialConstant n γ (j + 1) / (2 * R + 2) := by
    change (finiteStageState n H M R wmin θ (j + 1)).2 = _
    rw [finiteStageState_A_succ, finiteStageState_c_eq_product]
  let Good (j : ℕ) (center : EuclideanSpace ℝ (Fin (n + 1))) : Prop :=
    ∀ u ∈ parameterBall center (A.direction center x j) (r j),
      ‖u‖ ≤ 1 ∧
      coeff j * ε ^ orderBound j ≤ ‖(A.direction u x j).starProjection (D.vector (D.root u))‖ ∧
      ∀ i < j, ∀ z ∈ A.forbiddenSet u x ε i, γ i * ε ^ orderBound i ≤ ‖(D.root u : ℂ) - z‖
  have hsensitivity (j : ℕ) (hj : 0 < j) (hjn : j ≤ n)
      (u : EuclideanSpace ℝ (Fin (n + 1))) (hu : ‖u‖ ≤ 1)
      (havoid : ∀ i < j, ∀ z ∈ A.forbiddenSet u x ε i,
        γ i * ε ^ orderBound i ≤ ‖(D.root u : ℂ) - z‖) :
      (wmin * sensitivityPolynomialConstant n γ j / (2 * R + 2)) * ε ^ orderBound j ≤
        ‖(A.direction u x j).starProjection (D.vector (D.root u))‖ := by
    rw [A.direction_eq_polynomial_kernel u x hε.ne' j]
    exact real_kernel_projected_sensitivity_lower_bound hj hjn (A.polynomialObservation u x ε)
      (D.root u) x γ (fun i _ => hγ i) hε hε1 hR hwmin (D.weight_lower u hu)
      (D.root_distance u hu) hhalf (A.complexQueryLocation u x) havoid
  have hex (j : ℕ) (hjn : j ≤ n) : ∃ center, Good j center := by
    induction j with
    | zero =>
      refine ⟨0, ?_⟩
      intro u hu
      have hu' : ‖u‖ ≤ 1 / 2 := by
        simpa only [sub_zero, r, finiteStageRadius_zero] using hu.2
      have hu1 : ‖u‖ ≤ 1 := hu'.trans (by norm_num)
      refine ⟨hu1, ?_, ?_⟩
      · simpa only [coeff, finiteStageState, orderBound_zero, pow_one] using
          D.initial_sensitivity_at A u hu1 hε.le
      · intro i hi
        omega
    | succ j ih =>
      have hj : j < n := by omega
      obtain ⟨center, hcenter⟩ := ih (Nat.le_of_lt hj)
      have hcenter_mem := parameterBall_center center (A.direction center x j) (hr j).le
      have hbound := (hcenter center hcenter_mem).2.1
      let a := ‖(A.direction center x j).starProjection (D.vector (D.root center))‖
      have ha : 0 < a := (mul_pos (hc j) (pow_pos hε _)).trans_le hbound
      have hball : ∀ u ∈ parameterBall center (A.direction center x j) (r j), ‖u‖ ≤ 1 :=
        fun u hu => (hcenter u hu).1
      obtain ⟨next, hnext, hsubset, hnew⟩ := D.next_ball A hj (hr j) (hr1 j) ha hm hM hK
        hball rfl (A.forbiddenSet center x ε j) (A.forbiddenSet_card_le center x ε j)
      have hrnext : r (j + 1) = θ * r j := finiteStageRadius_succ θ j
      change parameterBall next (A.direction next x (j + 1)) (θ * r j) ⊆ _ at hsubset
      change ∀ u ∈ parameterBall next (A.direction next x (j + 1)) (θ * r j), _ at hnew
      rw [← hrnext] at hsubset hnew
      refine ⟨next, ?_⟩
      intro u hu
      have hold := hcenter u (hsubset hu)
      have havoid : ∀ i < j + 1, ∀ z ∈ A.forbiddenSet u x ε i,
          γ i * ε ^ orderBound i ≤ ‖(D.root u : ℂ) - z‖ := by
        intro i hi z hz
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hij | hij
        · exact hold.2.2 i hij z hz
        · subst i
          rw [A.forbiddenSet_eq_on_parameterBall hj (hsubset hu)] at hz
          have hsep := (hnew u hu).2 z hz
          have hscale : γ j * ε ^ orderBound j ≤ r j * a / (8 * M * (H + 1 : ℝ)) := by
            have hmul := mul_le_mul_of_nonneg_left hbound (hr j).le
            have hdiv := div_le_div_of_nonneg_right hmul (by positivity : 0 ≤ 8 * M * (H + 1 : ℝ))
            calc
              γ j * ε ^ orderBound j = (r j * (coeff j * ε ^ orderBound j)) /
                  (8 * M * (H + 1 : ℝ)) := by dsimp [γ, finiteStageGamma, r, coeff]; ring
              _ ≤ r j * a / (8 * M * (H + 1 : ℝ)) := hdiv
          exact hscale.trans hsep
      refine ⟨hold.1, ?_, havoid⟩
      rw [hcformula]
      exact hsensitivity (j + 1) (by omega) hjn u hold.1 havoid
  obtain ⟨center, hcenter⟩ := hex n le_rfl
  have hcenter_mem := parameterBall_center center (A.direction center x n) (hr n).le
  have hbound := (hcenter center hcenter_mem).2.1
  let a := ‖(A.direction center x n).starProjection (D.vector (D.root center))‖
  have ha : 0 < a := (mul_pos (hc n) (pow_pos hε _)).trans_le hbound
  have hball : ∀ u ∈ parameterBall center (A.direction center x n) (r n), ‖u‖ ≤ 1 :=
    fun u hu => (hcenter u hu).1
  obtain ⟨u, hu, herror⟩ := A.exists_large_error_of_root_interval (hr n) ha hM
    (D.root_interval _ (hr n) ha hm hM hball rfl)
  have hgood := hcenter u hu
  refine ⟨u, hgood.1, ?_, ?_⟩
  · have hmul := mul_le_mul_of_nonneg_left hbound (hr n).le
    have hdiv := div_le_div_of_nonneg_right hmul (by positivity : 0 ≤ 2 * M)
    calc
      finiteScaleErrorConstant n m M R wmin K * ε ^ orderBound n =
          (r n * (coeff n * ε ^ orderBound n)) / (2 * M) := by
        dsimp [finiteScaleErrorConstant, r, coeff, H, θ]
        ring
      _ ≤ r n * a / (2 * M) := hdiv
      _ ≤ |A.run u x - D.root u| := herror
  · intro i z hloc
    exact A.root_ne_actual_location_of_avoidance u x ε (D.root u) (γ i.val * ε ^ orderBound i.val) i
      (mul_pos (hγ i.val) (pow_pos hε _)) (hgood.2.2 i.val i.isLt) hloc

end KungTraub
