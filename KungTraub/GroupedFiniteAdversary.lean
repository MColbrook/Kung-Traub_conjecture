import KungTraub.GroupedAdversaryStep
import KungTraub.GroupedStageConstants
import KungTraub.GroupedForbiddenSets
import KungTraub.GroupedPolynomialSensitivity

/-!
# The finite-scale adversary for prescribed evaluation groups

The induction constructs actual parameter balls. Their invariants contain the
proved polynomial forbidden sets, and the sensitivity estimate is obtained from
their avoidance. All constants below depend only on the degree and analytic
family bounds, before the algorithm, scale and transcript are chosen.
-/

noncomputable section

namespace KungTraub

def groupedFiniteScaleContraction (n : ℕ) (m M K : ℝ) : ℝ :=
  adversaryRadiusFactor m M (1 + K / (2 * m)) ((n * forbiddenWronskianCountBound n))

def groupedFiniteScaleErrorConstant {k : ℕ} (sizes : Fin k → ℕ) (m M R wmin K : ℝ) : ℝ :=
  let n := groupedObservationCount sizes
  let θ := groupedFiniteScaleContraction n m M K
  finiteStageRadius θ k *
    (groupedFiniteStageState sizes n ((n * forbiddenWronskianCountBound n)) M R wmin θ k).2 / (2 * M)

theorem groupedFiniteScaleContraction_pos (n : ℕ) {m M K : ℝ}
    (hm : 0 < m) (hM : 0 < M) (hK : 0 ≤ K) : 0 < groupedFiniteScaleContraction n m M K :=
  adversaryRadiusFactor_pos hm hM (by positivity)

theorem groupedFiniteScaleErrorConstant_pos {k : ℕ} (sizes : Fin k → ℕ) {m M R wmin K : ℝ}
    (hm : 0 < m) (hM : 0 < M) (hR : 0 < R) (hwmin : 0 < wmin) (hK : 0 ≤ K) :
    0 < groupedFiniteScaleErrorConstant sizes m M R wmin K :=
  groupedFiniteStage_final_error_constant_pos sizes _ _ hM hR hwmin
    (groupedFiniteScaleContraction_pos _ hm hM hK)

theorem FiniteRootFamily.grouped_finite_adversary {k : ℕ} (sizes : Fin k → ℕ)
    (_hk : 0 < k) (hsizes : ∀ i, 0 < sizes i)
    {ε x m M R wmin K : ℝ} (D : FiniteRootFamily (groupedObservationCount sizes) ε x m M R wmin K)
    (hm : 0 < m) (hM : 0 < M) (hR : 0 < R) (hwmin : 0 < wmin) (hK : 0 ≤ K)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hhalf : R * ε ≤ 1 / 2)
    (A : GroupedAffineAlgorithm (EuclideanSpace ℝ (Fin (groupedObservationCount sizes + 1))) sizes) :
    ∃ u : EuclideanSpace ℝ (Fin (groupedObservationCount sizes + 1)), ‖u‖ ≤ 1 ∧
      groupedFiniteScaleErrorConstant sizes m M R wmin K * ε ^ groupedStageExponent sizes k ≤ |A.run u x - D.root u| ∧
      ∀ i : Fin k, ∀ slot : Fin (sizes i), ∀ z : ℝ,
        (A.actualObservations u x i slot).location = some z → D.root u ≠ z := by
  let n := groupedObservationCount sizes
  let H := (n * forbiddenWronskianCountBound n)
  let θ := groupedFiniteScaleContraction n m M K
  let r := finiteStageRadius θ
  let coeff := fun j => (groupedFiniteStageState sizes n H M R wmin θ j).2
  let γ := groupedFiniteStageGamma sizes n H M R wmin θ
  have hθ : 0 < θ := groupedFiniteScaleContraction_pos n hm hM hK
  have hθhalf : θ ≤ 1 / 2 := adversaryRadiusFactor_le_half _ _ _ _
  have hr (j : ℕ) : 0 < r j := finiteStageRadius_pos hθ j
  have hr1 (j : ℕ) : r j ≤ 1 :=
    (finiteStageRadius_le_half hθ.le (by linarith : θ ≤ 1) j).trans (by norm_num)
  have hc (j : ℕ) : 0 < coeff j := (groupedFiniteStageState_pos sizes n H hM hR hwmin hθ j).2
  have hγ (j : ℕ) : 0 < γ j := groupedFiniteStageGamma_pos sizes n H hM hR hwmin hθ j
  have hcformula (j : ℕ) (hj : j < k) : coeff (j + 1) =
      wmin * sensitivityPolynomialConstant n (fun t => γ (scalarGroupAt sizes t))
        (groupedPrefixCount sizes (j + 1)) / (2 * R + 2) := by
    change (groupedFiniteStageState sizes n H M R wmin θ (j + 1)).2 = _
    rw [groupedFiniteStageState_A_succ, groupedFiniteStageState_c_eq_product sizes n H M R wmin θ
      (Nat.succ_le_of_lt hj)]
  let Good (j : ℕ) (center : EuclideanSpace ℝ (Fin (groupedObservationCount sizes + 1))) : Prop :=
    ∀ u ∈ parameterBall center (A.direction center x j) (r j),
      ‖u‖ ≤ 1 ∧
      coeff j * ε ^ groupedStageExponent sizes j ≤ ‖(A.direction u x j).starProjection (D.vector (D.root u))‖ ∧
      ∀ i : Fin k, i.val < j → ∀ z ∈ A.groupForbiddenSet u x ε i,
        γ i.val * ε ^ groupedStageExponent sizes i.val ≤ ‖(D.root u : ℂ) - z‖
  have hsensitivity (j : ℕ) (hj : 0 < j) (hjn : j ≤ k)
      (u : EuclideanSpace ℝ (Fin (groupedObservationCount sizes + 1))) (hu : ‖u‖ ≤ 1)
      (havoid : ∀ i : Fin k, i.val < j → ∀ z ∈ A.groupForbiddenSet u x ε i,
        γ i.val * ε ^ groupedStageExponent sizes i.val ≤ ‖(D.root u : ℂ) - z‖) :
      (wmin * sensitivityPolynomialConstant n (fun t => γ (scalarGroupAt sizes t))
        (groupedPrefixCount sizes j) / (2 * R + 2)) * ε ^ groupedStageExponent sizes j ≤
        ‖(A.direction u x j).starProjection (D.vector (D.root u))‖ := by
    exact A.projected_sensitivity_of_group_forbidden_avoidance hsizes hj hjn
      u (D.root u) x γ (fun i _ => hγ i) hε hε1 hR hwmin (D.weight_lower u hu)
      (D.root_distance u hu) hhalf havoid
  have hex (j : ℕ) (hjn : j ≤ k) : ∃ center, Good j center := by
    induction j with
    | zero =>
      refine ⟨0, ?_⟩
      intro u hu
      have hu' : ‖u‖ ≤ 1 / 2 := by
        simpa only [sub_zero, r, finiteStageRadius_zero] using hu.2
      have hu1 : ‖u‖ ≤ 1 := hu'.trans (by norm_num)
      refine ⟨hu1, ?_, ?_⟩
      · simpa only [coeff, groupedFiniteStageState, groupedStageExponent_zero, pow_one] using
          D.grouped_initial_sensitivity_at A u hu1 hε.le
      · intro i hi
        omega
    | succ j ih =>
      have hj : j < k := by omega
      obtain ⟨center, hcenter⟩ := ih (Nat.le_of_lt hj)
      have hcenter_mem := parameterBall_center center (A.direction center x j) (hr j).le
      have hbound := (hcenter center hcenter_mem).2.1
      let a := ‖(A.direction center x j).starProjection (D.vector (D.root center))‖
      have ha : 0 < a := (mul_pos (hc j) (pow_pos hε _)).trans_le hbound
      have hball : ∀ u ∈ parameterBall center (A.direction center x j) (r j), ‖u‖ ≤ 1 :=
        fun u hu => (hcenter u hu).1
      have hsize : sizes ⟨j, hj⟩ ≤ n := by
        exact Finset.single_le_sum (fun i _ => Nat.zero_le (sizes i))
          (Finset.mem_univ (⟨j, hj⟩ : Fin k))
      have hcard : (A.groupForbiddenSet center x ε ⟨j, hj⟩).card ≤ H :=
        (A.groupForbiddenSet_card_le center x ε ⟨j, hj⟩).trans
          (Nat.mul_le_mul_right _ hsize)
      obtain ⟨next, hnext, hsubset, hnew⟩ := D.next_group_ball A hj (hr j) (hr1 j) ha hm hM hK
        hball rfl (A.groupForbiddenSet center x ε ⟨j, hj⟩) hcard
      have hrnext : r (j + 1) = θ * r j := finiteStageRadius_succ θ j
      change parameterBall next (A.direction next x (j + 1)) (θ * r j) ⊆ _ at hsubset
      change ∀ u ∈ parameterBall next (A.direction next x (j + 1)) (θ * r j), _ at hnew
      rw [← hrnext] at hsubset hnew
      refine ⟨next, ?_⟩
      intro u hu
      have hold := hcenter u (hsubset hu)
      have havoid : ∀ i : Fin k, i.val < j + 1 → ∀ z ∈ A.groupForbiddenSet u x ε i,
          γ i.val * ε ^ groupedStageExponent sizes i.val ≤ ‖(D.root u : ℂ) - z‖ := by
        intro i hi z hz
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hij | hij
        · exact hold.2.2 i hij z hz
        · have hieq : i = ⟨j, hj⟩ := Fin.ext hij
          subst i
          rw [A.groupForbiddenSet_eq_on_parameterBall ⟨j, hj⟩ (hsubset hu)] at hz
          have hsep := (hnew u hu).2 z hz
          have hscale : γ j * ε ^ groupedStageExponent sizes j ≤ r j * a / (8 * M * (H + 1 : ℝ)) := by
            have hmul := mul_le_mul_of_nonneg_left hbound (hr j).le
            have hdiv := div_le_div_of_nonneg_right hmul (by positivity : 0 ≤ 8 * M * (H + 1 : ℝ))
            calc
              γ j * ε ^ groupedStageExponent sizes j = (r j * (coeff j * ε ^ groupedStageExponent sizes j)) /
                  (8 * M * (H + 1 : ℝ)) := by dsimp [γ, groupedFiniteStageGamma, r, coeff]; ring
              _ ≤ r j * a / (8 * M * (H + 1 : ℝ)) := hdiv
          exact hscale.trans hsep
      refine ⟨hold.1, ?_, havoid⟩
      rw [hcformula j hj]
      exact hsensitivity (j + 1) (by omega) hjn u hold.1 havoid
  obtain ⟨center, hcenter⟩ := hex k le_rfl
  have hcenter_mem := parameterBall_center center (A.direction center x k) (hr k).le
  have hbound := (hcenter center hcenter_mem).2.1
  let a := ‖(A.direction center x k).starProjection (D.vector (D.root center))‖
  have ha : 0 < a := (mul_pos (hc k) (pow_pos hε _)).trans_le hbound
  have hball : ∀ u ∈ parameterBall center (A.direction center x k) (r k), ‖u‖ ≤ 1 :=
    fun u hu => (hcenter u hu).1
  obtain ⟨u, hu, herror⟩ := A.exists_large_error_of_root_interval (hr k) ha hM
    (D.root_interval _ (hr k) ha hm hM hball rfl)
  have hgood := hcenter u hu
  refine ⟨u, hgood.1, ?_, ?_⟩
  · have hmul := mul_le_mul_of_nonneg_left hbound (hr k).le
    have hdiv := div_le_div_of_nonneg_right hmul (by positivity : 0 ≤ 2 * M)
    calc
      groupedFiniteScaleErrorConstant sizes m M R wmin K * ε ^ groupedStageExponent sizes k =
          (r k * (coeff k * ε ^ groupedStageExponent sizes k)) / (2 * M) := by
        dsimp [groupedFiniteScaleErrorConstant, r, coeff, H, θ]
        ring
      _ ≤ r k * a / (2 * M) := hdiv
      _ ≤ |A.run u x - D.root u| := herror
  · intro i slot z hloc heq
    have hmem := A.actual_location_mem_groupForbiddenSet u x ε i slot hloc
    have hsep := hgood.2.2 i i.isLt (z : ℂ) hmem
    rw [heq, sub_self, norm_zero] at hsep
    exact (not_le_of_gt (mul_pos (hγ i.val) (pow_pos hε _))) hsep

end KungTraub
