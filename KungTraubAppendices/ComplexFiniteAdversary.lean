import KungTraubAppendices.ComplexFiniteFamilyGeometry
import KungTraubAppendices.ComplexFiniteStageConstants
import KungTraubAppendices.ComplexAdaptiveForbiddenSets

/-!
# Finite-scale complex adaptive adversary

The induction follows `KungTraub.FiniteAdversary`, with complex kernels,
projected conjugate evaluation vectors, Appendix B's attained root discs and
its exact denominators. Uniform geometric containment is explicit family data
and must be established by the concrete polynomial stage construction.
-/
noncomputable section
namespace KungTraubAppendices
open KungTraub

def complexFiniteScaleContraction (n : ℕ) (m M K : ℝ) : ℝ :=
  complexRadiusFactor m M (1 + K / (2 * m)) (forbiddenWronskianCountBound n)

def complexFiniteScaleErrorConstant (n : ℕ) (m M R wmin K : ℝ) : ℝ :=
  let θ := complexFiniteScaleContraction n m M K
  complexFiniteStageRadius (complexInitialRadius M K) θ n *
    (complexFiniteStageState n (forbiddenWronskianCountBound n) M R wmin (complexInitialRadius M K) θ n).2 / (4 * M)

theorem complexFiniteScaleContraction_pos (n : ℕ) {m M K : ℝ}
    (hm : 0 < m) (hM : 0 < M) (hK : 0 ≤ K) : 0 < complexFiniteScaleContraction n m M K :=
  complexRadiusFactor_pos hm hM (by positivity)

theorem complexFiniteScaleErrorConstant_pos (n : ℕ) {m M R wmin K : ℝ}
    (hm : 0 < m) (hM : 0 < M) (hR : 0 < R) (hwmin : 0 < wmin) (hK : 0 ≤ K) :
    0 < complexFiniteScaleErrorConstant n m M R wmin K :=
  complexFiniteStage_final_error_constant_pos n _ hM hR hwmin (complexInitialRadius_pos hM hK) (complexFiniteScaleContraction_pos n hm hM hK)

theorem ComplexFiniteRootFamily.finite_adversary {n : ℕ} (_hn : 0 < n)
    {ε m M R wmin K : ℝ} {x : ℂ} (D : ComplexFiniteRootFamily n ε x m M R wmin K)
    (hm : 0 < m) (hM : 0 < M) (hR : 0 < R) (hwmin : 0 < wmin) (hK : 0 ≤ K)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hhalf : R * ε ≤ 1 / 2)
    (A : ComplexAffineAlgorithm (EuclideanSpace ℂ (Fin (n + 1))) n) :
    ∃ u : EuclideanSpace ℂ (Fin (n + 1)), ‖u‖ ≤ 1 ∧
      complexFiniteScaleErrorConstant n m M R wmin K * ε ^ orderBound n ≤ ‖A.run u x - D.root u‖ ∧
      ∀ i : Fin n, ∀ z : ℂ, (A.actualObservation u x i).location = some z → D.root u ≠ z := by
  let H := forbiddenWronskianCountBound n
  let θ := complexFiniteScaleContraction n m M K
  let r₀ := complexInitialRadius M K
  let r := complexFiniteStageRadius r₀ θ
  let coeff := fun j => (complexFiniteStageState n H M R wmin r₀ θ j).2
  let γ := complexFiniteStageGamma n H M R wmin r₀ θ
  have hθ : 0 < θ := complexFiniteScaleContraction_pos n hm hM hK
  have hθhalf : θ ≤ 1 / 2 := complexRadiusFactor_le_half _ _ _ _
  have hr₀ : 0 < r₀ := complexInitialRadius_pos hM hK
  have hr (j : ℕ) : 0 < r j := complexFiniteStageRadius_pos hr₀ hθ j
  have hrinitial (j : ℕ) : r j ≤ r₀ :=
    complexFiniteStageRadius_le_initial hr₀.le hθ.le (by linarith : θ ≤ 1) j
  have hc (j : ℕ) : 0 < coeff j := (complexFiniteStageState_pos n H hM hR hwmin hr₀ hθ j).2
  have hγ (j : ℕ) : 0 < γ j := complexFiniteStageGamma_pos n H hM hR hwmin hr₀ hθ j
  have hcformula (j : ℕ) : coeff (j + 1) =
      wmin * sensitivityPolynomialConstant n γ (j + 1) / (2 * R + 2) := by
    change (complexFiniteStageState n H M R wmin r₀ θ (j + 1)).2 = _
    rw [complexFiniteStageState_A_succ, complexFiniteStageState_c_eq_product]
  let Good (j : ℕ) (center : EuclideanSpace ℂ (Fin (n + 1))) : Prop :=
    ∀ u ∈ complexParameterBall center (A.direction center x j) (r j),
      ‖u‖ ≤ 1 ∧
      coeff j * ε ^ orderBound j ≤ ‖(A.direction u x j).starProjection (complexConjVector (D.vector (D.root u)))‖ ∧
      ∀ i < j, ∀ z ∈ A.forbiddenSet u x ε i, γ i * ε ^ orderBound i ≤ ‖(D.root u : ℂ) - z‖
  have hsensitivity (j : ℕ) (hj : 0 < j) (hjn : j ≤ n)
      (u : EuclideanSpace ℂ (Fin (n + 1))) (hu : ‖u‖ ≤ 1)
      (havoid : ∀ i < j, ∀ z ∈ A.forbiddenSet u x ε i,
        γ i * ε ^ orderBound i ≤ ‖(D.root u : ℂ) - z‖) :
      (wmin * sensitivityPolynomialConstant n γ j / (2 * R + 2)) * ε ^ orderBound j ≤
        ‖(A.direction u x j).starProjection (complexConjVector (D.vector (D.root u)))‖ := by
    rw [A.direction_eq_polynomial_kernel u x hε.ne' j]
    exact complex_kernel_projected_sensitivity_lower_bound hj hjn (A.polynomialObservation u x ε)
      (D.root u) x γ (fun i _ => hγ i) hε hε1 hR hwmin (D.weight_lower u hu)
      (D.root_distance u hu) hhalf (A.queryLocation u x) havoid
  have hex (j : ℕ) (hjn : j ≤ n) : ∃ center, Good j center := by
    induction j with
    | zero =>
      refine ⟨0, ?_⟩
      intro u hu
      have hu' : ‖u‖ ≤ r₀ := by
        simpa only [sub_zero, r, complexFiniteStageRadius_zero] using hu.2
      have hu1 : ‖u‖ ≤ 1 := hu'.trans ((complexInitialRadius_le_half M K).trans (by norm_num))
      refine ⟨hu1, ?_, ?_⟩
      · simpa only [coeff, complexFiniteStageState, orderBound_zero, pow_one] using
          D.initial_sensitivity A u hu1 hε.le
      · intro i hi
        omega
    | succ j ih =>
      have hj : j < n := by omega
      obtain ⟨center, hcenter⟩ := ih (Nat.le_of_lt hj)
      have hcenter_mem := complexParameterBall_center center (A.direction center x j) (hr j).le
      have hbound := (hcenter center hcenter_mem).2.1
      let a := ‖(A.direction center x j).starProjection (complexConjVector (D.vector (D.root center)))‖
      have ha : 0 < a := (mul_pos (hc j) (pow_pos hε _)).trans_le hbound
      have hball : ∀ u ∈ complexParameterBall center (A.direction center x j) (r j), ‖u‖ ≤ 1 :=
        fun u hu => (hcenter u hu).1
      obtain ⟨next, hnext, hsubset, hnew⟩ := D.next_ball A hj (hr j) (hrinitial j) ha hm hM hK
        hball rfl (A.forbiddenSet center x ε j) (A.forbiddenSet_card_le center x ε j)
      have hrnext : r (j + 1) = θ * r j := complexFiniteStageRadius_succ r₀ θ j
      change complexParameterBall next (A.direction next x (j + 1)) (θ * r j) ⊆ _ at hsubset
      change ∀ u ∈ complexParameterBall next (A.direction next x (j + 1)) (θ * r j), _ at hnew
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
          have hscale : γ j * ε ^ orderBound j ≤ r j * a / (16 * M * (H + 1 : ℝ)) := by
            have hmul := mul_le_mul_of_nonneg_left hbound (hr j).le
            have hdiv := div_le_div_of_nonneg_right hmul (by positivity : 0 ≤ 16 * M * (H + 1 : ℝ))
            calc
              γ j * ε ^ orderBound j = (r j * (coeff j * ε ^ orderBound j)) /
                  (16 * M * (H + 1 : ℝ)) := by dsimp [γ, complexFiniteStageGamma, r, coeff]; ring
              _ ≤ r j * a / (16 * M * (H + 1 : ℝ)) := hdiv
          exact hscale.trans hsep
      refine ⟨hold.1, ?_, havoid⟩
      rw [hcformula]
      exact hsensitivity (j + 1) (by omega) hjn u hold.1 havoid
  obtain ⟨center, hcenter⟩ := hex n le_rfl
  have hcenter_mem := complexParameterBall_center center (A.direction center x n) (hr n).le
  have hbound := (hcenter center hcenter_mem).2.1
  let a := ‖(A.direction center x n).starProjection (complexConjVector (D.vector (D.root center)))‖
  have ha : 0 < a := (mul_pos (hc n) (pow_pos hε _)).trans_le hbound
  have hball : ∀ u ∈ complexParameterBall center (A.direction center x n) (r n), ‖u‖ ≤ 1 :=
    fun u hu => (hcenter u hu).1
  have hcover := D.root_disc _ (hr n) (hrinitial n) ha hm hM hK hball rfl
  obtain ⟨u, huhalf, herror⟩ := A.exists_error_ge_of_root_disc
    (show 0 < r n * a / (4 * M) from div_pos (mul_pos (hr n) ha) (by positivity)) hcover
  have hu : u ∈ complexParameterBall center (A.direction center x n) (r n) :=
    complexParameterBall_mono_radius (by linarith [hr n]) huhalf
  have hgood := hcenter u hu
  refine ⟨u, hgood.1, ?_, ?_⟩
  · have hmul := mul_le_mul_of_nonneg_left hbound (hr n).le
    have hdiv := div_le_div_of_nonneg_right hmul (by positivity : 0 ≤ 4 * M)
    calc
      complexFiniteScaleErrorConstant n m M R wmin K * ε ^ orderBound n =
          (r n * (coeff n * ε ^ orderBound n)) / (4 * M) := by
        dsimp [complexFiniteScaleErrorConstant, r, r₀, coeff, H, θ]
        ring
      _ ≤ r n * a / (4 * M) := hdiv
      _ ≤ ‖A.run u x - D.root u‖ := herror
  · intro i z hloc
    exact A.root_ne_actual_location_of_avoidance u x (D.root u) ε (γ i.val * ε ^ orderBound i.val) i
      (mul_pos (hγ i.val) (pow_pos hε _)) (hgood.2.2 i.val i.isLt) hloc

end KungTraubAppendices
