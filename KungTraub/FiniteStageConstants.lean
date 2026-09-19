import KungTraub.AdversaryStep
import KungTraub.PolynomialSensitivity

/-!
# Constants in the finite adversarial induction

The pair recursion constructs c_j and A_j, with the separate initial value
A_0 = w_*. The separation coefficient gamma_j uses only the preceding stage.
Here gamma j denotes the paper's gamma_(j+1). No algorithm or scale occurs in
these definitions. The product formula for c_j is proved from the recursion.
-/

noncomputable section
open scoped BigOperators

namespace KungTraub

def finiteStageRadius (θ : ℝ) (j : ℕ) : ℝ := θ ^ j / 2

def finiteStageState (n H : ℕ) (M R w θ : ℝ) : ℕ → ℝ × ℝ
  | 0 => (((4 : ℝ) ^ n)⁻¹, w)
  | j + 1 =>
      let previous := finiteStageState n H M R w θ j
      let gamma := finiteStageRadius θ j * previous.2 / (8 * M * (H + 1 : ℝ))
      let c := previous.1 * min 1 (gamma / uniformWronskianConstant n)
      (c, w * c / (2 * R + 2))

def finiteStageGamma (n H : ℕ) (M R w θ : ℝ) (j : ℕ) : ℝ :=
  finiteStageRadius θ j * (finiteStageState n H M R w θ j).2 /
    (8 * M * (H + 1 : ℝ))

theorem finiteStageRadius_zero (θ : ℝ) : finiteStageRadius θ 0 = 1 / 2 := by
  simp [finiteStageRadius]

theorem finiteStageRadius_succ (θ : ℝ) (j : ℕ) :
    finiteStageRadius θ (j + 1) = θ * finiteStageRadius θ j := by
  simp only [finiteStageRadius, pow_succ]
  ring

theorem finiteStageRadius_pos {θ : ℝ} (hθ : 0 < θ) (j : ℕ) :
    0 < finiteStageRadius θ j := by unfold finiteStageRadius; positivity

theorem finiteStageRadius_le_half {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (j : ℕ) :
    finiteStageRadius θ j ≤ 1 / 2 := by
  exact div_le_div_of_nonneg_right (pow_le_one₀ hθ hθ1) (by norm_num)

theorem finiteStageState_initial (n H : ℕ) (M R w θ : ℝ) :
    finiteStageState n H M R w θ 0 = (((4 : ℝ) ^ n)⁻¹, w) := rfl

theorem finiteStageState_c_succ (n H : ℕ) (M R w θ : ℝ) (j : ℕ) :
    (finiteStageState n H M R w θ (j + 1)).1 =
      (finiteStageState n H M R w θ j).1 *
        min 1 (finiteStageGamma n H M R w θ j / uniformWronskianConstant n) := rfl

theorem finiteStageState_A_succ (n H : ℕ) (M R w θ : ℝ) (j : ℕ) :
    (finiteStageState n H M R w θ (j + 1)).2 =
      w * (finiteStageState n H M R w θ (j + 1)).1 / (2 * R + 2) := rfl

theorem finiteStageState_pos (n H : ℕ) {M R w θ : ℝ}
    (hM : 0 < M) (hR : 0 < R) (hw : 0 < w) (hθ : 0 < θ) (j : ℕ) :
    0 < (finiteStageState n H M R w θ j).1 ∧
      0 < (finiteStageState n H M R w θ j).2 := by
  induction j with
  | zero => simp only [finiteStageState]; constructor; positivity; exact hw
  | succ j ih =>
    have hg : 0 < finiteStageGamma n H M R w θ j := by
      unfold finiteStageGamma
      exact div_pos (mul_pos (finiteStageRadius_pos hθ j) ih.2) (by positivity)
    have hc : 0 < (finiteStageState n H M R w θ (j + 1)).1 := by
      rw [finiteStageState_c_succ]
      exact mul_pos ih.1 (lt_min zero_lt_one (div_pos hg (uniformWronskianConstant_pos n)))
    refine ⟨hc, ?_⟩
    rw [finiteStageState_A_succ]
    exact div_pos (mul_pos hw hc) (by positivity)

theorem finiteStageGamma_pos (n H : ℕ) {M R w θ : ℝ}
    (hM : 0 < M) (hR : 0 < R) (hw : 0 < w) (hθ : 0 < θ) (j : ℕ) :
    0 < finiteStageGamma n H M R w θ j := by
  unfold finiteStageGamma
  exact div_pos (mul_pos (finiteStageRadius_pos hθ j)
    (finiteStageState_pos n H hM hR hw hθ j).2) (by positivity)

theorem finiteStageState_c_eq_product (n H : ℕ) (M R w θ : ℝ) (j : ℕ) :
    (finiteStageState n H M R w θ j).1 =
      sensitivityPolynomialConstant n (finiteStageGamma n H M R w θ) j := by
  induction j with
  | zero => simp [finiteStageState, sensitivityPolynomialConstant]
  | succ j ih =>
    rw [finiteStageState_c_succ, ih]
    simp only [sensitivityPolynomialConstant, Finset.prod_range_succ]
    ring

theorem finiteStageState_c_le_one (n H : ℕ) {M R w θ : ℝ}
    (hM : 0 < M) (hR : 0 < R) (hw : 0 < w) (hθ : 0 < θ) (j : ℕ) :
    (finiteStageState n H M R w θ j).1 ≤ 1 := by
  rw [finiteStageState_c_eq_product]
  exact sensitivityPolynomialConstant_le_one _
    (fun i _ => finiteStageGamma_pos n H hM hR hw hθ i)

theorem finiteStageState_A_le_weight (n H : ℕ) {M R w θ : ℝ}
    (hM : 0 < M) (hR : 0 < R) (hw : 0 < w) (hθ : 0 < θ) (j : ℕ) :
    (finiteStageState n H M R w θ j).2 ≤ w := by
  cases j with
  | zero => exact le_rfl
  | succ j =>
    rw [finiteStageState_A_succ]
    apply (div_le_iff₀ (by positivity : 0 < 2 * R + 2)).mpr
    have hc := mul_le_mul_of_nonneg_left (finiteStageState_c_le_one n H hM hR hw hθ (j + 1)) hw.le
    nlinarith

theorem finiteStage_final_error_constant_pos (n H : ℕ) {M R w θ : ℝ}
    (hM : 0 < M) (hR : 0 < R) (hw : 0 < w) (hθ : 0 < θ) :
    0 < finiteStageRadius θ n * (finiteStageState n H M R w θ n).2 / (2 * M) := by
  exact div_pos (mul_pos (finiteStageRadius_pos hθ n)
    (finiteStageState_pos n H hM hR hw hθ n).2) (by positivity)

end KungTraub
