import support_reference.KungTraub.AdversaryStep
import support_reference.KungTraub.PolynomialSensitivity

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
  sorry

theorem finiteStageRadius_succ (θ : ℝ) (j : ℕ) :
    finiteStageRadius θ (j + 1) = θ * finiteStageRadius θ j := by
  sorry

theorem finiteStageRadius_pos {θ : ℝ} (hθ : 0 < θ) (j : ℕ) :
    0 < finiteStageRadius θ j := by
  sorry

theorem finiteStageRadius_le_half {θ : ℝ} (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (j : ℕ) :
    finiteStageRadius θ j ≤ 1 / 2 := by
  sorry

theorem finiteStageState_initial (n H : ℕ) (M R w θ : ℝ) :
    finiteStageState n H M R w θ 0 = (((4 : ℝ) ^ n)⁻¹, w) := by
  sorry

theorem finiteStageState_c_succ (n H : ℕ) (M R w θ : ℝ) (j : ℕ) :
    (finiteStageState n H M R w θ (j + 1)).1 =
      (finiteStageState n H M R w θ j).1 *
        min 1 (finiteStageGamma n H M R w θ j / uniformWronskianConstant n) := by
  sorry

theorem finiteStageState_A_succ (n H : ℕ) (M R w θ : ℝ) (j : ℕ) :
    (finiteStageState n H M R w θ (j + 1)).2 =
      w * (finiteStageState n H M R w θ (j + 1)).1 / (2 * R + 2) := by
  sorry

theorem finiteStageState_pos (n H : ℕ) {M R w θ : ℝ}
    (hM : 0 < M) (hR : 0 < R) (hw : 0 < w) (hθ : 0 < θ) (j : ℕ) :
    0 < (finiteStageState n H M R w θ j).1 ∧
      0 < (finiteStageState n H M R w θ j).2 := by
  sorry

theorem finiteStageGamma_pos (n H : ℕ) {M R w θ : ℝ}
    (hM : 0 < M) (hR : 0 < R) (hw : 0 < w) (hθ : 0 < θ) (j : ℕ) :
    0 < finiteStageGamma n H M R w θ j := by
  sorry

theorem finiteStageState_c_eq_product (n H : ℕ) (M R w θ : ℝ) (j : ℕ) :
    (finiteStageState n H M R w θ j).1 =
      sensitivityPolynomialConstant n (finiteStageGamma n H M R w θ) j := by
  sorry

theorem finiteStageState_c_le_one (n H : ℕ) {M R w θ : ℝ}
    (hM : 0 < M) (hR : 0 < R) (hw : 0 < w) (hθ : 0 < θ) (j : ℕ) :
    (finiteStageState n H M R w θ j).1 ≤ 1 := by
  sorry

theorem finiteStageState_A_le_weight (n H : ℕ) {M R w θ : ℝ}
    (hM : 0 < M) (hR : 0 < R) (hw : 0 < w) (hθ : 0 < θ) (j : ℕ) :
    (finiteStageState n H M R w θ j).2 ≤ w := by
  sorry

theorem finiteStage_final_error_constant_pos (n H : ℕ) {M R w θ : ℝ}
    (hM : 0 < M) (hR : 0 < R) (hw : 0 < w) (hθ : 0 < θ) :
    0 < finiteStageRadius θ n * (finiteStageState n H M R w θ n).2 / (2 * M) := by
  sorry

end KungTraub
