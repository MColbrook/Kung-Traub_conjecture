import support_reference.KungTraub.GroupedIndexing
import support_reference.KungTraub.AdversaryStep
import support_reference.KungTraub.FiniteStageConstants

/-!
# Constants for a prescribed group schedule

Every scalar observation in group j receives the same separation coefficient.
The polynomial sensitivity product therefore receives one factor per slot.
All constants are selected before the algorithm and the scale.
-/

noncomputable section
open scoped BigOperators

namespace KungTraub

def groupedFiniteStageState {k : ℕ} (sizes : Fin k → ℕ) (n H : ℕ) (M R w θ : ℝ) : ℕ → ℝ × ℝ
  | 0 => (((4 : ℝ) ^ n)⁻¹, w)
  | j + 1 =>
      let previous := groupedFiniteStageState sizes n H M R w θ j
      let gamma := finiteStageRadius θ j * previous.2 / (8 * M * (H + 1 : ℝ))
      let c := previous.1 * (min 1 (gamma / uniformWronskianConstant n)) ^ groupSizeAt sizes j
      (c, w * c / (2 * R + 2))

def groupedFiniteStageGamma {k : ℕ} (sizes : Fin k → ℕ) (n H : ℕ) (M R w θ : ℝ) (j : ℕ) : ℝ :=
  finiteStageRadius θ j * (groupedFiniteStageState sizes n H M R w θ j).2 /
    (8 * M * (H + 1 : ℝ))

theorem groupedFiniteStageState_initial {k : ℕ} (sizes : Fin k → ℕ) (n H : ℕ) (M R w θ : ℝ) :
    groupedFiniteStageState sizes n H M R w θ 0 = (((4 : ℝ) ^ n)⁻¹, w) := by
  sorry

theorem groupedFiniteStageState_c_succ {k : ℕ} (sizes : Fin k → ℕ) (n H : ℕ) (M R w θ : ℝ) (j : ℕ) :
    (groupedFiniteStageState sizes n H M R w θ (j + 1)).1 =
      (groupedFiniteStageState sizes n H M R w θ j).1 *
        (min 1 (groupedFiniteStageGamma sizes n H M R w θ j / uniformWronskianConstant n)) ^ groupSizeAt sizes j := by
  sorry

theorem groupedFiniteStageState_A_succ {k : ℕ} (sizes : Fin k → ℕ) (n H : ℕ) (M R w θ : ℝ) (j : ℕ) :
    (groupedFiniteStageState sizes n H M R w θ (j + 1)).2 =
      w * (groupedFiniteStageState sizes n H M R w θ (j + 1)).1 / (2 * R + 2) := by
  sorry

theorem groupedFiniteStageState_pos {k : ℕ} (sizes : Fin k → ℕ) (n H : ℕ) {M R w θ : ℝ}
    (hM : 0 < M) (hR : 0 < R) (hw : 0 < w) (hθ : 0 < θ) (j : ℕ) :
    0 < (groupedFiniteStageState sizes n H M R w θ j).1 ∧
      0 < (groupedFiniteStageState sizes n H M R w θ j).2 := by
  sorry

theorem groupedFiniteStageGamma_pos {k : ℕ} (sizes : Fin k → ℕ) (n H : ℕ) {M R w θ : ℝ}
    (hM : 0 < M) (hR : 0 < R) (hw : 0 < w) (hθ : 0 < θ) (j : ℕ) :
    0 < groupedFiniteStageGamma sizes n H M R w θ j := by
  sorry


theorem groupedFiniteStageState_c_eq_product {k : ℕ} (sizes : Fin k → ℕ)
    (n H : ℕ) (M R w θ : ℝ) {j : ℕ} (hj : j ≤ k) :
    (groupedFiniteStageState sizes n H M R w θ j).1 =
      sensitivityPolynomialConstant n
        (fun t => groupedFiniteStageGamma sizes n H M R w θ (scalarGroupAt sizes t))
        (groupedPrefixCount sizes j) := by
  sorry

theorem groupedFiniteStage_final_error_constant_pos {k : ℕ} (sizes : Fin k → ℕ)
    (n H : ℕ) {M R w θ : ℝ}
    (hM : 0 < M) (hR : 0 < R) (hw : 0 < w) (hθ : 0 < θ) :
    0 < finiteStageRadius θ k * (groupedFiniteStageState sizes n H M R w θ k).2 /
      (2 * M) := by
  sorry

end KungTraub
