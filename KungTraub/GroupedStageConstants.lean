import KungTraub.GroupedIndexing
import KungTraub.AdversaryStep
import KungTraub.FiniteStageConstants

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
    groupedFiniteStageState sizes n H M R w θ 0 = (((4 : ℝ) ^ n)⁻¹, w) := rfl

theorem groupedFiniteStageState_c_succ {k : ℕ} (sizes : Fin k → ℕ) (n H : ℕ) (M R w θ : ℝ) (j : ℕ) :
    (groupedFiniteStageState sizes n H M R w θ (j + 1)).1 =
      (groupedFiniteStageState sizes n H M R w θ j).1 *
        (min 1 (groupedFiniteStageGamma sizes n H M R w θ j / uniformWronskianConstant n)) ^ groupSizeAt sizes j := rfl

theorem groupedFiniteStageState_A_succ {k : ℕ} (sizes : Fin k → ℕ) (n H : ℕ) (M R w θ : ℝ) (j : ℕ) :
    (groupedFiniteStageState sizes n H M R w θ (j + 1)).2 =
      w * (groupedFiniteStageState sizes n H M R w θ (j + 1)).1 / (2 * R + 2) := rfl

theorem groupedFiniteStageState_pos {k : ℕ} (sizes : Fin k → ℕ) (n H : ℕ) {M R w θ : ℝ}
    (hM : 0 < M) (hR : 0 < R) (hw : 0 < w) (hθ : 0 < θ) (j : ℕ) :
    0 < (groupedFiniteStageState sizes n H M R w θ j).1 ∧
      0 < (groupedFiniteStageState sizes n H M R w θ j).2 := by
  induction j with
  | zero => simp only [groupedFiniteStageState]; constructor; positivity; exact hw
  | succ j ih =>
    have hg : 0 < groupedFiniteStageGamma sizes n H M R w θ j := by
      unfold groupedFiniteStageGamma
      exact div_pos (mul_pos (finiteStageRadius_pos hθ j) ih.2) (by positivity)
    have hc : 0 < (groupedFiniteStageState sizes n H M R w θ (j + 1)).1 := by
      rw [groupedFiniteStageState_c_succ]
      exact mul_pos ih.1 (pow_pos (lt_min zero_lt_one (div_pos hg (uniformWronskianConstant_pos n))) _)
    refine ⟨hc, ?_⟩
    rw [groupedFiniteStageState_A_succ]
    exact div_pos (mul_pos hw hc) (by positivity)

theorem groupedFiniteStageGamma_pos {k : ℕ} (sizes : Fin k → ℕ) (n H : ℕ) {M R w θ : ℝ}
    (hM : 0 < M) (hR : 0 < R) (hw : 0 < w) (hθ : 0 < θ) (j : ℕ) :
    0 < groupedFiniteStageGamma sizes n H M R w θ j := by
  unfold groupedFiniteStageGamma
  exact div_pos (mul_pos (finiteStageRadius_pos hθ j)
    (groupedFiniteStageState_pos sizes n H hM hR hw hθ j).2) (by positivity)


theorem groupedFiniteStageState_c_eq_product {k : ℕ} (sizes : Fin k → ℕ)
    (n H : ℕ) (M R w θ : ℝ) {j : ℕ} (hj : j ≤ k) :
    (groupedFiniteStageState sizes n H M R w θ j).1 =
      sensitivityPolynomialConstant n
        (fun t => groupedFiniteStageGamma sizes n H M R w θ (scalarGroupAt sizes t))
        (groupedPrefixCount sizes j) := by
  induction j with
  | zero => simp [groupedFiniteStageState, sensitivityPolynomialConstant]
  | succ j ih =>
    have hjk : j < k := by omega
    rw [groupedFiniteStageState_c_succ, ih (by omega)]
    simp only [sensitivityPolynomialConstant, groupedPrefixCount_succ sizes hjk,
      Finset.prod_range_add, groupSizeAt_of_lt sizes hjk]
    have heq : (∏ t ∈ Finset.range (sizes ⟨j, hjk⟩),
        min 1 (groupedFiniteStageGamma sizes n H M R w θ
          (scalarGroupAt sizes (groupedPrefixCount sizes j + t)) /
          uniformWronskianConstant n)) =
        (min 1 (groupedFiniteStageGamma sizes n H M R w θ j /
          uniformWronskianConstant n)) ^ sizes ⟨j, hjk⟩ := by
      calc
        _ = ∏ _t ∈ Finset.range (sizes ⟨j, hjk⟩),
            min 1 (groupedFiniteStageGamma sizes n H M R w θ j /
              uniformWronskianConstant n) := by
          apply Finset.prod_congr rfl
          intro t ht
          rw [scalarGroupAt_offset sizes hjk (Finset.mem_range.mp ht)]
        _ = _ := by simp
    rw [heq]
    ring

theorem groupedFiniteStage_final_error_constant_pos {k : ℕ} (sizes : Fin k → ℕ)
    (n H : ℕ) {M R w θ : ℝ}
    (hM : 0 < M) (hR : 0 < R) (hw : 0 < w) (hθ : 0 < θ) :
    0 < finiteStageRadius θ k * (groupedFiniteStageState sizes n H M R w θ k).2 /
      (2 * M) := by
  exact div_pos (mul_pos (finiteStageRadius_pos hθ k)
    (groupedFiniteStageState_pos sizes n H hM hR hw hθ k).2) (by positivity)

end KungTraub
