import KungTraub.PolynomialSensitivity
import KungTraubAppendices.ComplexStageRadii

/-!
# Constants of the complex finite induction

Adapted from `KungTraub.FiniteStageConstants` with Appendix B's exact radii:
r_j = r₀ θ^j, separation denominator sixteen, and final error denominator four.
The initial radius remains a parameter. All constants are fixed before the
algorithm, scale, or transcript. Gamma j denotes gamma_(j+1) in the paper.
-/
noncomputable section
open scoped BigOperators
namespace KungTraubAppendices
open KungTraub

def complexFiniteStageRadius (r₀ θ : ℝ) (j : ℕ) : ℝ := r₀ * θ ^ j

def complexFiniteStageState (n H : ℕ) (M R w r₀ θ : ℝ) : ℕ → ℝ × ℝ
  | 0 => (((4 : ℝ) ^ n)⁻¹, w)
  | j + 1 =>
      let previous := complexFiniteStageState n H M R w r₀ θ j
      let gamma := complexFiniteStageRadius r₀ θ j * previous.2 / (16 * M * (H + 1 : ℝ))
      let c := previous.1 * min 1 (gamma / uniformWronskianConstant n)
      (c, w * c / (2 * R + 2))

def complexFiniteStageGamma (n H : ℕ) (M R w r₀ θ : ℝ) (j : ℕ) : ℝ :=
  complexFiniteStageRadius r₀ θ j * (complexFiniteStageState n H M R w r₀ θ j).2 /
    (16 * M * (H + 1 : ℝ))

theorem complexFiniteStageRadius_zero (r₀ θ : ℝ) : complexFiniteStageRadius r₀ θ 0 = r₀ := by
  simp [complexFiniteStageRadius]

theorem complexFiniteStageRadius_succ (r₀ θ : ℝ) (j : ℕ) :
    complexFiniteStageRadius r₀ θ (j + 1) = θ * complexFiniteStageRadius r₀ θ j := by
  simp only [complexFiniteStageRadius, pow_succ]
  ring

theorem complexFiniteStageRadius_pos {r₀ θ : ℝ} (hr₀ : 0 < r₀) (hθ : 0 < θ) (j : ℕ) :
    0 < complexFiniteStageRadius r₀ θ j := by unfold complexFiniteStageRadius; positivity

theorem complexFiniteStageRadius_le_initial {r₀ θ : ℝ} (hr₀ : 0 ≤ r₀)
    (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) (j : ℕ) :
    complexFiniteStageRadius r₀ θ j ≤ r₀ := by
  exact (mul_le_mul_of_nonneg_left (pow_le_one₀ hθ hθ1) hr₀).trans_eq (mul_one r₀)

theorem complexFiniteStageState_initial (n H : ℕ) (M R w r₀ θ : ℝ) :
    complexFiniteStageState n H M R w r₀ θ 0 = (((4 : ℝ) ^ n)⁻¹, w) := rfl

theorem complexFiniteStageState_c_succ (n H : ℕ) (M R w r₀ θ : ℝ) (j : ℕ) :
    (complexFiniteStageState n H M R w r₀ θ (j + 1)).1 =
      (complexFiniteStageState n H M R w r₀ θ j).1 *
        min 1 (complexFiniteStageGamma n H M R w r₀ θ j / uniformWronskianConstant n) := rfl

theorem complexFiniteStageState_A_succ (n H : ℕ) (M R w r₀ θ : ℝ) (j : ℕ) :
    (complexFiniteStageState n H M R w r₀ θ (j + 1)).2 =
      w * (complexFiniteStageState n H M R w r₀ θ (j + 1)).1 / (2 * R + 2) := rfl

theorem complexFiniteStageState_pos (n H : ℕ) {M R w r₀ θ : ℝ}
    (hM : 0 < M) (hR : 0 < R) (hw : 0 < w) (hr₀ : 0 < r₀) (hθ : 0 < θ) (j : ℕ) :
    0 < (complexFiniteStageState n H M R w r₀ θ j).1 ∧
      0 < (complexFiniteStageState n H M R w r₀ θ j).2 := by
  induction j with
  | zero => simp only [complexFiniteStageState]; constructor; positivity; exact hw
  | succ j ih =>
    have hg : 0 < complexFiniteStageGamma n H M R w r₀ θ j := by
      unfold complexFiniteStageGamma
      exact div_pos (mul_pos (complexFiniteStageRadius_pos hr₀ hθ j) ih.2) (by positivity)
    have hc : 0 < (complexFiniteStageState n H M R w r₀ θ (j + 1)).1 := by
      rw [complexFiniteStageState_c_succ]
      exact mul_pos ih.1 (lt_min zero_lt_one (div_pos hg (uniformWronskianConstant_pos n)))
    refine ⟨hc, ?_⟩
    rw [complexFiniteStageState_A_succ]
    exact div_pos (mul_pos hw hc) (by positivity)

theorem complexFiniteStageGamma_pos (n H : ℕ) {M R w r₀ θ : ℝ}
    (hM : 0 < M) (hR : 0 < R) (hw : 0 < w) (hr₀ : 0 < r₀) (hθ : 0 < θ) (j : ℕ) :
    0 < complexFiniteStageGamma n H M R w r₀ θ j := by
  unfold complexFiniteStageGamma
  exact div_pos (mul_pos (complexFiniteStageRadius_pos hr₀ hθ j)
    (complexFiniteStageState_pos n H hM hR hw hr₀ hθ j).2) (by positivity)

theorem complexFiniteStageState_c_eq_product (n H : ℕ) (M R w r₀ θ : ℝ) (j : ℕ) :
    (complexFiniteStageState n H M R w r₀ θ j).1 =
      sensitivityPolynomialConstant n (complexFiniteStageGamma n H M R w r₀ θ) j := by
  induction j with
  | zero => simp [complexFiniteStageState, sensitivityPolynomialConstant]
  | succ j ih =>
    rw [complexFiniteStageState_c_succ, ih]
    simp only [sensitivityPolynomialConstant, Finset.prod_range_succ]
    ring

theorem complexFiniteStageState_c_le_one (n H : ℕ) {M R w r₀ θ : ℝ}
    (hM : 0 < M) (hR : 0 < R) (hw : 0 < w) (hr₀ : 0 < r₀) (hθ : 0 < θ) (j : ℕ) :
    (complexFiniteStageState n H M R w r₀ θ j).1 ≤ 1 := by
  rw [complexFiniteStageState_c_eq_product]
  exact sensitivityPolynomialConstant_le_one _
    (fun i _ => complexFiniteStageGamma_pos n H hM hR hw hr₀ hθ i)

theorem complexFiniteStageState_A_le_weight (n H : ℕ) {M R w r₀ θ : ℝ}
    (hM : 0 < M) (hR : 0 < R) (hw : 0 < w) (hr₀ : 0 < r₀) (hθ : 0 < θ) (j : ℕ) :
    (complexFiniteStageState n H M R w r₀ θ j).2 ≤ w := by
  cases j with
  | zero => exact le_rfl
  | succ j =>
    rw [complexFiniteStageState_A_succ]
    apply (div_le_iff₀ (by positivity : 0 < 2 * R + 2)).mpr
    have hc := mul_le_mul_of_nonneg_left (complexFiniteStageState_c_le_one n H hM hR hw hr₀ hθ (j + 1)) hw.le
    nlinarith

theorem complexFiniteStage_final_error_constant_pos (n H : ℕ) {M R w r₀ θ : ℝ}
    (hM : 0 < M) (hR : 0 < R) (hw : 0 < w) (hr₀ : 0 < r₀) (hθ : 0 < θ) :
    0 < complexFiniteStageRadius r₀ θ n * (complexFiniteStageState n H M R w r₀ θ n).2 / (4 * M) := by
  exact div_pos (mul_pos (complexFiniteStageRadius_pos hr₀ hθ n)
    (complexFiniteStageState_pos n H hM hR hw hr₀ hθ n).2) (by positivity)

end KungTraubAppendices
