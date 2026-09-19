import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! The exact initial radius and contraction factor of Appendix B. -/

noncomputable section

namespace KungTraubAppendices

/-- The zero-Lipschitz case implements the infinite-ratio convention. -/
def complexInitialRadius (M K : ℝ) : ℝ :=
  if K = 0 then 1 / 2 else min (1 / 2) (2 * M / K)

theorem complexInitialRadius_pos {M K : ℝ} (hM : 0 < M) (hK : 0 ≤ K) :
    0 < complexInitialRadius M K := by
  unfold complexInitialRadius
  split_ifs with hz
  · norm_num
  · have : 0 < K := lt_of_le_of_ne hK (Ne.symm hz)
    positivity

theorem complexInitialRadius_le_half (M K : ℝ) : complexInitialRadius M K ≤ 1 / 2 := by
  unfold complexInitialRadius
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

theorem complexInitialRadius_lipschitz_bound {M K : ℝ} (hM : 0 < M) (hK : 0 ≤ K) :
    K * complexInitialRadius M K ≤ 2 * M := by
  by_cases hz : K = 0
  · simp only [hz, zero_mul]
    linarith
  · have hKpos : 0 < K := lt_of_le_of_ne hK (Ne.symm hz)
    have h := min_le_right (1 / 2 : ℝ) (2 * M / K)
    have hm := mul_le_mul_of_nonneg_left h hK
    simp only [complexInitialRadius, if_neg hz]
    calc
      _ ≤ K * (2 * M / K) := hm
      _ = 2 * M := by field_simp

/-- The concrete stage bound gives the half radius as a consequence. -/
theorem complexInitialRadius_concrete {K : ℝ} (hK : 0 ≤ K) (hsmall : K ≤ 1 / 32) :
    complexInitialRadius (3 / 2) K = 1 / 2 := by
  unfold complexInitialRadius
  split_ifs with hz
  · rfl
  · have hKpos : 0 < K := lt_of_le_of_ne hK (Ne.symm hz)
    apply min_eq_left
    apply (le_div_iff₀ hKpos).mpr
    linarith

/-- The complex proof uses denominator sixteen in its shrinkage factor. -/
def complexRadiusFactor (m M Q : ℝ) (H : ℕ) : ℝ :=
  min (1 / 2) (m / (16 * Q * M * ((H : ℝ) + 1)))

theorem complexRadiusFactor_pos {m M Q : ℝ} {H : ℕ}
    (hm : 0 < m) (hM : 0 < M) (hQ : 0 < Q) : 0 < complexRadiusFactor m M Q H := by
  unfold complexRadiusFactor
  positivity

theorem complexRadiusFactor_le_half (m M Q : ℝ) (H : ℕ) :
    complexRadiusFactor m M Q H ≤ 1 / 2 := min_le_left _ _

/-- Motion on the new parameter ball consumes at most half the avoidance margin. -/
theorem complexRadiusFactor_motion_bound {m M Q a r : ℝ} {H : ℕ}
    (hm : 0 < m) (hM : 0 < M) (hQ : 0 < Q) (ha : 0 ≤ a) (hr : 0 ≤ r) :
    (Q * a / m) * (complexRadiusFactor m M Q H * r) ≤
      r * a / (16 * M * ((H : ℝ) + 1)) := by
  have htheta : complexRadiusFactor m M Q H ≤ m / (16 * Q * M * ((H : ℝ) + 1)) :=
    min_le_right _ _
  calc
    _ ≤ (Q * a / m) * ((m / (16 * Q * M * ((H : ℝ) + 1))) * r) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right htheta hr) (by positivity)
    _ = _ := by field_simp

end KungTraubAppendices
