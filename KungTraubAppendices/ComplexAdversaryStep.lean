import KungTraubAppendices.ComplexFamilyRootMotion
import KungTraubAppendices.ComplexParameterBalls
import KungTraubAppendices.ComplexDiscAvoidance
import KungTraubAppendices.ComplexStageRadii

/-!
# A complex geometric selection step

The attained root disc and the area estimate select a center away from a finite
forbidden set. The complex radius factor preserves half that separation on
the successor transcript ball.

The argument follows `KungTraub.AdversaryStep`, using the root-disc and motion
bounds for the complex family, with denominators eight and sixteen.
-/

noncomputable section

namespace KungTraubAppendices

variable {d n : ℕ}
local notation "E" => EuclideanSpace ℂ (Fin d)

/-- The complex family and the actual adaptive fibre yield a next
ball with a constant successor prefix and the uniform separation. -/
theorem ComplexAffineAlgorithm.exists_next_ball_avoiding_finite_set
    (A : ComplexAffineAlgorithm E n)
    {P : Set E} {J : Set ℂ} {F : E → ℂ → ℂ} {root : E → ℂ}
    {vector : ℂ → E} {center : E} {x : ℂ} {m M K r a : ℝ} {j H : ℕ}
    (hj : j < n) (hm : 0 < m) (hM : 0 < M) (hK : 0 ≤ K)
    (hr : 0 < r) (hrone : r ≤ 1) (hKr : K * r ≤ 2 * M)
    (hroot : ∀ u ∈ P, root u ∈ J ∧ F u (root u) = 0)
    (hlower : ∀ u ∈ P, ∀ z ∈ J, ∀ t ∈ J,
      m * ‖z - t‖ ≤ ‖F u z - F u t‖)
    (haffine : ∀ u ∈ P, ∀ v ∈ P, ∀ t ∈ J,
      F u t = F v t + complexBilinearDot (u - v) (vector t))
    (hvector : ∀ z ∈ J, ∀ t ∈ J, ‖vector z - vector t‖ ≤ K * ‖z - t‖)
    (hball : complexParameterBall center (A.direction center x j) r ⊆ P)
    (hupper : ∀ t ∈ J, ‖F center t - F center (root center)‖ ≤ M * ‖t - root center‖)
    (ha : 0 < a)
    (haeq : a = ‖(A.direction center x j).starProjection
      (complexConjVector (vector (root center)))‖)
    (hcontain : Metric.closedBall (root center) (r * a / (4 * M)) ⊆ J)
    (S : Finset ℂ) (hcard : S.card ≤ H) :
    let Q := 1 + K / (2 * m)
    ∃ next ∈ complexParameterBall center (A.direction center x j) (r / 2),
      complexParameterBall next (A.direction next x (j + 1))
          (complexRadiusFactor m M Q H * r) ⊆
        complexParameterBall center (A.direction center x j) r ∧
      ∀ u ∈ complexParameterBall next (A.direction next x (j + 1))
          (complexRadiusFactor m M Q H * r),
        A.prefix u x (j + 1) (Nat.succ_le_of_lt hj) =
            A.prefix next x (j + 1) (Nat.succ_le_of_lt hj) ∧
        ∀ z ∈ S, r * a / (16 * M * ((H : ℝ) + 1)) ≤ ‖root u - z‖ := by
  let Q : ℝ := 1 + K / (2 * m)
  change ∃ next ∈ complexParameterBall center (A.direction center x j) (r / 2),
    complexParameterBall next (A.direction next x (j + 1))
        (complexRadiusFactor m M Q H * r) ⊆
      complexParameterBall center (A.direction center x j) r ∧
    ∀ u ∈ complexParameterBall next (A.direction next x (j + 1))
        (complexRadiusFactor m M Q H * r),
      A.prefix u x (j + 1) (Nat.succ_le_of_lt hj) =
          A.prefix next x (j + 1) (Nat.succ_le_of_lt hj) ∧
      ∀ z ∈ S, r * a / (16 * M * ((H : ℝ) + 1)) ≤ ‖root u - z‖
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hhalf : complexParameterBall center (A.direction center x j) (r / 2) ⊆
      complexParameterBall center (A.direction center x j) r :=
    complexParameterBall_mono_radius (by linarith)
  have hcenterP : center ∈ P :=
    hball (complexParameterBall_center center (A.direction center x j) hr.le)
  have hparameter : ∀ h ∈ A.direction center x j, ‖h‖ ≤ r / 2 → center + h ∈ P :=
    fun h hh hn => hball (hhalf (complexParameterBall_add_mem hh hn))
  have hcover := complexFamily_attained_closedBall (A.direction center x j)
    hm hM hK hr hKr hroot hlower haffine hvector hcenterP hparameter hupper
    (by simpa only [← haeq] using ha) (by simpa only [← haeq] using hcontain)
  obtain ⟨t, ht, htsep⟩ := exists_mem_closedBall_avoiding_finset (root center)
    (show 0 < r * a / (4 * M) by positivity) S H hcard
  have htcover := hcover (by simpa only [← haeq] using ht)
  obtain ⟨next, ⟨hnextP, hnextdir, hnextnorm⟩, hnextroot⟩ := htcover
  have hnext : next ∈ complexParameterBall center (A.direction center x j) (r / 2) :=
    ⟨hnextdir, hnextnorm⟩
  have hsep : ∀ z ∈ S,
      2 * (r * a / (16 * M * ((H : ℝ) + 1))) < ‖root next - z‖ := by
    intro z hz
    rw [hnextroot]
    have heq : 2 * (r * a / (16 * M * ((H : ℝ) + 1))) =
        (r * a / (4 * M)) / (2 * ((H : ℝ) + 1)) := by
      have hH : (H : ℝ) + 1 ≠ 0 := by positivity
      field_simp [hM.ne', hH]
      ring
    rw [heq]
    exact htsep z hz
  have hsmall : complexRadiusFactor m M Q H * r ≤ r / 2 := by
    have h := mul_le_mul_of_nonneg_right (complexRadiusFactor_le_half m M Q H) hr.le
    linarith
  have hsubset := A.parameterBall_next_subset hj hnext hsmall
  have hp := A.prefix_eq_on_parameterBall hj.le hnext
  have hWV : A.direction next x (j + 1) ≤ A.direction center x j := by
    rw [A.direction_succ_of_prefix_eq hj hp]
    exact inf_le_left
  refine ⟨next, hnext, hsubset, ?_⟩
  intro u hu
  refine ⟨A.prefix_eq_on_parameterBall (Nat.succ_le_of_lt hj) hu, ?_⟩
  have hraw := complexFamily_root_motion_from_half_ball
    (A.direction center x j) (A.direction next x (j + 1)) hWV
    hm hK hrone hroot hlower haffine hvector hnextP hcenterP
    (hball (hsubset hu)) hnextdir hnextnorm hu.1
  have hmove : ‖root u - root next‖ ≤ r * a / (16 * M * ((H : ℝ) + 1)) := by
    calc
      _ ≤ (Q * a / m) * ‖u - next‖ := by simpa only [Q, haeq] using hraw
      _ ≤ (Q * a / m) * (complexRadiusFactor m M Q H * r) :=
        mul_le_mul_of_nonneg_left hu.2 (by positivity)
      _ ≤ r * a / (16 * M * ((H : ℝ) + 1)) :=
        complexRadiusFactor_motion_bound hm hM hQ ha.le hr.le
  intro z hz
  have htriangle : ‖root next - z‖ ≤ ‖root u - root next‖ + ‖root u - z‖ := by
    simpa only [norm_sub_rev (root next) (root u)] using
      norm_sub_le_norm_sub_add_norm_sub (root next) (root u) z
  have hsepz := hsep z hz
  linarith

/-- Opposite points of an attained root disc force an error at least its
radius for one parameter with the same complete transcript. -/
theorem ComplexAffineAlgorithm.exists_error_ge_of_root_disc
    (A : ComplexAffineAlgorithm E n) {root : E → ℂ} {center : E}
    {x α : ℂ} {r R : ℝ} (hR : 0 < R)
    (hcover : Metric.closedBall α R ⊆
      root '' complexParameterBall center (A.direction center x n) r) :
    ∃ u ∈ complexParameterBall center (A.direction center x n) r,
      R ≤ ‖A.run u x - root u‖ := by
  have hplus : α + (R : ℂ) ∈ Metric.closedBall α R := by
    simp [Metric.mem_closedBall, dist_eq_norm, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hR]
  have hminus : α - (R : ℂ) ∈ Metric.closedBall α R := by
    simp [Metric.mem_closedBall, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hR]
  obtain ⟨u, hu, huroot⟩ := hcover hplus
  obtain ⟨v, hv, hvroot⟩ := hcover hminus
  have hsep : ‖(α + (R : ℂ)) - (α - (R : ℂ))‖ = 2 * R := by
    have heq : (α + (R : ℂ)) - (α - (R : ℂ)) = (2 : ℂ) * (R : ℂ) := by ring
    rw [heq, norm_mul]
    norm_num [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  have htriangle : 2 * R ≤ ‖A.run center x - (α + (R : ℂ))‖ +
      ‖A.run center x - (α - (R : ℂ))‖ := by
    rw [← hsep]
    simpa only [norm_sub_rev (α + (R : ℂ)) (A.run center x)] using
      norm_sub_le_norm_sub_add_norm_sub (α + (R : ℂ)) (A.run center x) (α - (R : ℂ))
  by_cases herror : R ≤ ‖A.run center x - (α + (R : ℂ))‖
  · refine ⟨u, hu, ?_⟩
    rw [A.run_eq_on_parameterBall hu, huroot]
    exact herror
  · refine ⟨v, hv, ?_⟩
    rw [A.run_eq_on_parameterBall hv, hvroot]
    linarith

end KungTraubAppendices
