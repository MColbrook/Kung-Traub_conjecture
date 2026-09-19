import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-!
# Avoidance of finitely many points

The choice of the next answer in Section 3 requires a real point separated from
at most `H` complex points. An equally spaced finite grid proves the manuscript's
bound without a measure estimate. The conclusion retains the full real interval
and the exact factor `4 * (H + 1)`.
-/

open Set

namespace KungTraub

theorem exists_far_from_finite_of_separated {X : Type*} [MetricSpace X]
    {H : ℕ} (S : Finset X) (hcard : S.card ≤ H) (grid : Fin (H + 1) → X)
    {δ : ℝ} (hsep : ∀ i j, i ≠ j → 2 * δ ≤ dist (grid i) (grid j)) :
    ∃ i, ∀ z ∈ S, δ ≤ dist (grid i) z := by
  classical
  by_contra h
  push Not at h
  choose z hz hdist using h
  let f : Fin (H + 1) → {z // z ∈ S} := fun i => ⟨z i, hz i⟩
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have heq : z i = z j := congrArg Subtype.val hij
    have ht := dist_triangle (grid i) (z i) (grid j)
    have hj : dist (z i) (grid j) < δ := by
      simpa [heq, dist_comm] using hdist j
    have hi := hdist i
    have hs := hsep i j hne
    linarith
  have hc := Fintype.card_le_of_injective f hinj
  have hc' : H + 1 ≤ S.card := by simpa using hc
  omega

theorem exists_real_point_away_from_finite_complex_set
    {a b : ℝ} (hab : a < b) {H : ℕ} (S : Finset ℂ) (hcard : S.card ≤ H) :
    ∃ t ∈ Icc a b, ∀ z ∈ S, (b - a) / (4 * (H + 1 : ℝ)) ≤ ‖(t : ℂ) - z‖ := by
  let step : ℝ := (b - a) / (H + 1)
  have hH : (0 : ℝ) < H + 1 := by positivity
  have hstep : 0 < step := div_pos (sub_pos.mpr hab) hH
  have hwidth : (H + 1 : ℝ) * step = b - a := by
    dsimp [step]
    field_simp
  let grid : Fin (H + 1) → ℂ := fun i => ((a + (i.val : ℝ) * step : ℝ) : ℂ)
  have hsep : ∀ i j : Fin (H + 1), i ≠ j →
      2 * ((b - a) / (4 * (H + 1 : ℝ))) ≤ dist (grid i) (grid j) := by
    intro i j hne
    have hval : i.val ≠ j.val := fun h => hne (Fin.ext h)
    have hdiff : 1 ≤ |(i.val : ℝ) - j.val| := by
      rcases lt_or_gt_of_ne hval with hij | hji
      · have hij' : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast hij
        rw [abs_of_nonpos (by linarith : (i.val : ℝ) - j.val ≤ 0)]
        linarith
      · have hji' : (j.val : ℝ) + 1 ≤ i.val := by exact_mod_cast hji
        rw [abs_of_nonneg (by linarith : 0 ≤ (i.val : ℝ) - j.val)]
        linarith
    have hd : dist (grid i) (grid j) = |(i.val : ℝ) - j.val| * step := by
      simp only [grid, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      rw [show a + (i.val : ℝ) * step - (a + (j.val : ℝ) * step) =
        ((i.val : ℝ) - j.val) * step by ring, abs_mul, abs_of_pos hstep]
    rw [hd]
    have hhalf : 2 * ((b - a) / (4 * (H + 1 : ℝ))) = step / 2 := by
      dsimp [step]
      field_simp
      ring
    rw [hhalf]
    nlinarith
  obtain ⟨i, hi⟩ := exists_far_from_finite_of_separated S hcard grid hsep
  refine ⟨a + (i.val : ℝ) * step, ⟨?_, ?_⟩, ?_⟩
  · have hi0 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
    nlinarith
  · have hiH : (i.val : ℝ) ≤ H := by exact_mod_cast Nat.le_of_lt_succ i.isLt
    nlinarith
  · intro z hz
    simpa only [grid, dist_eq_norm] using hi z hz

theorem separation_retained_after_motion {X : Type*} [MetricSpace X]
    {center moved z : X} {δ : ℝ} (hsep : 2 * δ ≤ dist center z)
    (hmotion : dist moved center ≤ δ) : δ ≤ dist moved z := by
  have htriangle := dist_triangle center moved z
  rw [dist_comm center moved] at htriangle
  linarith

end KungTraub
