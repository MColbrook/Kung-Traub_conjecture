import KungTraubAppendices.LocalInverse
import Mathlib.Tactic

/-! Common neighborhoods and the finite family of strict bounds in Appendix A. -/

noncomputable section

open Set Filter
open scoped Topology

namespace KungTraubAppendices

/-- Every neighborhood of a simple analytic zero has an image containing a
nondegenerate compact interval about zero. -/
theorem exists_closed_interval_in_analytic_image {f : ℝ → ℝ} {α : ℝ} {I : Set ℝ}
    (hf : AnalyticAt ℝ f α) (hzero : f α = 0) (hd : deriv f α ≠ 0)
    (hI : I ∈ 𝓝 α) : ∃ r > 0, Icc (-r) r ⊆ f '' I := by
  have himage : f '' I ∈ map f (𝓝 α) := image_mem_map hI
  rw [hf.hasStrictDerivAt.map_nhds_eq hd, hzero] at himage
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp himage
  refine ⟨r / 2, by positivity, ?_⟩
  intro t ht
  apply hball
  change dist t 0 < r
  rw [Real.dist_eq, sub_zero]
  have habs : |t| ≤ r / 2 := abs_le.mpr ht
  linarith

/-- Analyticity at the zero gives the local linear bound with one fixed
constant at least one, independent of the subsequent starting point. -/
theorem exists_local_linear_bound {f : ℝ → ℝ} {α : ℝ}
    (hf : AnalyticAt ℝ f α) (hzero : f α = 0) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ᶠ y in 𝓝 α, |f y| ≤ L * |y - α| := by
  obtain ⟨K, s, hs, hLip⟩ := hf.hasStrictDerivAt.hasStrictFDerivAt.exists_lipschitzOnWith
  refine ⟨max 1 (K : ℝ), le_max_left _ _, ?_⟩
  filter_upwards [hs] with y hy
  have hbound : |f y| ≤ (K : ℝ) * |y - α| := by
    simpa [Real.dist_eq, hzero] using
      (lipschitzOnWith_iff_dist_le_mul.mp hLip) y hy α (mem_of_mem_nhds hs)
  exact hbound.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _))

/-- One positive radius satisfies every strict power inequality in the
complete index range. All constants are fixed before its choice. -/
theorem exists_small_hermite_radius (n : ℕ) (hn : 2 ≤ n) (D L : ℝ)
    {r : ℝ} (hr : 0 < r) :
    ∃ δ > 0, δ < r ∧ ∀ j : ℕ, j ≤ n - 2 →
      D * L ^ (j + 2) * δ ^ (j + 1) < (1 / 2 : ℝ) := by
  have hevent : ∀ j : Fin (n - 1), ∀ᶠ δ : ℝ in 𝓝 0,
      D * L ^ (j.val + 2) * δ ^ (j.val + 1) < (1 / 2 : ℝ) := by
    intro j
    have hcont : ContinuousAt (fun δ : ℝ => D * L ^ (j.val + 2) * δ ^ (j.val + 1)) 0 := by
      fun_prop
    exact hcont.eventually_lt continuousAt_const (by simp)
  obtain ⟨s, hs, hball⟩ := Metric.eventually_nhds_iff.mp (Filter.eventually_all.mpr hevent)
  let δ := min r s / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδr : δ < r := by dsimp [δ]; have := min_le_left r s; linarith
  have hδs : δ < s := by dsimp [δ]; have := min_le_right r s; linarith
  refine ⟨δ, hδ, hδr, ?_⟩
  intro j hj
  have hdist : dist δ 0 < s := by simpa [Real.dist_eq, abs_of_pos hδ] using hδs
  exact hball hdist ⟨j, by omega⟩

/-- All interval, image, linear-bound and contraction requirements hold on
one closed neighborhood, before any execution is analysed. -/
theorem exists_common_hermite_neighborhood (n : ℕ) (hn : 2 ≤ n)
    {f : ℝ → ℝ} {α D L : ℝ} {I K : Set ℝ}
    (hf : ContinuousAt f α) (hzero : f α = 0) (hI : I ∈ 𝓝 α) (hK : K ∈ 𝓝 (0 : ℝ))
    (hL : ∀ᶠ y in 𝓝 α, |f y| ≤ L * |y - α|) :
    ∃ δ > 0, Icc (α - δ) (α + δ) ⊆ I ∧
      (∀ y ∈ Icc (α - δ) (α + δ), f y ∈ K ∧ |f y| ≤ L * |y - α|) ∧
      (∀ j : ℕ, j ≤ n - 2 → D * L ^ (j + 2) * δ ^ (j + 1) < (1 / 2 : ℝ)) := by
  have hfK : ∀ᶠ y in 𝓝 α, f y ∈ K := hf.tendsto.eventually (by simpa [hzero] using hK)
  have hcommon : ∀ᶠ y in 𝓝 α, y ∈ I ∧ f y ∈ K ∧ |f y| ≤ L * |y - α| :=
    Filter.Eventually.and hI (hfK.and hL)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hcommon
  obtain ⟨δ, hδ, hδr, hsmall⟩ := exists_small_hermite_radius n hn D L hr
  have hclosed : ∀ y ∈ Icc (α - δ) (α + δ),
      y ∈ I ∧ f y ∈ K ∧ |f y| ≤ L * |y - α| := by
    intro y hy
    apply hball
    rw [Real.dist_eq]
    have habs : |y - α| ≤ δ := by
      rw [abs_le]
      constructor <;> linarith [hy.1, hy.2]
    exact habs.trans_lt hδr
  exact ⟨δ, hδ, (fun y hy => (hclosed y hy).1),
    (fun y hy => (hclosed y hy).2), hsmall⟩

end KungTraubAppendices
