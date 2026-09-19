import KungTraubAppendices.HermiteStepBounds

/-! Extension of a valid observation history, before the next interpolation. -/

noncomputable section
open Set
namespace KungTraubAppendices

/-- On the derived neighborhood, a zero answer identifies the given root. -/
theorem InverseHermiteLocalData.zero_iff {n : ℕ} {hn : 2 ≤ n}
    {U : Set ℝ} {f : ℝ → ℝ} {α : ℝ} (d : InverseHermiteLocalData n hn U f α)
    {y : ℝ} (hy : y ∈ Icc (α - d.δ) (α + d.δ)) : f y = 0 ↔ y = α := by
  constructor
  · intro h
    have hi := d.left_inverse y (d.closed_neighborhood_subset hy)
    rw [h, d.inverse_zero] at hi
    exact hi.symm
  · rintro rfl
    exact d.root_value

/-- Contraction places the computed output in the same closed neighborhood. -/
theorem InverseHermiteLocalData.step_mem {n : ℕ} {hn : 2 ≤ n}
    {U : Set ℝ} {f : ℝ → ℝ} {α : ℝ} (d : InverseHermiteLocalData n hn U f α)
    {j : ℕ} (hj : j ≤ n - 2) (points : Fin (j + 1) → ℝ)
    (hpoints : Function.Injective points)
    (hin : ∀ i, points i ∈ Icc (α - d.δ) (α + d.δ))
    (hlast : points (Fin.last j) ≠ α) :
    (hermiteWithDerivative Finset.univ (fun i => f (points i)) points 0
      (deriv f (points 0))⁻¹).eval 0 ∈ Icc (α - d.δ) (α + d.δ) := by
  have hc := d.step_strict_contraction hj points hpoints hin hlast
  have he : |points (Fin.last j) - α| ≤ d.δ := by
    rw [abs_le]
    constructor <;> linarith [(hin (Fin.last j)).1, (hin (Fin.last j)).2]
  have hnew := (abs_le.mp (show
      |(hermiteWithDerivative Finset.univ (fun i => f (points i)) points 0
        (deriv f (points 0))⁻¹).eval 0 - α| ≤ d.δ by linarith [d.delta_pos]))
  constructor <;> linarith [hnew.1, hnew.2]

/-- The new point is closer than every earlier point. Thus it is a fresh
point even if it equals the root, before any new interpolation is invoked. -/
theorem InverseHermiteLocalData.step_lt_each {n : ℕ} {hn : 2 ≤ n}
    {U : Set ℝ} {f : ℝ → ℝ} {α : ℝ} (d : InverseHermiteLocalData n hn U f α)
    {j : ℕ} (hj : j ≤ n - 2) (points : Fin (j + 1) → ℝ)
    (hpoints : Function.Injective points)
    (hin : ∀ i, points i ∈ Icc (α - d.δ) (α + d.δ))
    (hlast : points (Fin.last j) ≠ α)
    (hmin : ∀ i, |points (Fin.last j) - α| ≤ |points i - α|) (i : Fin (j + 1)) :
    |(hermiteWithDerivative Finset.univ (fun i => f (points i)) points 0
      (deriv f (points 0))⁻¹).eval 0 - α| < |points i - α| := by
  have hc := d.step_strict_contraction hj points hpoints hin hlast
  have hp := abs_pos.mpr (sub_ne_zero.mpr hlast)
  linarith [hmin i]

/-- A fresh computed point preserves injectivity of the observation history. -/
theorem InverseHermiteLocalData.step_snoc_injective {n : ℕ} {hn : 2 ≤ n}
    {U : Set ℝ} {f : ℝ → ℝ} {α : ℝ} (d : InverseHermiteLocalData n hn U f α)
    {j : ℕ} (hj : j ≤ n - 2) (points : Fin (j + 1) → ℝ)
    (hpoints : Function.Injective points)
    (hin : ∀ i, points i ∈ Icc (α - d.δ) (α + d.δ))
    (hlast : points (Fin.last j) ≠ α)
    (hmin : ∀ i, |points (Fin.last j) - α| ≤ |points i - α|) :
    Function.Injective (Fin.snoc points
      ((hermiteWithDerivative Finset.univ (fun i => f (points i)) points 0
        (deriv f (points 0))⁻¹).eval 0)) := by
  apply Fin.snoc_injective_of_injective hpoints
  rintro ⟨i, hi⟩
  have h := d.step_lt_each hj points hpoints hin hlast hmin i
  rw [← hi] at h
  exact lt_irrefl _ h

end KungTraubAppendices
