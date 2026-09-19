import appendix_reference.KungTraubAppendices.HermiteStepBounds

/-! Extension of a valid observation history, before the next interpolation. -/

noncomputable section
open Set
namespace KungTraubAppendices

/-- On the derived neighborhood, a zero answer identifies the given root. -/
theorem InverseHermiteLocalData.zero_iff {n : ℕ} {hn : 2 ≤ n}
    {U : Set ℝ} {f : ℝ → ℝ} {α : ℝ} (d : InverseHermiteLocalData n hn U f α)
    {y : ℝ} (hy : y ∈ Icc (α - d.δ) (α + d.δ)) : f y = 0 ↔ y = α := by
  sorry

/-- Contraction places the computed output in the same closed neighborhood. -/
theorem InverseHermiteLocalData.step_mem {n : ℕ} {hn : 2 ≤ n}
    {U : Set ℝ} {f : ℝ → ℝ} {α : ℝ} (d : InverseHermiteLocalData n hn U f α)
    {j : ℕ} (hj : j ≤ n - 2) (points : Fin (j + 1) → ℝ)
    (hpoints : Function.Injective points)
    (hin : ∀ i, points i ∈ Icc (α - d.δ) (α + d.δ))
    (hlast : points (Fin.last j) ≠ α) :
    (hermiteWithDerivative Finset.univ (fun i => f (points i)) points 0
      (deriv f (points 0))⁻¹).eval 0 ∈ Icc (α - d.δ) (α + d.δ) := by
  sorry

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
  sorry

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
  sorry

end KungTraubAppendices
