import appendix_reference.KungTraubAppendices.HermiteStepBounds

/-! Division by the current nonzero error in the contraction estimate. -/

noncomputable section
open Set
namespace KungTraubAppendices

/-- The ratio estimate, with the current error canceled only after
its strict positivity has been proved. The product retains the initial point. -/
theorem InverseHermiteLocalData.step_error_ratio {n : ℕ} {hn : 2 ≤ n}
    {U : Set ℝ} {f : ℝ → ℝ} {α : ℝ} (d : InverseHermiteLocalData n hn U f α)
    {j : ℕ} (hj : j ≤ n - 2) (points : Fin (j + 1) → ℝ)
    (hpoints : Function.Injective points)
    (hin : ∀ i, points i ∈ Icc (α - d.δ) (α + d.δ))
    (hlast : points (Fin.last j) ≠ α) :
    |(hermiteWithDerivative Finset.univ (fun i => f (points i)) points 0
      (deriv f (points 0))⁻¹).eval 0 - α| / |points (Fin.last j) - α| ≤
      inverseHermiteDerivativeBound n hn d.g (Icc (-d.r) d.r) *
        d.L ^ (j + 2) * |points 0 - α| * ∏ i : Fin j, |points i.castSucc - α| := by
  sorry

/-- The ratio is strictly below one half on every nonroot step. -/
theorem InverseHermiteLocalData.step_error_ratio_lt_half {n : ℕ} {hn : 2 ≤ n}
    {U : Set ℝ} {f : ℝ → ℝ} {α : ℝ} (d : InverseHermiteLocalData n hn U f α)
    {j : ℕ} (hj : j ≤ n - 2) (points : Fin (j + 1) → ℝ)
    (hpoints : Function.Injective points)
    (hin : ∀ i, points i ∈ Icc (α - d.δ) (α + d.δ))
    (hlast : points (Fin.last j) ≠ α) :
    |(hermiteWithDerivative Finset.univ (fun i => f (points i)) points 0
      (deriv f (points 0))⁻¹).eval 0 - α| / |points (Fin.last j) - α| < (1 / 2 : ℝ) := by
  sorry

end KungTraubAppendices
