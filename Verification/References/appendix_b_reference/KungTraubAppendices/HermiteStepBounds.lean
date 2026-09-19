import appendix_b_reference.KungTraubAppendices.HermiteLocalData
import appendix_b_reference.KungTraubAppendices.HermiteDividedDifference

/-! Estimates for the polynomial update computed from actual observations. -/

noncomputable section

open Polynomial Set

namespace KungTraubAppendices

/-- The observed-data update satisfies the exact product estimate. Its
inverse and local constants occur only in the proof and its bound. -/
theorem InverseHermiteLocalData.step_error_product {n : ℕ} {hn : 2 ≤ n}
    {U : Set ℝ} {f : ℝ → ℝ} {α : ℝ} (d : InverseHermiteLocalData n hn U f α)
    {j : ℕ} (hj : j ≤ n - 2) (points : Fin (j + 1) → ℝ)
    (hpoints : Function.Injective points)
    (hin : ∀ i, points i ∈ Icc (α - d.δ) (α + d.δ)) :
    |(hermiteWithDerivative Finset.univ (fun i => f (points i)) points 0
        (deriv f (points 0))⁻¹).eval 0 - α| ≤
      inverseHermiteDerivativeBound n hn d.g (Icc (-d.r) d.r) *
        d.L ^ (j + 2) * |points 0 - α| * ∏ i, |points i - α| := by
  sorry

/-- The common radius makes every update contract relative to the most
recent nonroot point. The same argument includes the singleton base case. -/
theorem InverseHermiteLocalData.step_strict_contraction {n : ℕ} {hn : 2 ≤ n}
    {U : Set ℝ} {f : ℝ → ℝ} {α : ℝ} (d : InverseHermiteLocalData n hn U f α)
    {j : ℕ} (hj : j ≤ n - 2) (points : Fin (j + 1) → ℝ)
    (hpoints : Function.Injective points)
    (hin : ∀ i, points i ∈ Icc (α - d.δ) (α + d.δ))
    (hlast : points (Fin.last j) ≠ α) :
    |(hermiteWithDerivative Finset.univ (fun i => f (points i)) points 0
        (deriv f (points 0))⁻¹).eval 0 - α| < |points (Fin.last j) - α| / 2 := by
  sorry

end KungTraubAppendices
