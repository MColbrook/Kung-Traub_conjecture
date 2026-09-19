import appendix_reference.KungTraubAppendices.LocalNeighborhoods
import appendix_reference.KungTraubAppendices.HermiteCoefficientBounds

/-!
# Local data for the sharpness proof

The simple analytic zero gives common intervals and constants for the error
estimates. These data are fixed before the starting point is chosen.
-/

noncomputable section

open Set
open scoped Topology

namespace KungTraubAppendices

/-- The common intervals, constants and derivative bound of Appendix A. -/
structure InverseHermiteLocalData (n : ℕ) (hn : 2 ≤ n) (U : Set ℝ) (f : ℝ → ℝ) (α : ℝ) where
  a : ℝ
  b : ℝ
  r : ℝ
  L : ℝ
  δ : ℝ
  g : ℝ → ℝ
  left_lt : a < α
  lt_right : α < b
  radius_pos : 0 < r
  linear_constant_ge_one : 1 ≤ L
  delta_pos : 0 < δ
  interval_subset : Ioo a b ⊆ U
  root_value : f α = 0
  injective : InjOn f (Ioo a b)
  analytic_f : AnalyticOnNhd ℝ f (Ioo a b)
  derivative_ne_zero : ∀ y ∈ Ioo a b, deriv f y ≠ 0
  compact_interval_subset_image : Icc (-r) r ⊆ f '' Ioo a b
  analytic_g : AnalyticOnNhd ℝ g (Icc (-r) r)
  inverse_zero : g 0 = α
  left_inverse : ∀ y ∈ Ioo a b, g (f y) = y
  inverse_derivative : ∀ y ∈ Ioo a b, deriv g (f y) = 1 / deriv f y
  closed_neighborhood_subset : Icc (α - δ) (α + δ) ⊆ Ioo a b
  image_and_bound : ∀ y ∈ Icc (α - δ) (α + δ),
    f y ∈ Icc (-r) r ∧ |f y| ≤ L * |y - α|
  small : ∀ j : ℕ, j ≤ n - 2 →
    inverseHermiteDerivativeBound n hn g (Icc (-r) r) *
      L ^ (j + 2) * δ ^ (j + 1) < (1 / 2 : ℝ)

/-- A simple analytic zero gives all local data on the open input domain. -/
theorem exists_inverseHermiteLocalData (n : ℕ) (hn : 2 ≤ n)
    {U : Set ℝ} (hU : IsOpen U) {f : ℝ → ℝ} {α : ℝ} (hα : α ∈ U)
    (hf : AnalyticAt ℝ f α) (hzero : f α = 0) (hd : deriv f α ≠ 0) :
    Nonempty (InverseHermiteLocalData n hn U f α) := by
  sorry

/-- The same constant controls all coefficients in the stated index range,
including coincident nodes. -/
theorem InverseHermiteLocalData.coefficient_bound {n : ℕ} {hn : 2 ≤ n}
    {U : Set ℝ} {f : ℝ → ℝ} {α : ℝ} (d : InverseHermiteLocalData n hn U f α)
    {j : ℕ} (hj : j ≤ n - 2) (nodes : Fin (j + 1) → ℝ)
    (hin : ∀ i, nodes i ∈ Icc (-d.r) d.r) :
    |confluentDividedDifference d.g (0 :: nodes 0 :: List.ofFn nodes)| ≤
      inverseHermiteDerivativeBound n hn d.g (Icc (-d.r) d.r) := by
  sorry

end KungTraubAppendices
