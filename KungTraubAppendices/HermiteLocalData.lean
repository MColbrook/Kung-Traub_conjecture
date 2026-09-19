import KungTraubAppendices.LocalNeighborhoods
import KungTraubAppendices.HermiteCoefficientBounds

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
  obtain ⟨a, b, g, ha, hb, hsub, hinj, hfa, hdf, hga, hgzero, hleft, hgderiv⟩ :=
    exists_analytic_inverse_interval hU hα hf hzero hd
  have hI : Ioo a b ∈ 𝓝 α := Ioo_mem_nhds ha hb
  obtain ⟨r, hr, hcompact⟩ := exists_closed_interval_in_analytic_image hf hzero hd hI
  have hgan : AnalyticOnNhd ℝ g (Icc (-r) r) := hga.mono hcompact
  obtain ⟨L, hL, hlinear⟩ := exists_local_linear_bound hf hzero
  have hK : Icc (-r) r ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by linarith) hr
  obtain ⟨δ, hδ, hclosed, himage, hsmall⟩ := exists_common_hermite_neighborhood n hn
    (D := inverseHermiteDerivativeBound n hn g (Icc (-r) r))
    hf.continuousAt hzero hI hK hlinear
  exact ⟨{
    a := a, b := b, r := r, L := L, δ := δ, g := g
    left_lt := ha, lt_right := hb, radius_pos := hr
    linear_constant_ge_one := hL, delta_pos := hδ
    interval_subset := hsub, root_value := hzero, injective := hinj, analytic_f := hfa
    derivative_ne_zero := hdf, compact_interval_subset_image := hcompact
    analytic_g := hgan, inverse_zero := hgzero, left_inverse := hleft
    inverse_derivative := hgderiv, closed_neighborhood_subset := hclosed
    image_and_bound := himage, small := hsmall }⟩

/-- The same constant controls all coefficients in the stated index range,
including coincident nodes. -/
theorem InverseHermiteLocalData.coefficient_bound {n : ℕ} {hn : 2 ≤ n}
    {U : Set ℝ} {f : ℝ → ℝ} {α : ℝ} (d : InverseHermiteLocalData n hn U f α)
    {j : ℕ} (hj : j ≤ n - 2) (nodes : Fin (j + 1) → ℝ)
    (hin : ∀ i, nodes i ∈ Icc (-d.r) d.r) :
    |confluentDividedDifference d.g (0 :: nodes 0 :: List.ofFn nodes)| ≤
      inverseHermiteDerivativeBound n hn d.g (Icc (-d.r) d.r) :=
  hermiteDividedDifference_le_uniform_bound n hn d.analytic_g
    (by constructor <;> linarith [d.radius_pos]) hj nodes hin

end KungTraubAppendices
