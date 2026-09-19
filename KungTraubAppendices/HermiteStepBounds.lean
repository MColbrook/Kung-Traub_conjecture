import KungTraubAppendices.HermiteLocalData
import KungTraubAppendices.HermiteDividedDifference

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
  let nodes := fun i => f (points i)
  let D := inverseHermiteDerivativeBound n hn d.g (Icc (-d.r) d.r)
  have hD : 0 ≤ D := le_trans zero_le_one (one_le_inverseHermiteDerivativeBound _ _ _ _)
  have hL : 0 ≤ d.L := le_trans zero_le_one d.linear_constant_ge_one
  have hI : ∀ i, points i ∈ Ioo d.a d.b := fun i => d.closed_neighborhood_subset (hin i)
  have hnodes : Function.Injective nodes := by
    intro i k heq
    exact hpoints (d.injective (hI i) (hI k) heq)
  have hK : ∀ i, nodes i ∈ Icc (-d.r) d.r := fun i => (d.image_and_bound _ (hin i)).1
  have hgan : ∀ i, AnalyticAt ℝ d.g (nodes i) := fun i => d.analytic_g _ (hK i)
  have hgzero : AnalyticAt ℝ d.g 0 :=
    d.analytic_g _ (by constructor <;> linarith [d.radius_pos])
  have hvalues : (fun i => d.g (nodes i)) = points :=
    funext (fun i => d.left_inverse _ (hI i))
  have hderiv : deriv d.g (nodes 0) = (deriv f (points 0))⁻¹ := by
    simpa only [one_div] using d.inverse_derivative _ (hI 0)
  have heq := hermiteWithDerivative_dividedDifference_remainder nodes hnodes hgan 0 hgzero
  rw [hvalues, hderiv, d.inverse_zero] at heq
  have habs : |(hermiteWithDerivative Finset.univ nodes points 0
      (deriv f (points 0))⁻¹).eval 0 - α| =
      |confluentDividedDifference d.g (0 :: nodes 0 :: List.ofFn nodes)| *
        (|nodes 0| * ∏ i, |nodes i|) := by
    rw [abs_sub_comm, heq, abs_mul, doubleNodal_eval, abs_mul, Finset.abs_prod]
    simp only [zero_sub, abs_neg]
  have hcoef : |confluentDividedDifference d.g (0 :: nodes 0 :: List.ofFn nodes)| ≤ D :=
    d.coefficient_bound hj nodes hK
  have hnodebound : ∀ i, |nodes i| ≤ d.L * |points i - α| :=
    fun i => (d.image_and_bound _ (hin i)).2
  have hprod : (∏ i, |nodes i|) ≤ ∏ i, d.L * |points i - α| :=
    Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun i _ => hnodebound i)
  calc
    _ = |confluentDividedDifference d.g (0 :: nodes 0 :: List.ofFn nodes)| *
        |nodes 0| * ∏ i, |nodes i| := by rw [habs]; ring
    _ ≤ D * (d.L * |points 0 - α|) * ∏ i, d.L * |points i - α| :=
      mul_le_mul (mul_le_mul hcoef (hnodebound 0) (abs_nonneg _) hD) hprod
        (Finset.prod_nonneg (fun _ _ => abs_nonneg _))
        (mul_nonneg hD (mul_nonneg hL (abs_nonneg _)))
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        pow_succ d.L (j + 1)]
      ring

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
  let D := inverseHermiteDerivativeBound n hn d.g (Icc (-d.r) d.r)
  have hD : 0 ≤ D := le_trans zero_le_one (one_le_inverseHermiteDerivativeBound _ _ _ _)
  have hL : 0 ≤ d.L := le_trans zero_le_one d.linear_constant_ge_one
  have herr : ∀ i, |points i - α| ≤ d.δ := by
    intro i
    rw [abs_le]
    constructor <;> linarith [(hin i).1, (hin i).2]
  have hprod : (∏ i : Fin j, |points i.castSucc - α|) ≤ d.δ ^ j := by
    calc
      _ ≤ ∏ _ : Fin j, d.δ :=
        Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun i _ => herr i.castSucc)
      _ = _ := by simp
  have hbound := d.step_error_product hj points hpoints hin
  rw [Fin.prod_univ_castSucc] at hbound
  have hlastpos : 0 < |points (Fin.last j) - α| := abs_pos.mpr (sub_ne_zero.mpr hlast)
  calc
    _ ≤ D * d.L ^ (j + 2) * |points 0 - α| *
        ((∏ i : Fin j, |points i.castSucc - α|) * |points (Fin.last j) - α|) := hbound
    _ ≤ D * d.L ^ (j + 2) * d.δ * (d.δ ^ j * |points (Fin.last j) - α|) := by
      gcongr
      · exact mul_nonneg (mul_nonneg hD (pow_nonneg hL _)) d.delta_pos.le
      · exact herr 0
    _ = (D * d.L ^ (j + 2) * d.δ ^ (j + 1)) * |points (Fin.last j) - α| := by
      rw [pow_succ d.δ j]
      ring
    _ < (1 / 2 : ℝ) * |points (Fin.last j) - α| :=
      mul_lt_mul_of_pos_right (d.small j hj) hlastpos
    _ = _ := by ring

end KungTraubAppendices
