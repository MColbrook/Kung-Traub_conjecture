import appendix_reference.KungTraubAppendices.HermiteHistory
import appendix_reference.KungTraubAppendices.HermiteOrderConstants
import appendix_reference.KungTraubAppendices.RealExecutionDomain

/-! Domain and error bounds along the actual answer branches of the tail. -/

noncomputable section
open Set KungTraub
namespace KungTraubAppendices

/-- One actual interpolation step propagates the fixed uniform order constants. -/
theorem InverseHermiteLocalData.step_order {n : ℕ} {hn : 2 ≤ n}
    {U : Set ℝ} {f : ℝ → ℝ} {α : ℝ} (d : InverseHermiteLocalData n hn U f α)
    {j : ℕ} (hj : j ≤ n - 2) (points : Fin (j + 1) → ℝ)
    (hpoints : Function.Injective points)
    (hin : ∀ i, points i ∈ Icc (α - d.δ) (α + d.δ))
    (hbound : ∀ i, |points i - α| ≤
      hermiteOrderConstant (inverseHermiteDerivativeBound n hn d.g (Icc (-d.r) d.r))
        d.L i.val * |points 0 - α| ^ (2 ^ i.val)) :
    |(hermiteWithDerivative Finset.univ (fun i => f (points i)) points 0
      (deriv f (points 0))⁻¹).eval 0 - α| ≤
      hermiteOrderConstant (inverseHermiteDerivativeBound n hn d.g (Icc (-d.r) d.r))
        d.L (j + 1) * |points 0 - α| ^ (2 ^ (j + 1)) := by
  sorry

set_option maxHeartbeats 800000 in
/-- The actual tail remains admissible and satisfies the final order estimate,
including early stopping and the final unqueried output. -/
theorem InverseHermiteLocalData.tail_analysis {n : ℕ} {hn : 2 ≤ n}
    {U : Set ℝ} {f : ℝ → ℝ} {α : ℝ} (d : InverseHermiteLocalData n hn U f α)
    (remaining j : ℕ) (hbudget : j + remaining ≤ n - 2)
    (points : Fin (j + 1) → ℝ) (hpoints : Function.Injective points)
    (hin : ∀ i, points i ∈ Icc (α - d.δ) (α + d.δ))
    (hlast : points (Fin.last j) ≠ α)
    (hmin : ∀ i, |points (Fin.last j) - α| ≤ |points i - α|)
    (hbound : ∀ i, |points i - α| ≤
      hermiteOrderConstant (inverseHermiteDerivativeBound n hn d.g (Icc (-d.r) d.r))
        d.L i.val * |points 0 - α| ^ (2 ^ i.val)) :
    let H := hermiteWithDerivative Finset.univ (fun i => f (points i)) points 0
      (deriv f (points 0))⁻¹
    let tree := inverseHermiteTail remaining j (fun i => f (points i)) points
      (deriv f (points 0))⁻¹ (H.eval 0)
    realTreeExecutionIn tree f U ∧
      |tree.run f - α| ≤
        hermiteOrderConstant (inverseHermiteDerivativeBound n hn d.g (Icc (-d.r) d.r))
          d.L (j + remaining + 1) * |points 0 - α| ^ (2 ^ (j + remaining + 1)) := by
  sorry

end KungTraubAppendices
