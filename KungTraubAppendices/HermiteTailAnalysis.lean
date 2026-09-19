import KungTraubAppendices.HermiteHistory
import KungTraubAppendices.HermiteOrderConstants
import KungTraubAppendices.RealExecutionDomain

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
  exact (d.step_error_product hj points hpoints hin).trans
    (hermiteOrderConstant_product_bound
      (le_trans zero_le_one (one_le_inverseHermiteDerivativeBound _ _ _ _))
      (le_trans zero_le_one d.linear_constant_ge_one) (abs_nonneg _) j
      (fun i => |points i - α|) (fun i => abs_nonneg _) hbound)

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
  induction remaining generalizing j with
  | zero =>
    exact ⟨trivial, d.step_order hbudget points hpoints hin hbound⟩
  | succ remaining ih =>
    let next := (hermiteWithDerivative Finset.univ (fun i => f (points i)) points 0
      (deriv f (points 0))⁻¹).eval 0
    have hj : j ≤ n - 2 := by omega
    have hnext := d.step_mem hj points hpoints hin hlast
    have hnextU := d.interval_subset (d.closed_neighborhood_subset hnext)
    have horder := d.step_order hj points hpoints hin hbound
    have hD : 0 < inverseHermiteDerivativeBound n hn d.g (Icc (-d.r) d.r) :=
      lt_of_lt_of_le zero_lt_one (one_le_inverseHermiteDerivativeBound _ _ _ _)
    have hL : 0 < d.L := lt_of_lt_of_le zero_lt_one d.linear_constant_ge_one
    change (next ∈ U ∧ realTreeExecutionIn
      (if f next = 0 then (BoundedRealTree.stop (n := remaining) next) else _) f U) ∧
      |(if f next = 0 then (BoundedRealTree.stop (n := remaining) next) else _).run f - α| ≤ _
    simp only [RealQuery.answer, iteratedDeriv_zero]
    by_cases hz : f next = 0
    · have heq : next = α := (d.zero_iff hnext).mp hz
      simp only [if_pos hz, realTreeExecutionIn, BoundedRealTree.run]
      refine ⟨⟨hnextU, trivial⟩, ?_⟩
      rw [heq, sub_self, abs_zero]
      exact mul_nonneg (hermiteOrderConstant_pos hD hL _).le (pow_nonneg (abs_nonneg _) _)
    · simp only [if_neg hz]
      let extended : Fin (j + 2) → ℝ := Fin.snoc points next
      have hextIn : ∀ i, extended i ∈ Icc (α - d.δ) (α + d.δ) := by
        intro i
        refine Fin.lastCases ?_ (fun k => ?_) i
        · simpa only [extended, Fin.snoc_last] using hnext
        · simpa only [extended, Fin.snoc_castSucc] using hin k
      have hextLast : extended (Fin.last (j + 1)) ≠ α := by
        simpa only [extended, Fin.snoc_last] using (d.zero_iff hnext).not.mp hz
      have hextMin : ∀ i, |extended (Fin.last (j + 1)) - α| ≤ |extended i - α| := by
        intro i
        refine Fin.lastCases ?_ (fun k => ?_) i
        · exact le_rfl
        · simpa only [extended, Fin.snoc_last, Fin.snoc_castSucc] using
            (d.step_lt_each hj points hpoints hin hlast hmin k).le
      have hextZero : extended 0 = points 0 := Fin.snoc_apply_zero _ _
      have hextBound : ∀ i, |extended i - α| ≤
          hermiteOrderConstant (inverseHermiteDerivativeBound n hn d.g (Icc (-d.r) d.r))
            d.L i.val * |extended 0 - α| ^ (2 ^ i.val) := by
        intro i
        rw [hextZero]
        refine Fin.lastCases ?_ (fun k => ?_) i
        · simpa only [extended, Fin.snoc_last, Fin.val_last] using horder
        · simpa only [extended, Fin.snoc_castSucc, Fin.val_castSucc] using hbound k
      have hex := ih (j + 1) (by omega) extended
        (d.step_snoc_injective hj points hpoints hin hlast hmin)
        hextIn hextLast hextMin hextBound
      have hvalues : Fin.snoc (fun i => f (points i)) (f next) =
          fun i => f (extended i) := by
        simpa only [Function.comp_def, extended] using (Fin.comp_snoc f points next).symm
      rw [hextZero] at hex
      have hindex : j + 1 + remaining + 1 = j + (remaining + 1) + 1 := by omega
      rw [hindex] at hex
      rw [← hvalues] at hex
      exact And.intro (And.intro hnextU hex.1) hex.2

end KungTraubAppendices
