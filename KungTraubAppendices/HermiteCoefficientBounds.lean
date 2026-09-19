import KungTraubAppendices.ConfluentLimit
import KungTraubAppendices.HermiteUniformBound

/-! Bounds and limits for exactly the node pattern in Appendix A. -/

noncomputable section

open Set Filter
open scoped Topology

namespace KungTraubAppendices

/-- The uniform constant bounds the canonical coefficient, including
coincidences among any of the value nodes. -/
theorem hermiteDividedDifference_le_uniform_bound (n : ℕ) (hn : 2 ≤ n)
    {g : ℝ → ℝ} {a b : ℝ} (hg : AnalyticOnNhd ℝ g (Icc a b))
    (hzero : (0 : ℝ) ∈ Icc a b) {j : ℕ} (hj : j ≤ n - 2)
    (nodes : Fin (j + 1) → ℝ) (hin : ∀ i, nodes i ∈ Icc a b) :
    |confluentDividedDifference g (0 :: nodes 0 :: List.ofFn nodes)| ≤
      inverseHermiteDerivativeBound n hn g (Icc a b) := by
  apply confluentDividedDifference_abs_le (n := j + 2) hg _ (by simp)
  · intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hzero
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hin 0
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
    exact hin i
  · intro c hc
    exact normalized_derivative_le_inverseHermiteDerivativeBound n hn
      isCompact_Icc hg hj hc

/-- The exact coefficient in the Hermite remainder has the coalescing limit of derivative order `j+2`, divided by `(j+2)!`. -/
theorem hermiteDividedDifference_tendsto {X : Type*} {l : Filter X}
    (j : ℕ) {g : ℝ → ℝ} (hg : AnalyticAt ℝ g 0)
    (nodes : X → Fin (j + 1) → ℝ)
    (hnodes : ∀ i, Tendsto (fun u => nodes u i) l (𝓝 (0 : ℝ))) :
    Tendsto (fun u => confluentDividedDifference g (0 :: nodes u 0 :: List.ofFn (nodes u))) l
      (𝓝 (iteratedDeriv (j + 2) g 0 / ((j + 2).factorial : ℝ))) := by
  let x : X → Fin (j + 3) → ℝ := fun u => Fin.cons 0 (Fin.cons (nodes u 0) (nodes u))
  have hnodes' : ∀ i : Fin (j + 3), Tendsto (fun u => x u i) l (𝓝 (0 : ℝ)) := by
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · exact tendsto_const_nhds
    · refine Fin.cases ?_ (fun k => ?_) k
      · exact hnodes 0
      · exact hnodes k
  have h := confluentDividedDifference_tendsto (j + 2) hg x hnodes'
  simpa only [x, List.ofFn_cons] using h

end KungTraubAppendices
