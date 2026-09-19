import appendix_reference.KungTraubAppendices.DividedDifferences

/-!
# Coalescing-node limits

The mean-value point belongs to an interval that shrinks with all the nodes.
Only analyticity near the limiting point is used. Repetitions and approaches
from either side are allowed throughout.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace KungTraubAppendices

/-- Uniform continuity at the full diagonal. -/
theorem confluentDividedDifference_near_diagonal (n : ℕ) {f : ℝ → ℝ} {a : ℝ}
    (hf : AnalyticAt ℝ f a) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ xs : List ℝ, xs.length = n + 1 →
      (∀ z ∈ xs, |z - a| < δ) →
      |confluentDividedDifference f xs -
        iteratedDeriv n f a / (n.factorial : ℝ)| < ε := by
  sorry

/-- Every finite family of nodes converging to `a` has the full confluent
limit, including arbitrary coincidences and any parameter filter. -/
theorem confluentDividedDifference_tendsto {X : Type*} {l : Filter X}
    (n : ℕ) {f : ℝ → ℝ} {a : ℝ} (hf : AnalyticAt ℝ f a)
    (x : X → Fin (n + 1) → ℝ)
    (hx : ∀ i, Tendsto (fun u => x u i) l (𝓝 a)) :
    Tendsto (fun u => confluentDividedDifference f (List.ofFn (x u))) l
      (𝓝 (iteratedDeriv n f a / (n.factorial : ℝ))) := by
  sorry

end KungTraubAppendices
