import KungTraubAppendices.DividedDifferences

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
  have hcont : ContinuousAt (iteratedDeriv n f) a := by
    rw [iteratedDeriv_eq_iterate]
    exact (hf.iterated_deriv n).continuousAt
  obtain ⟨r, hr, hrcont⟩ := Metric.continuousAt_iff.mp
    (hcont.div_const (n.factorial : ℝ)) ε hε
  obtain ⟨s, hs, hsanalytic⟩ := Metric.eventually_nhds_iff.mp hf.eventually_analyticAt
  let δ := min r s / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδr : δ < r := by dsimp [δ]; have := min_le_left r s; linarith
  have hδs : δ < s := by dsimp [δ]; have := min_le_right r s; linarith
  have hdist : ∀ z ∈ Icc (a - δ) (a + δ), dist z a ≤ δ := by
    intro z hz
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith [hz.1, hz.2]
  have hlocal : AnalyticOnNhd ℝ f (Icc (a - δ) (a + δ)) := by
    intro z hz
    exact hsanalytic ((hdist z hz).trans_lt hδs)
  refine ⟨δ, hδ, ?_⟩
  intro xs hlen hnodes
  have hxin : ∀ z ∈ xs, z ∈ Icc (a - δ) (a + δ) := by
    intro z hz
    have habs := abs_lt.mp (hnodes z hz)
    constructor <;> linarith [habs.1, habs.2]
  obtain ⟨c, hc, heq⟩ := confluentDividedDifference_mean_value hlocal xs hlen hxin
  rw [heq]
  exact hrcont ((hdist c hc).trans_lt hδr)

/-- Every finite family of nodes converging to `a` has the full confluent
limit, including arbitrary coincidences and any parameter filter. -/
theorem confluentDividedDifference_tendsto {X : Type*} {l : Filter X}
    (n : ℕ) {f : ℝ → ℝ} {a : ℝ} (hf : AnalyticAt ℝ f a)
    (x : X → Fin (n + 1) → ℝ)
    (hx : ∀ i, Tendsto (fun u => x u i) l (𝓝 a)) :
    Tendsto (fun u => confluentDividedDifference f (List.ofFn (x u))) l
      (𝓝 (iteratedDeriv n f a / (n.factorial : ℝ))) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hnear⟩ := confluentDividedDifference_near_diagonal n hf hε
  have hevent : ∀ᶠ u in l, ∀ i, dist (x u i) a < δ :=
    Filter.eventually_all.mpr (fun i => Metric.tendsto_nhds.mp (hx i) δ hδ)
  filter_upwards [hevent] with u hu
  apply hnear (List.ofFn (x u)) (by simp)
  intro z hz
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
  exact hu i

end KungTraubAppendices
