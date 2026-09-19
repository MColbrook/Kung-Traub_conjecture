import KungTraub.GroupedStageConstruction

/-!
# Entire witnesses for prescribed groups

The grouped entire construction in Matthew J. Colbrook's manuscript. The grouped finite adversary supplies its exact exponent
to the common history recursion. Exact equality of the flattened and grouped
executions then transfers the full witness, with no change of exponent.
-/

noncomputable section

namespace KungTraub

/-- Actual grouped stages, retaining the prescribed-group exponent. -/
theorem exists_grouped_gaussianAdversarialStages {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedRealAlgorithm sizes) (hk : 0 < k) (hsizes : ∀ i, 0 < sizes i)
    (exponent : ℕ → ℝ) (hp : ∀ s, (groupedOrderBound sizes : ℝ) < exponent s) :
    Nonempty (GaussianAdversarialStages A.flatten (groupedOrderBound sizes : ℝ) exponent) :=
  exists_gaussianAdversarialStages_of_extension
    (grouped_gaussianStageExtensionAvailable A hk hsizes exponent hp)

/-- A full entire counterexample for the original grouped execution. -/
theorem grouped_entireCounterexample_constructed {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedRealAlgorithm sizes) (hk : 0 < k) (hsizes : ∀ i, 0 < sizes i)
    (p : ℝ) (hp : (groupedOrderBound sizes : ℝ) < p) :
    EntireCounterexample A.run p := by
  let D := Classical.choice
    (exists_grouped_gaussianAdversarialStages A hk hsizes (fun _ => p) (fun _ => hp))
  have h := entireCounterexample_of_gaussian_stages D
    ((Nat.cast_nonneg (groupedOrderBound sizes)).trans hp.le)
  have hrun : A.flatten.run = A.run := funext (fun f => funext (A.flatten_run_eq f))
  rw [hrun] at h
  exact h

/-- One entire input and one start sequence work for all larger grouped exponents. -/
theorem grouped_simultaneousEntireCounterexample_constructed {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedRealAlgorithm sizes) (hk : 0 < k) (hsizes : ∀ i, 0 < sizes i) :
    SimultaneousEntireCounterexample A.run (groupedOrderBound sizes : ℝ) := by
  have hp : ∀ s : ℕ, (groupedOrderBound sizes : ℝ) <
      (groupedOrderBound sizes : ℝ) + 1 / ((s : ℝ) + 1) := by
    intro s
    have h : (0 : ℝ) < 1 / ((s : ℝ) + 1) := by positivity
    linarith
  let D := Classical.choice (exists_grouped_gaussianAdversarialStages A hk hsizes
    (fun s => (groupedOrderBound sizes : ℝ) + 1 / ((s : ℝ) + 1)) hp)
  have h := simultaneousEntireCounterexample_of_gaussian_stages D (Nat.cast_nonneg _)
  have hrun : A.flatten.run = A.run := funext (fun f => funext (A.flatten_run_eq f))
  rw [hrun] at h
  exact h

end KungTraub
