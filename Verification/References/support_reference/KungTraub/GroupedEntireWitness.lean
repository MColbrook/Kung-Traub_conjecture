import support_reference.KungTraub.GroupedStageConstruction

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
    Nonempty (GaussianAdversarialStages A.flatten (groupedOrderBound sizes : ℝ) exponent) := by
  sorry

/-- A full entire counterexample for the original grouped execution. -/
theorem grouped_entireCounterexample_constructed {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedRealAlgorithm sizes) (hk : 0 < k) (hsizes : ∀ i, 0 < sizes i)
    (p : ℝ) (hp : (groupedOrderBound sizes : ℝ) < p) :
    EntireCounterexample A.run p := by
  sorry

/-- One entire input and one start sequence work for all larger grouped exponents. -/
theorem grouped_simultaneousEntireCounterexample_constructed {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedRealAlgorithm sizes) (hk : 0 < k) (hsizes : ∀ i, 0 < sizes i) :
    SimultaneousEntireCounterexample A.run (groupedOrderBound sizes : ℝ) := by
  sorry

end KungTraub
