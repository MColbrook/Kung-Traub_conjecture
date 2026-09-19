import KungTraub.Definitions
import KungTraubAppendices.ComplexDefinitions
import KungTraubAppendices.SharpnessDefinitions

/-! Reference statements for the principal real, grouped and complex results. -/

namespace KungTraub

theorem entire_counterexample {n : ℕ} (hn : 1 ≤ n) (A : RealAlgorithm n)
    (p : ℝ) (hp : (orderBound n : ℝ) < p) :
    EntireCounterexample A.run p := by
  sorry

theorem no_entire_universal_order_above {n : ℕ} (hn : 1 ≤ n) (A : RealAlgorithm n)
    (p : ℝ) (hp : (orderBound n : ℝ) < p) :
    ¬ EntireUniversalLocalOrder A.run p := by
  sorry

theorem no_universal_order_above {n : ℕ} (hn : 1 ≤ n) (A : RealAlgorithm n)
    (p : ℝ) (hp : (orderBound n : ℝ) < p) :
    ¬ AnalyticUniversalLocalOrder A.run p := by
  sorry

theorem grouped_entire_counterexample {k : ℕ} (hk : 1 ≤ k) (sizes : Fin k → ℕ)
    (hsize : ∀ j, 1 ≤ sizes j) (A : GroupedRealAlgorithm sizes)
    (p : ℝ) (hp : (groupedOrderBound sizes : ℝ) < p) :
    EntireCounterexample A.run p := by
  sorry

theorem no_grouped_entire_universal_order_above {k : ℕ} (hk : 1 ≤ k)
    (sizes : Fin k → ℕ) (hsize : ∀ j, 1 ≤ sizes j) (A : GroupedRealAlgorithm sizes)
    (p : ℝ) (hp : (groupedOrderBound sizes : ℝ) < p) :
    ¬ EntireUniversalLocalOrder A.run p := by
  sorry

theorem no_grouped_universal_order_above {k : ℕ} (hk : 1 ≤ k)
    (sizes : Fin k → ℕ) (hsize : ∀ j, 1 ≤ sizes j) (A : GroupedRealAlgorithm sizes)
    (p : ℝ) (hp : (groupedOrderBound sizes : ℝ) < p) :
    ¬ AnalyticUniversalLocalOrder A.run p := by
  sorry

theorem simultaneous_entire_counterexample {n : ℕ} (hn : 1 ≤ n)
    (A : RealAlgorithm n) :
    SimultaneousEntireCounterexample A.run (orderBound n : ℝ) := by
  sorry

end KungTraub

open Filter
open scoped Topology

namespace KungTraubAppendices

theorem complex_entire_counterexample {n : ℕ} (hn : 1 ≤ n)
    (A : ComplexAlgorithm n) (p : ℝ) (hp : (KungTraub.orderBound n : ℝ) < p) :
    ComplexEntireCounterexample A.run p := by
  sorry

theorem no_complex_universal_order_above {n : ℕ} (hn : 1 ≤ n)
    (A : ComplexAlgorithm n) (p : ℝ) (hp : (KungTraub.orderBound n : ℝ) < p) :
    ¬ ComplexUniversalLocalOrder A p := by
  sorry

theorem inverseHermite_universal_local_order (n : ℕ) (hn : 2 ≤ n) :
    RealIntervalUniversalLocalOrder (inverseHermiteAlgorithm n)
      (KungTraub.orderBound n : ℝ) := by
  sorry

theorem inverseHermite_exp_asymptotic (n : ℕ) (hn : 2 ≤ n) :
    Tendsto (fun x : ℝ =>
      (inverseHermiteAlgorithm n).run (fun t => Real.exp t - 1) x /
        x ^ KungTraub.orderBound n)
      (𝓝[≠] (0 : ℝ)) (𝓝 (sharpnessCoefficient (n - 1))) := by
  sorry

theorem inverseHermite_not_local_order_exp (n : ℕ) (hn : 2 ≤ n)
    (p : ℝ) (hp : (KungTraub.orderBound n : ℝ) < p) :
    ¬ KungTraub.LocalOrderAt (inverseHermiteAlgorithm n).run
      (fun t => Real.exp t - 1) 0 p := by
  sorry

end KungTraubAppendices
