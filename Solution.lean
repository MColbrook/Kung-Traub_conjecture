import KungTraub.EntireStageSequence
import KungTraub.AnalyticRestriction
import KungTraub.GroupedEntireWitness

/-!
# Kung–Traub upper bounds

The scalar witnesses follow from the finite adversary, compatible Gaussian stages,
and their entire limit. The whole-line real-analytic consequence follows by
restriction. The grouped construction retains the prescribed schedule and its
exact exponent.

Source: Matthew J. Colbrook, *Adversarial Wronskians: A proof of the Kung–Traub
conjecture*, the main theorem, its simultaneous-failure strengthening, and the
corollary for prescribed groups.
-/

namespace KungTraub

theorem entire_counterexample {n : ℕ} (hn : 1 ≤ n) (A : RealAlgorithm n)
    (p : ℝ) (hp : (orderBound n : ℝ) < p) :
    EntireCounterexample A.run p :=
  scalar_entireCounterexample_constructed A hn p hp

theorem no_entire_universal_order_above {n : ℕ} (hn : 1 ≤ n) (A : RealAlgorithm n)
    (p : ℝ) (hp : (orderBound n : ℝ) < p) :
    ¬ EntireUniversalLocalOrder A.run p :=
  (entire_counterexample hn A p hp).not_entireUniversalLocalOrder

theorem no_universal_order_above {n : ℕ} (hn : 1 ≤ n) (A : RealAlgorithm n)
    (p : ℝ) (hp : (orderBound n : ℝ) < p) :
    ¬ AnalyticUniversalLocalOrder A.run p :=
  (entire_counterexample hn A p hp).not_analyticUniversalLocalOrder

theorem grouped_entire_counterexample {k : ℕ} (hk : 1 ≤ k) (sizes : Fin k → ℕ)
    (hsize : ∀ j, 1 ≤ sizes j) (A : GroupedRealAlgorithm sizes)
    (p : ℝ) (hp : (groupedOrderBound sizes : ℝ) < p) :
    EntireCounterexample A.run p :=
  grouped_entireCounterexample_constructed A hk hsize p hp

theorem no_grouped_entire_universal_order_above {k : ℕ} (hk : 1 ≤ k)
    (sizes : Fin k → ℕ) (hsize : ∀ j, 1 ≤ sizes j) (A : GroupedRealAlgorithm sizes)
    (p : ℝ) (hp : (groupedOrderBound sizes : ℝ) < p) :
    ¬ EntireUniversalLocalOrder A.run p :=
  (grouped_entire_counterexample hk sizes hsize A p hp).not_entireUniversalLocalOrder

theorem no_grouped_universal_order_above {k : ℕ} (hk : 1 ≤ k)
    (sizes : Fin k → ℕ) (hsize : ∀ j, 1 ≤ sizes j) (A : GroupedRealAlgorithm sizes)
    (p : ℝ) (hp : (groupedOrderBound sizes : ℝ) < p) :
    ¬ AnalyticUniversalLocalOrder A.run p :=
  (grouped_entire_counterexample hk sizes hsize A p hp).not_analyticUniversalLocalOrder

theorem simultaneous_entire_counterexample {n : ℕ} (hn : 1 ≤ n)
    (A : RealAlgorithm n) :
    SimultaneousEntireCounterexample A.run (orderBound n : ℝ) :=
  scalar_simultaneousEntireCounterexample_constructed A hn

end KungTraub
