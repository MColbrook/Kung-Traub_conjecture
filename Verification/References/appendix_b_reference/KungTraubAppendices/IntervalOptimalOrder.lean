import appendix_b_reference.KungTraubAppendices.HermiteLocalOrder
import appendix_b_reference.KungTraub.EntireStageSequence
import appendix_b_reference.KungTraub.AnalyticRestriction

/-!
# The optimal universal exponent in the interval-local model

Appendix A's attainment predicate includes query admissibility on arbitrary
open real intervals. Specialization to the real line gives the analytic input
class of the main theorem.

The counterexample `KungTraub.scalar_entireCounterexample_constructed` and its
analytic restriction consequence therefore give the upper bound in the same
interval-local model.
-/

namespace KungTraubAppendices

/-- Interval-local universal order implies universal order on whole-line
analytic inputs, retaining the identical algorithm and real exponent. -/
theorem RealIntervalUniversalLocalOrder.analyticUniversalLocalOrder
    {n : ℕ} {A : KungTraub.RealAlgorithm n} {p : ℝ}
    (h : RealIntervalUniversalLocalOrder A p) :
    KungTraub.AnalyticUniversalLocalOrder A.run p := by
  sorry

/-- The real upper bound applies to every algorithm in the interval-local model. -/
theorem no_real_interval_universal_order_above {n : ℕ} (hn : 1 ≤ n)
    (A : KungTraub.RealAlgorithm n) (p : ℝ)
    (hp : (KungTraub.orderBound n : ℝ) < p) :
    ¬ RealIntervalUniversalLocalOrder A p := by
  sorry

/-- For n>=2 the actual inverse Hermite algorithm attains the universal
exponent, and every larger real exponent is impossible for every algorithm
with the same observation budget in the same interval-local input model. -/
theorem inverseHermite_optimal_universal_exponent (n : ℕ) (hn : 2 ≤ n) :
    RealIntervalUniversalLocalOrder (inverseHermiteAlgorithm n)
        (KungTraub.orderBound n : ℝ) ∧
      ∀ A : KungTraub.RealAlgorithm n, ∀ p : ℝ,
        (KungTraub.orderBound n : ℝ) < p → ¬ RealIntervalUniversalLocalOrder A p := by
  sorry

end KungTraubAppendices
