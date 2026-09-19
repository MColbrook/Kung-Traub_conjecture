import KungTraubAppendices.HermiteLocalOrder
import KungTraub.EntireStageSequence
import KungTraub.AnalyticRestriction

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
  intro f hf α hroot
  obtain ⟨C, hC, δ, hδ, hlocal⟩ := h Set.univ isOpen_univ Set.ordConnected_univ
    f (fun t _ => hf t) α (Set.mem_univ α) hroot
  exact ⟨C, hC, δ, hδ, fun x hx hnear => (hlocal x hx hnear).2.2⟩

/-- The real upper bound applies to every algorithm in the interval-local model. -/
theorem no_real_interval_universal_order_above {n : ℕ} (hn : 1 ≤ n)
    (A : KungTraub.RealAlgorithm n) (p : ℝ)
    (hp : (KungTraub.orderBound n : ℝ) < p) :
    ¬ RealIntervalUniversalLocalOrder A p := by
  intro h
  have hcounter := KungTraub.scalar_entireCounterexample_constructed A (by omega) p hp
  exact hcounter.not_analyticUniversalLocalOrder h.analyticUniversalLocalOrder

/-- For n>=2 the actual inverse Hermite algorithm attains the universal
exponent, and every larger real exponent is impossible for every algorithm
with the same observation budget in the same interval-local input model. -/
theorem inverseHermite_optimal_universal_exponent (n : ℕ) (hn : 2 ≤ n) :
    RealIntervalUniversalLocalOrder (inverseHermiteAlgorithm n)
        (KungTraub.orderBound n : ℝ) ∧
      ∀ A : KungTraub.RealAlgorithm n, ∀ p : ℝ,
        (KungTraub.orderBound n : ℝ) < p → ¬ RealIntervalUniversalLocalOrder A p := by
  exact ⟨inverseHermite_universal_local_order n hn,
    fun A p hp => no_real_interval_universal_order_above (by omega) A p hp⟩

end KungTraubAppendices
