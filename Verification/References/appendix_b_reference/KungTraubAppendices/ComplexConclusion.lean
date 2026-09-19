import appendix_b_reference.KungTraubAppendices.ComplexStageSequence
import appendix_b_reference.KungTraubAppendices.ComplexConsequences

/-!
# Appendix B: the complex upper bound

The finite adversary, polynomial stages and entire limit give a fixed entire
counterexample for each exponent above the scalar bound. This rules out a
larger universal order on arbitrary open holomorphic domains.
-/

noncomputable section
namespace KungTraubAppendices

/-- One fixed entire counterexample for each exponent above the scalar bound. -/
theorem complex_entire_counterexample {n : ℕ} (hn : 1 ≤ n)
    (A : ComplexAlgorithm n) (p : ℝ) (hp : (KungTraub.orderBound n : ℝ) < p) :
    ComplexEntireCounterexample A.run p := by
  sorry

/-- Consequently no larger universal order holds on arbitrary open holomorphic domains. -/
theorem no_complex_universal_order_above {n : ℕ} (hn : 1 ≤ n)
    (A : ComplexAlgorithm n) (p : ℝ) (hp : (KungTraub.orderBound n : ℝ) < p) :
    ¬ ComplexUniversalLocalOrder A p := by
  sorry

end KungTraubAppendices
