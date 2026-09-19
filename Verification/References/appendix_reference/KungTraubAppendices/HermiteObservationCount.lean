import appendix_reference.KungTraubAppendices.ExponentialAsymptotic

/-!
# Exact observation counts on nonstopping Hermite executions

This supplies the numerical count in Appendix A of Matthew J. Colbrook's
manuscript. The actual bounded tree makes one value observation for each
nonstopping tail stage, in addition to the initial value and derivative.
The proof adapts the exact history transport in `HermiteHistorySequence`
(`inverseHermiteTail_run_eq_history`), replacing output equality by the
actual `BoundedRealTree.observationCount`. No query is added at the final output.
The exponential case follows from eventual validity of the interpolation histories.
-/

noncomputable section

open Filter KungTraub
open scoped Topology

namespace KungTraubAppendices

/-- The actual tail uses every remaining value-observation slot when its
queried history values are nonzero. The unqueried final output is excluded. -/
theorem inverseHermiteTail_observationCount_eq (f : ℝ → ℝ) (x : ℝ)
    (remaining j : ℕ)
    (hnonzero : ∀ k, j + 1 ≤ k → k ≤ j + remaining →
      f (inverseHermiteHistory f k x (Fin.last k)) ≠ 0) :
    (inverseHermiteTail remaining j (fun i => f (inverseHermiteHistory f j x i))
      (inverseHermiteHistory f j x) (deriv f x)⁻¹
      (inverseHermiteHistory f (j + 1) x (Fin.last (j + 1)))).observationCount f =
        remaining := by
  sorry

/-- With a nonzero initial derivative and no zero queried value, the actual
method uses exactly `n` observations: two initial observations and `n−2` values. -/
theorem inverseHermiteTree_observationCount_eq (n : ℕ) (hn : 2 ≤ n)
    (f : ℝ → ℝ) (x : ℝ) (hd : deriv f x ≠ 0)
    (hnonzero : ∀ k, k < n - 1 →
      f (inverseHermiteHistory f k x (Fin.last k)) ≠ 0) :
    (inverseHermiteTree n x).observationCount f = n := by
  sorry

/-- On the exponential witness every sufficiently small nonzero starting
point uses the full observation budget, from either side of zero. -/
theorem inverseHermite_exp_eventually_observationCount_eq (n : ℕ) (hn : 2 ≤ n) :
    ∀ᶠ x in 𝓝[≠] (0 : ℝ),
      ((inverseHermiteMethod n) x).observationCount (fun t => Real.exp t - 1) = n := by
  sorry

end KungTraubAppendices
