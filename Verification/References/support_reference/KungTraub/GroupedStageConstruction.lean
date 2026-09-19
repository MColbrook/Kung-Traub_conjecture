import support_reference.KungTraub.EntireStageSequence
import support_reference.KungTraub.GroupedFiniteAdversary
import support_reference.KungTraub.GroupedFlattening

/-!
# Gaussian stage construction for prescribed groups

The actual grouped finite adversary supplies the next Gaussian correction
with the exact grouped product exponent. Flattening is used only to feed the
proved generic history recursion: actual outputs and derivative queries are
transferred by the exact flattening equalities.
-/

noncomputable section
open scoped BigOperators ContDiff
namespace KungTraub

theorem exists_grouped_gaussianStageChoice {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedRealAlgorithm sizes) (hk : 0 < k) (hsizes : ∀ i, 0 < sizes i)
    (P : Polynomial ℝ) (Z : Finset ℝ) (orders : ℝ → ℕ) {a b R p : ℝ}
    (hbase : ∀ t : ℝ, |(t + gaussianPolynomial P t) - t| ≤ 1 / 16 ∧
      (15 : ℝ) / 16 ≤ deriv (fun y => y + gaussianPolynomial P y) t ∧
      deriv (fun y => y + gaussianPolynomial P y) t ≤ 17 / 16)
    (ha : |a| ≤ 1 / 4) (hroot : a + gaussianPolynomial P a = 0)
    (hold : ∀ z ∈ Z, z + gaussianPolynomial P z ≠ 0)
    (hb : 0 < b) (hbsmall : b ≤ 1 / 16) (hR : 0 ≤ R)
    (hp : (groupedOrderBound sizes : ℝ) < p) (s : ℕ) :
    Nonempty (GaussianStageChoice A.flatten P Z orders a b R (groupedOrderBound sizes : ℝ) p s) := by
  sorry


/-- Every stage exponent above the exact grouped bound admits the concrete
Gaussian extension required by the generic history construction. -/
theorem grouped_gaussianStageExtensionAvailable {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedRealAlgorithm sizes) (hk : 0 < k) (hsizes : ∀ i, 0 < sizes i)
    (exponent : ℕ → ℝ) (hp : ∀ s, (groupedOrderBound sizes : ℝ) < exponent s) :
    GaussianStageExtensionAvailable A.flatten (groupedOrderBound sizes : ℝ) exponent := by
  sorry

end KungTraub

