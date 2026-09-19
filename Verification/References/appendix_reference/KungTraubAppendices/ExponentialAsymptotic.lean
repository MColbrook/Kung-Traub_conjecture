import appendix_reference.KungTraubAppendices.HermiteHistorySequence
import appendix_reference.KungTraubAppendices.ExponentialHermiteStep
import appendix_reference.KungTraubAppendices.AsymptoticSeparation

/-! Exact leading coefficients for the actual finite observation histories. -/

noncomputable section
open Filter KungTraub
open scoped Topology
namespace KungTraubAppendices

/-- All entries of the actual unstopped history have the asymptotics,
with eventual distinctness derived at each preceding stage. -/
theorem inverseHermiteHistory_exp_asymptotic (j : ℕ) :
    ∀ i : Fin (j + 1), Tendsto (fun x : ℝ =>
      inverseHermiteHistory (fun t => Real.exp t - 1) j x i / x ^ (2 ^ i.val))
      (𝓝[≠] (0 : ℝ)) (𝓝 (sharpnessCoefficient i.val)) := by
  sorry

/-- The unstopped exponential history eventually has no zero entries and
has distinct points, simultaneously for every entry of the finite history. -/
theorem inverseHermiteHistory_exp_eventually_valid (j : ℕ) :
    ∀ᶠ x in 𝓝[≠] (0 : ℝ),
      Function.Injective (inverseHermiteHistory (fun t => Real.exp t - 1) j x) ∧
      ∀ i, inverseHermiteHistory (fun t => Real.exp t - 1) j x i ≠ 0 := by
  sorry

/-- Eventual nonvanishing excludes every early-return branch of the actual
exponential execution, while its final output remains unqueried. -/
theorem inverseHermite_exp_eventually_run_eq_history (n : ℕ) (hn : 2 ≤ n) :
    ∀ᶠ x in 𝓝[≠] (0 : ℝ),
      (inverseHermiteAlgorithm n).run (fun t => Real.exp t - 1) x =
        inverseHermiteHistory (fun t => Real.exp t - 1) (n - 1) x (Fin.last (n - 1)) := by
  sorry

/-- The exact leading coefficient of the same actual algorithm on the
exponential example, with a two-sided punctured limit. -/
theorem inverseHermite_exp_asymptotic (n : ℕ) (hn : 2 ≤ n) :
    Tendsto (fun x : ℝ =>
      (inverseHermiteAlgorithm n).run (fun t => Real.exp t - 1) x /
        x ^ KungTraub.orderBound n)
      (𝓝[≠] (0 : ℝ)) (𝓝 (sharpnessCoefficient (n - 1))) := by
  sorry

end KungTraubAppendices
