import KungTraub.Definitions
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic

/-!
# A nonzero leading coefficient excludes every larger local order

A normalized limit of order `m` with nonzero coefficient contradicts a uniform
punctured-neighbourhood bound of real order `p > m`. The argument applies on
both sides of zero and includes `m = 0`.

The proof uses Mathlib's continuity of real powers, `Real.rpow_sub_natCast`
and `le_of_tendsto_of_tendsto`.
-/

noncomputable section

open Filter
open scoped Topology

namespace KungTraubAppendices

/-- A nonzero normalized limit precludes a higher real-power bound on every
sufficiently close nonzero real point. No regularity of `F` is required. -/
theorem not_local_power_bound_of_normalized_limit {m : ℕ} {c : ℝ} (hc : c ≠ 0)
    {F : ℝ → ℝ}
    (hF : Tendsto (fun x => F x / x ^ m) (𝓝[≠] (0 : ℝ)) (𝓝 c))
    (p : ℝ) (hp : (m : ℝ) < p) :
    ¬ ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ x : ℝ, 0 < |x| → |x| < δ → |F x| ≤ C * Real.rpow |x| p := by
  sorry

/-- The same obstruction in the original local-order predicate at zero.
 -/
theorem not_localOrderAt_zero_of_normalized_limit {m : ℕ} {c : ℝ} (hc : c ≠ 0)
    {T : KungTraub.RealUpdate} {f : ℝ → ℝ}
    (hT : Tendsto (fun x => T f x / x ^ m) (𝓝[≠] (0 : ℝ)) (𝓝 c))
    (p : ℝ) (hp : (m : ℝ) < p) :
    ¬ KungTraub.LocalOrderAt T f 0 p := by
  sorry

end KungTraubAppendices
