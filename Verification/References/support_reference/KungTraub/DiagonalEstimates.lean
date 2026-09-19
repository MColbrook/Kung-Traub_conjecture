import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic

/-!
# Budget, scale and error estimates for the entire construction

Section 4 of Matthew J. Colbrook's manuscript uses geometric correction budgets,
a sufficiently small scale for each real exponent, and stage inequalities that
force the error ratio to tend to infinity.

The series proofs reuse Mathlib's `le_geom`, `summable_geometric_two` and
`tsum_geometric_two`. Scale selection uses Mathlib's continuity of positive real powers;
the limit arguments use its reciprocal limits and ordered-filter comparison lemmas.
Indices are zero-based here: index `s` denotes the paper's positive stage `s + 1`.
-/

noncomputable section

open Filter Set
open scoped BigOperators Topology

namespace KungTraub

/-- A budget which decreases by at least a factor of two is bounded by its geometric
majorant. Index zero corresponds to the first positive correction budget in the paper. -/
theorem budget_le_geometric {b : ℕ → ℝ}
    (hstep : ∀ n, b (n + 1) ≤ b n / 2) (n : ℕ) :
    b n ≤ b 0 * (1 / 2 : ℝ) ^ n := by
  sorry

/-- The nonnegative geometric budgets are summable. -/
theorem summable_budget {b : ℕ → ℝ} (hpos : ∀ n, 0 ≤ b n)
    (hstep : ∀ n, b (n + 1) ≤ b n / 2) : Summable b := by
  sorry

/-- The sum of all correction budgets is at most twice the initial budget. -/
theorem tsum_budget_le_twice {b : ℕ → ℝ} (hpos : ∀ n, 0 ≤ b n)
    (hstep : ∀ n, b (n + 1) ≤ b n / 2) : (∑' n, b n) ≤ 2 * b 0 := by
  sorry

/-- Every tail, including its first term, is bounded by twice that first term.
Offset `s + 1` gives the remaining budgets after zero-based stage `s`. -/
theorem tsum_budget_tail_le_twice {b : ℕ → ℝ} (hpos : ∀ n, 0 ≤ b n)
    (hstep : ∀ n, b (n + 1) ≤ b n / 2) (s : ℕ) :
    (∑' j, b (j + s)) ≤ 2 * b s := by
  sorry

/-- The paper's initial budget `1/32` gives a total correction budget at most `1/16`. -/
theorem tsum_budget_le_one_sixteenth {b : ℕ → ℝ} (hpos : ∀ n, 0 ≤ b n)
    (hstep : ∀ n, b (n + 1) ≤ b n / 2) (hfirst : b 0 ≤ 1 / 32) :
    (∑' n, b n) ≤ 1 / 16 := by
  sorry

/-- Positive error and scale leave a positive choice for the next correction budget. -/
theorem exists_next_budget {b E ε : ℝ} (hb : 0 < b) (hE : 0 < E) (hε : 0 < ε) :
    ∃ bnext : ℝ, 0 < bnext ∧ bnext ≤ b / 2 ∧ bnext ≤ E / 32 ∧ bnext ≤ ε / 32 := by
  sorry

/-- The next budget converts the root-displacement bound into the two relative bounds
used to preserve the old error and the starting distance. -/
theorem root_displacement_of_budget {α a bnext E ε : ℝ}
    (hroot : |α - a| ≤ 4 * bnext) (hE : bnext ≤ E / 32)
    (hε : bnext ≤ ε / 32) : |α - a| ≤ E / 8 ∧ |α - a| ≤ ε / 8 := by
  sorry

/-- For real `p > B`, every positive threshold contains a scale satisfying the paper's
error amplification inequality. Neither exponent is restricted to an integer. -/
theorem exists_small_scale {B p c s δ : ℝ} (hp : B < p) (hc : 0 < c)
    (hs : 0 < s) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ s * (2 * ε) ^ p ≤ (c / 2) * ε ^ B := by
  sorry

/-- Scale selection at zero-based stage `s`, retaining the independent positive threshold
and the paper's exact caps `1/(s+1)` and `1/4`. -/
theorem exists_stage_scale {B p c threshold : ℝ} (hp : B < p) (hc : 0 < c)
    (hthreshold : 0 < threshold) (s : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < threshold ∧ ε < 1 / ((s : ℝ) + 1) ∧ ε < 1 / 4 ∧
      ((s : ℝ) + 1) * (2 * ε) ^ p ≤ (c / 2) * ε ^ B := by
  sorry

/-- The two root perturbation bounds give the precise final distance constants and retain
at least half the stage error. -/
theorem stage_root_error_bounds {ε x y a α : ℝ}
    (hleft : (3 / 4 : ℝ) * ε ≤ x - a) (hright : x - a ≤ (5 / 4 : ℝ) * ε)
    (hscale : |α - a| ≤ ε / 8) (herror : |α - a| ≤ |y - a| / 8) :
    (5 / 8 : ℝ) * ε ≤ x - α ∧ x - α ≤ (11 / 8 : ℝ) * ε ∧
      |y - a| / 2 ≤ |y - α| := by
  sorry

/-- The complete scalar inequality at one stage, including its nonzero starting distance.
Its assumptions are precisely stage error, root displacement and scale inequalities. -/
theorem stage_error_ratio_lower_bound {ε x y a α B p c s : ℝ}
    (hε : 0 < ε) (hp : 0 ≤ p)
    (hleft : (3 / 4 : ℝ) * ε ≤ x - a) (hright : x - a ≤ (5 / 4 : ℝ) * ε)
    (hscale : |α - a| ≤ ε / 8) (htail : |α - a| ≤ |y - a| / 8)
    (herror : c * ε ^ B ≤ |y - a|)
    (hchoice : s * (2 * ε) ^ p ≤ (c / 2) * ε ^ B) :
    x ≠ α ∧ s ≤ |y - α| / |x - α| ^ p := by
  sorry

/-- The final stage inequalities force nonroot starts converging to the limiting root and
error ratios tending to infinity. -/
theorem stage_bounds_imply_divergence
    {ε x y a c : ℕ → ℝ} {α B p : ℝ} (hp : 0 ≤ p)
    (hε : ∀ s, 0 < ε s) (hsmall : ∀ s, ε s < 1 / ((s : ℝ) + 1))
    (hleft : ∀ s, (3 / 4 : ℝ) * ε s ≤ x s - a s)
    (hright : ∀ s, x s - a s ≤ (5 / 4 : ℝ) * ε s)
    (hscale : ∀ s, |α - a s| ≤ ε s / 8)
    (htail : ∀ s, |α - a s| ≤ |y s - a s| / 8)
    (herror : ∀ s, c s * ε s ^ B ≤ |y s - a s|)
    (hchoice : ∀ s : ℕ, ((s : ℝ) + 1) * (2 * ε s) ^ p ≤ (c s / 2) * ε s ^ B) :
    (∀ s, x s ≠ α) ∧ Tendsto x atTop (𝓝 α) ∧
      Tendsto (fun s => |y s - α| / |x s - α| ^ p) atTop atTop := by
  sorry

/-- Increasing the exponent increases an error ratio when its positive distance is at
most one. This is the comparison used for simultaneous failure of larger orders. -/
theorem error_ratio_mono_exponent {e d p q : ℝ} (he : 0 ≤ e) (hd : 0 < d)
    (hdone : d ≤ 1) (hpq : p ≤ q) : e / d ^ p ≤ e / d ^ q := by
  sorry

/-- The positive-stage exponents `B + 1/(s+1)` eventually lie below every fixed `p > B`. -/
theorem eventually_stage_exponent_le {B p : ℝ} (hp : B < p) :
    ∀ᶠ s : ℕ in atTop, B + 1 / ((s : ℝ) + 1) ≤ p := by
  sorry

/-- One sequence of errors and distances satisfying the moving-exponent inequalities
has a divergent ratio for every fixed larger exponent, with unchanged witnesses. -/
theorem simultaneous_ratio_divergence {e d : ℕ → ℝ} {B : ℝ}
    (he : ∀ s, 0 ≤ e s) (hd : ∀ s, 0 < d s)
    (hdone : ∀ᶠ s in atTop, d s ≤ 1)
    (hstage : ∀ s : ℕ, (s : ℝ) + 1 ≤ e s / d s ^ (B + 1 / ((s : ℝ) + 1)))
    (p : ℝ) (hp : B < p) : Tendsto (fun s => e s / d s ^ p) atTop atTop := by
  sorry

end KungTraub
