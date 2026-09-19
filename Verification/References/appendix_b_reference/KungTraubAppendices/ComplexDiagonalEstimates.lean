import appendix_b_reference.KungTraub.DiagonalEstimates
import Mathlib.Analysis.Complex.Basic

/-!
# Complex stage-to-limit error estimates

The norm estimates follow `KungTraub.DiagonalEstimates`, with Appendix B's
constants. Positive starting distances give nonroot starts, and the distance
estimate gives convergence.

Geometric-budget, positive-scale and real-power estimates are reused from that
module. Index `s` corresponds to the positive stage `s+1` in the paper.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace KungTraubAppendices

/-- Reuse the real budget arithmetic at the complex root-displacement norm. -/
theorem complex_root_displacement_of_budget {α a : ℂ} {bnext E ε : ℝ}
    (hroot : ‖α - a‖ ≤ 4 * bnext) (hE : bnext ≤ E / 32)
    (hε : bnext ≤ ε / 32) : ‖α - a‖ ≤ E / 8 ∧ ‖α - a‖ ≤ ε / 8 := by
  sorry

/-- The exact relative tail bounds preserve the starting distance and at least
half the old error. -/
theorem complex_stage_root_error_bounds {ε : ℝ} {x y a α : ℂ}
    (hleft : (3 / 4 : ℝ) * ε ≤ ‖x - a‖) (hright : ‖x - a‖ ≤ (5 / 4 : ℝ) * ε)
    (hscale : ‖α - a‖ ≤ ε / 8) (herror : ‖α - a‖ ≤ ‖y - a‖ / 8) :
    (5 / 8 : ℝ) * ε ≤ ‖x - α‖ ∧ ‖x - α‖ ≤ (11 / 8 : ℝ) * ε ∧
      ‖y - a‖ / 2 ≤ ‖y - α‖ := by
  sorry

/-- The complete one-stage estimate keeps the real exponents and derives a
nonzero starting distance before comparing the real-power denominators. -/
theorem complex_stage_error_ratio_lower_bound {ε B p c s : ℝ} {x y a α : ℂ}
    (hε : 0 < ε) (hp : 0 ≤ p)
    (hleft : (3 / 4 : ℝ) * ε ≤ ‖x - a‖) (hright : ‖x - a‖ ≤ (5 / 4 : ℝ) * ε)
    (hscale : ‖α - a‖ ≤ ε / 8) (htail : ‖α - a‖ ≤ ‖y - a‖ / 8)
    (herror : c * ε ^ B ≤ ‖y - a‖)
    (hchoice : s * (2 * ε) ^ p ≤ (c / 2) * ε ^ B) :
    x ≠ α ∧ s ≤ ‖y - α‖ / ‖x - α‖ ^ p := by
  sorry

/-- Conditional stage estimates give nonroot complex starts converging to α
and error ratios tending to infinity. -/
theorem complex_stage_bounds_imply_divergence
    {ε c : ℕ → ℝ} {x y a : ℕ → ℂ} {α : ℂ} {B p : ℝ} (hp : 0 ≤ p)
    (hε : ∀ s, 0 < ε s) (hsmall : ∀ s, ε s < 1 / ((s : ℝ) + 1))
    (hleft : ∀ s, (3 / 4 : ℝ) * ε s ≤ ‖x s - a s‖)
    (hright : ∀ s, ‖x s - a s‖ ≤ (5 / 4 : ℝ) * ε s)
    (hscale : ∀ s, ‖α - a s‖ ≤ ε s / 8)
    (htail : ∀ s, ‖α - a s‖ ≤ ‖y s - a s‖ / 8)
    (herror : ∀ s, c s * ε s ^ B ≤ ‖y s - a s‖)
    (hchoice : ∀ s : ℕ, ((s : ℝ) + 1) * (2 * ε s) ^ p ≤ (c s / 2) * ε s ^ B) :
    (∀ s, x s ≠ α) ∧ Tendsto x atTop (𝓝 α) ∧
      Tendsto (fun s => ‖y s - α‖ / ‖x s - α‖ ^ p) atTop atTop := by
  sorry

end KungTraubAppendices
