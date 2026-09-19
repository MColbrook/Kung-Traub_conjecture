import KungTraub.DiagonalEstimates
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
  simpa only [sub_zero, abs_norm] using
    KungTraub.root_displacement_of_budget (α := ‖α - a‖) (a := 0)
      (by simpa only [sub_zero, abs_norm] using hroot) hE hε

/-- The exact relative tail bounds preserve the starting distance and at least
half the old error. -/
theorem complex_stage_root_error_bounds {ε : ℝ} {x y a α : ℂ}
    (hleft : (3 / 4 : ℝ) * ε ≤ ‖x - a‖) (hright : ‖x - a‖ ≤ (5 / 4 : ℝ) * ε)
    (hscale : ‖α - a‖ ≤ ε / 8) (herror : ‖α - a‖ ≤ ‖y - a‖ / 8) :
    (5 / 8 : ℝ) * ε ≤ ‖x - α‖ ∧ ‖x - α‖ ≤ (11 / 8 : ℝ) * ε ∧
      ‖y - a‖ / 2 ≤ ‖y - α‖ := by
  have hleft_triangle : ‖x - a‖ ≤ ‖x - α‖ + ‖α - a‖ := by
    calc
      ‖x - a‖ = ‖(x - α) + (α - a)‖ := by congr 1; ring
      _ ≤ ‖x - α‖ + ‖α - a‖ := norm_add_le _ _
  have hright_triangle : ‖x - α‖ ≤ ‖x - a‖ + ‖α - a‖ := by
    calc
      ‖x - α‖ = ‖(x - a) - (α - a)‖ := by congr 1; ring
      _ ≤ ‖x - a‖ + ‖α - a‖ := norm_sub_le _ _
  have herror_triangle : ‖y - a‖ ≤ ‖y - α‖ + ‖α - a‖ := by
    calc
      ‖y - a‖ = ‖(y - α) + (α - a)‖ := by congr 1; ring
      _ ≤ ‖y - α‖ + ‖α - a‖ := norm_add_le _ _
  refine ⟨by linarith, by linarith, ?_⟩
  linarith [norm_nonneg (y - a)]

/-- The complete one-stage estimate keeps the real exponents and derives a
nonzero starting distance before comparing the real-power denominators. -/
theorem complex_stage_error_ratio_lower_bound {ε B p c s : ℝ} {x y a α : ℂ}
    (hε : 0 < ε) (hp : 0 ≤ p)
    (hleft : (3 / 4 : ℝ) * ε ≤ ‖x - a‖) (hright : ‖x - a‖ ≤ (5 / 4 : ℝ) * ε)
    (hscale : ‖α - a‖ ≤ ε / 8) (htail : ‖α - a‖ ≤ ‖y - a‖ / 8)
    (herror : c * ε ^ B ≤ ‖y - a‖)
    (hchoice : s * (2 * ε) ^ p ≤ (c / 2) * ε ^ B) :
    x ≠ α ∧ s ≤ ‖y - α‖ / ‖x - α‖ ^ p := by
  obtain ⟨hlo, hhi, hhalf⟩ := complex_stage_root_error_bounds hleft hright hscale htail
  have hx : 0 < ‖x - α‖ := lt_of_lt_of_le (by positivity) hlo
  have hne : x ≠ α := sub_ne_zero.mp (norm_pos_iff.mp hx)
  have hbase : 0 < 2 * ε := by positivity
  have hdenom : 0 < (2 * ε) ^ p := Real.rpow_pos_of_pos hbase p
  have hsmall : ‖x - α‖ ^ p ≤ (2 * ε) ^ p :=
    Real.rpow_le_rpow (norm_nonneg _) (by linarith) hp
  refine ⟨hne, ?_⟩
  calc
    s ≤ ((c / 2) * ε ^ B) / (2 * ε) ^ p := (le_div_iff₀ hdenom).mpr hchoice
    _ ≤ (‖y - a‖ / 2) / (2 * ε) ^ p :=
      div_le_div_of_nonneg_right (by nlinarith [herror]) hdenom.le
    _ ≤ ‖y - α‖ / (2 * ε) ^ p := div_le_div_of_nonneg_right hhalf hdenom.le
    _ ≤ ‖y - α‖ / ‖x - α‖ ^ p := div_le_div_of_nonneg_left (norm_nonneg _)
      (Real.rpow_pos_of_pos hx p) hsmall

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
  have hstage (s : ℕ) := complex_stage_error_ratio_lower_bound (hε s) hp (hleft s) (hright s)
    (hscale s) (htail s) (herror s) (hchoice s)
  have hepslim : Tendsto ε atTop (𝓝 0) := squeeze_zero (fun s => (hε s).le)
    (fun s => (hsmall s).le) tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨fun s => (hstage s).1, ?_, ?_⟩
  · apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg) (g := fun s => 2 * ε s)
    · intro s
      obtain ⟨_, hhi, _⟩ := complex_stage_root_error_bounds
        (hleft s) (hright s) (hscale s) (htail s)
      rw [dist_eq_norm]
      linarith [hε s]
    · simpa using hepslim.const_mul 2
  · apply tendsto_atTop_mono (fun s : ℕ => le_trans (by linarith : (s : ℝ) ≤ (s : ℝ) + 1)
      (hstage s).2)
    exact tendsto_natCast_atTop_atTop

end KungTraubAppendices
