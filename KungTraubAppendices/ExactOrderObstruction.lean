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
  rintro ⟨C, _hC, δ, hδ, hbound⟩
  have hpm : 0 < p - (m : ℝ) := sub_pos.mpr hp
  have hx : Tendsto (fun x : ℝ => |x|) (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [abs_zero] using
      (continuous_abs.continuousAt.tendsto.mono_left nhdsWithin_le_nhds :
        Tendsto (fun x : ℝ => |x|) (𝓝[≠] (0 : ℝ)) (𝓝 |(0 : ℝ)|))
  have hpower : Tendsto (fun x : ℝ => Real.rpow |x| (p - (m : ℝ)))
      (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, Real.rpow_eq_pow, Real.zero_rpow (ne_of_gt hpm)] using
      (Real.continuousAt_rpow_const 0 (p - (m : ℝ)) (Or.inr hpm.le)).tendsto.comp hx
  have hupper : Tendsto (fun x : ℝ => C * Real.rpow |x| (p - (m : ℝ)))
      (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hpower
  have hevent : ∀ᶠ x in 𝓝[≠] (0 : ℝ),
      |F x / x ^ m| ≤ C * Real.rpow |x| (p - (m : ℝ)) := by
    filter_upwards [self_mem_nhdsWithin, hx.eventually (gt_mem_nhds hδ)] with x hxne hxδ
    have hxpos : 0 < |x| := abs_pos.mpr hxne
    calc
      |F x / x ^ m| = |F x| / |x| ^ m := by rw [abs_div, abs_pow]
      _ ≤ (C * Real.rpow |x| p) / |x| ^ m :=
        div_le_div_of_nonneg_right (hbound x hxpos hxδ) (pow_nonneg (abs_nonneg _) _)
      _ = C * Real.rpow |x| (p - (m : ℝ)) := by
        rw [Real.rpow_eq_pow, Real.rpow_eq_pow,
          Real.rpow_sub_natCast (ne_of_gt hxpos)]
        ring
  exact (not_le_of_gt (abs_pos.mpr hc))
    (le_of_tendsto_of_tendsto hF.abs hupper hevent)

/-- The same obstruction in the original local-order predicate at zero.
 -/
theorem not_localOrderAt_zero_of_normalized_limit {m : ℕ} {c : ℝ} (hc : c ≠ 0)
    {T : KungTraub.RealUpdate} {f : ℝ → ℝ}
    (hT : Tendsto (fun x => T f x / x ^ m) (𝓝[≠] (0 : ℝ)) (𝓝 c))
    (p : ℝ) (hp : (m : ℝ) < p) :
    ¬ KungTraub.LocalOrderAt T f 0 p := by
  simpa only [KungTraub.LocalOrderAt, sub_zero] using
    not_local_power_bound_of_normalized_limit hc hT p hp

end KungTraubAppendices
