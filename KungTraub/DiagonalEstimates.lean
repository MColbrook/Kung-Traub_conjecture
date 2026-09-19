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
  simpa only [mul_comm] using
    le_geom (u := b) (c := (1 / 2 : ℝ)) (by norm_num) n
      (fun j _ => by simpa only [div_eq_mul_inv, one_div, one_mul, mul_comm] using hstep j)

/-- The nonnegative geometric budgets are summable. -/
theorem summable_budget {b : ℕ → ℝ} (hpos : ∀ n, 0 ≤ b n)
    (hstep : ∀ n, b (n + 1) ≤ b n / 2) : Summable b := by
  exact Summable.of_nonneg_of_le hpos (budget_le_geometric hstep)
    (summable_geometric_two.mul_left (b 0))

/-- The sum of all correction budgets is at most twice the initial budget. -/
theorem tsum_budget_le_twice {b : ℕ → ℝ} (hpos : ∀ n, 0 ≤ b n)
    (hstep : ∀ n, b (n + 1) ≤ b n / 2) : (∑' n, b n) ≤ 2 * b 0 := by
  calc
    (∑' n, b n) ≤ ∑' n, b 0 * (1 / 2 : ℝ) ^ n :=
      (summable_budget hpos hstep).tsum_le_tsum (budget_le_geometric hstep)
        (summable_geometric_two.mul_left (b 0))
    _ = 2 * b 0 := by rw [tsum_mul_left, tsum_geometric_two]; ring

/-- Every tail, including its first term, is bounded by twice that first term.
Offset `s + 1` gives the remaining budgets after zero-based stage `s`. -/
theorem tsum_budget_tail_le_twice {b : ℕ → ℝ} (hpos : ∀ n, 0 ≤ b n)
    (hstep : ∀ n, b (n + 1) ≤ b n / 2) (s : ℕ) :
    (∑' j, b (j + s)) ≤ 2 * b s := by
  have htailstep : ∀ j : ℕ, b ((j + 1) + s) ≤ b (j + s) / 2 := by
    intro j
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (hstep (j + s))
  simpa using tsum_budget_le_twice (b := fun j => b (j + s))
    (fun j => hpos (j + s)) htailstep

/-- The paper's initial budget `1/32` gives a total correction budget at most `1/16`. -/
theorem tsum_budget_le_one_sixteenth {b : ℕ → ℝ} (hpos : ∀ n, 0 ≤ b n)
    (hstep : ∀ n, b (n + 1) ≤ b n / 2) (hfirst : b 0 ≤ 1 / 32) :
    (∑' n, b n) ≤ 1 / 16 := by
  linarith [tsum_budget_le_twice hpos hstep]

/-- Positive error and scale leave a positive choice for the next correction budget. -/
theorem exists_next_budget {b E ε : ℝ} (hb : 0 < b) (hE : 0 < E) (hε : 0 < ε) :
    ∃ bnext : ℝ, 0 < bnext ∧ bnext ≤ b / 2 ∧ bnext ≤ E / 32 ∧ bnext ≤ ε / 32 := by
  refine ⟨min (b / 2) (min (E / 32) (ε / 32)), ?_, min_le_left _ _, ?_, ?_⟩
  · exact lt_min (by positivity) (lt_min (by positivity) (by positivity))
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)

/-- The next budget converts the root-displacement bound into the two relative bounds
used to preserve the old error and the starting distance. -/
theorem root_displacement_of_budget {α a bnext E ε : ℝ}
    (hroot : |α - a| ≤ 4 * bnext) (hE : bnext ≤ E / 32)
    (hε : bnext ≤ ε / 32) : |α - a| ≤ E / 8 ∧ |α - a| ≤ ε / 8 := by
  constructor <;> linarith

/-- For real `p > B`, every positive threshold contains a scale satisfying the paper's
error amplification inequality. Neither exponent is restricted to an integer. -/
theorem exists_small_scale {B p c s δ : ℝ} (hp : B < p) (hc : 0 < c)
    (hs : 0 < s) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ s * (2 * ε) ^ p ≤ (c / 2) * ε ^ B := by
  have hq : 0 < p - B := sub_pos.mpr hp
  have hpowtwo : 0 < (2 : ℝ) ^ p := Real.rpow_pos_of_pos (by norm_num) p
  have hdenom : 0 < 2 * s * (2 : ℝ) ^ p := by positivity
  have htarget : 0 < c / (2 * s * (2 : ℝ) ^ p) := div_pos hc hdenom
  have hlim : Tendsto (fun ε : ℝ => ε ^ (p - B)) (𝓝 0) (𝓝 0) := by
    simpa only [Real.zero_rpow hq.ne'] using
      (Real.continuous_rpow_const hq.le).tendsto (0 : ℝ)
  have hsmall : ∀ᶠ ε : ℝ in 𝓝 0, ε ^ (p - B) < c / (2 * s * (2 : ℝ) ^ p) :=
    hlim.eventually (gt_mem_nhds htarget)
  obtain ⟨r, hr, hsmallr⟩ := Metric.eventually_nhds_iff.mp hsmall
  obtain ⟨ε, hε, hεbound⟩ := exists_between (lt_min hδ hr)
  have hεδ : ε < δ := hεbound.trans_le (min_le_left _ _)
  have hεr : ε < r := hεbound.trans_le (min_le_right _ _)
  have hsmallε := hsmallr (show dist ε 0 < r by simpa [Real.dist_eq, abs_of_pos hε] using hεr)
  have hscaled : ε ^ (p - B) * (2 * s * (2 : ℝ) ^ p) ≤ c :=
    (le_div_iff₀ hdenom).mp hsmallε.le
  have hsplit : ε ^ p = ε ^ B * ε ^ (p - B) := by
    rw [← Real.rpow_add hε]
    congr 1
    ring
  refine ⟨ε, hε, hεδ, ?_⟩
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hε.le, hsplit]
  calc
    s * ((2 : ℝ) ^ p * (ε ^ B * ε ^ (p - B))) =
        (ε ^ (p - B) * (2 * s * (2 : ℝ) ^ p)) * ε ^ B / 2 := by ring
    _ ≤ c * ε ^ B / 2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hscaled
        (Real.rpow_nonneg hε.le B)) (by norm_num)
    _ = (c / 2) * ε ^ B := by ring

/-- Scale selection at zero-based stage `s`, retaining the independent positive threshold
and the paper's exact caps `1/(s+1)` and `1/4`. -/
theorem exists_stage_scale {B p c threshold : ℝ} (hp : B < p) (hc : 0 < c)
    (hthreshold : 0 < threshold) (s : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < threshold ∧ ε < 1 / ((s : ℝ) + 1) ∧ ε < 1 / 4 ∧
      ((s : ℝ) + 1) * (2 * ε) ^ p ≤ (c / 2) * ε ^ B := by
  have hstage : (0 : ℝ) < (s : ℝ) + 1 := by positivity
  have hcap : 0 < min threshold (min (1 / ((s : ℝ) + 1)) (1 / 4)) :=
    lt_min hthreshold (lt_min (one_div_pos.mpr hstage) (by norm_num))
  obtain ⟨ε, hε, hεcap, hchoice⟩ := exists_small_scale hp hc hstage hcap
  have hεinner : ε < min (1 / ((s : ℝ) + 1)) (1 / 4) :=
    hεcap.trans_le (min_le_right _ _)
  exact ⟨ε, hε, hεcap.trans_le (min_le_left _ _), hεinner.trans_le (min_le_left _ _),
    hεinner.trans_le (min_le_right _ _), hchoice⟩

/-- The two root perturbation bounds give the precise final distance constants and retain
at least half the stage error. -/
theorem stage_root_error_bounds {ε x y a α : ℝ}
    (hleft : (3 / 4 : ℝ) * ε ≤ x - a) (hright : x - a ≤ (5 / 4 : ℝ) * ε)
    (hscale : |α - a| ≤ ε / 8) (herror : |α - a| ≤ |y - a| / 8) :
    (5 / 8 : ℝ) * ε ≤ x - α ∧ x - α ≤ (11 / 8 : ℝ) * ε ∧
      |y - a| / 2 ≤ |y - α| := by
  obtain ⟨hscaleleft, hscaleright⟩ := abs_le.mp hscale
  have htriangle : |y - a| ≤ |y - α| + |α - a| := by
    calc
      |y - a| = |(y - α) + (α - a)| := by congr 1; ring
      _ ≤ |y - α| + |α - a| := abs_add_le _ _
  refine ⟨by linarith, by linarith, ?_⟩
  linarith [abs_nonneg (y - a)]

/-- The complete scalar inequality at one stage, including its nonzero starting distance.
Its assumptions are precisely stage error, root displacement and scale inequalities. -/
theorem stage_error_ratio_lower_bound {ε x y a α B p c s : ℝ}
    (hε : 0 < ε) (hp : 0 ≤ p)
    (hleft : (3 / 4 : ℝ) * ε ≤ x - a) (hright : x - a ≤ (5 / 4 : ℝ) * ε)
    (hscale : |α - a| ≤ ε / 8) (htail : |α - a| ≤ |y - a| / 8)
    (herror : c * ε ^ B ≤ |y - a|)
    (hchoice : s * (2 * ε) ^ p ≤ (c / 2) * ε ^ B) :
    x ≠ α ∧ s ≤ |y - α| / |x - α| ^ p := by
  obtain ⟨hlo, hhi, hhalf⟩ := stage_root_error_bounds hleft hright hscale htail
  have hx : 0 < x - α := lt_of_lt_of_le (by positivity) hlo
  have hbase : 0 < 2 * ε := by positivity
  have hdenom : 0 < (2 * ε) ^ p := Real.rpow_pos_of_pos hbase p
  have hsmall : |x - α| ^ p ≤ (2 * ε) ^ p :=
    Real.rpow_le_rpow (abs_nonneg _) (by rw [abs_of_pos hx]; linarith) hp
  refine ⟨ne_of_gt (sub_pos.mp hx), ?_⟩
  calc
    s ≤ ((c / 2) * ε ^ B) / (2 * ε) ^ p := (le_div_iff₀ hdenom).mpr hchoice
    _ ≤ (|y - a| / 2) / (2 * ε) ^ p :=
      div_le_div_of_nonneg_right (by nlinarith [herror]) hdenom.le
    _ ≤ |y - α| / (2 * ε) ^ p := div_le_div_of_nonneg_right hhalf hdenom.le
    _ ≤ |y - α| / |x - α| ^ p := div_le_div_of_nonneg_left (abs_nonneg _)
      (Real.rpow_pos_of_pos (abs_pos.mpr (sub_ne_zero.mpr (ne_of_gt (sub_pos.mp hx)))) p) hsmall

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
  have hstage (s : ℕ) := stage_error_ratio_lower_bound (hε s) hp (hleft s) (hright s)
    (hscale s) (htail s) (herror s) (hchoice s)
  have hepslim : Tendsto ε atTop (𝓝 0) := squeeze_zero (fun s => (hε s).le)
    (fun s => (hsmall s).le) tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨fun s => (hstage s).1, ?_, ?_⟩
  · apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg) (g := fun s => 2 * ε s)
    · intro s
      obtain ⟨hlo, hhi, _⟩ := stage_root_error_bounds (hleft s) (hright s) (hscale s) (htail s)
      have hx : 0 < x s - α := lt_of_lt_of_le (mul_pos (by norm_num) (hε s)) hlo
      rw [Real.dist_eq, abs_of_pos hx]
      linarith
    · simpa using hepslim.const_mul 2
  · apply tendsto_atTop_mono (fun s : ℕ => le_trans (by linarith : (s : ℝ) ≤ (s : ℝ) + 1)
      (hstage s).2)
    exact tendsto_natCast_atTop_atTop

/-- Increasing the exponent increases an error ratio when its positive distance is at
most one. This is the comparison used for simultaneous failure of larger orders. -/
theorem error_ratio_mono_exponent {e d p q : ℝ} (he : 0 ≤ e) (hd : 0 < d)
    (hdone : d ≤ 1) (hpq : p ≤ q) : e / d ^ p ≤ e / d ^ q := by
  exact div_le_div_of_nonneg_left he (Real.rpow_pos_of_pos hd q)
    (Real.rpow_le_rpow_of_exponent_ge hd hdone hpq)

/-- The positive-stage exponents `B + 1/(s+1)` eventually lie below every fixed `p > B`. -/
theorem eventually_stage_exponent_le {B p : ℝ} (hp : B < p) :
    ∀ᶠ s : ℕ in atTop, B + 1 / ((s : ℝ) + 1) ≤ p := by
  have hlim : Tendsto (fun s : ℕ => B + 1 / ((s : ℝ) + 1)) atTop (𝓝 B) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_add B
  exact (hlim.eventually (gt_mem_nhds hp)).mono fun _ h => h.le

/-- One sequence of errors and distances satisfying the moving-exponent inequalities
has a divergent ratio for every fixed larger exponent, with unchanged witnesses. -/
theorem simultaneous_ratio_divergence {e d : ℕ → ℝ} {B : ℝ}
    (he : ∀ s, 0 ≤ e s) (hd : ∀ s, 0 < d s)
    (hdone : ∀ᶠ s in atTop, d s ≤ 1)
    (hstage : ∀ s : ℕ, (s : ℝ) + 1 ≤ e s / d s ^ (B + 1 / ((s : ℝ) + 1)))
    (p : ℝ) (hp : B < p) : Tendsto (fun s => e s / d s ^ p) atTop atTop := by
  apply tendsto_atTop_mono' atTop (f₁ := fun s : ℕ => (s : ℝ))
  · filter_upwards [hdone, eventually_stage_exponent_le hp] with s hs hpstage
    exact le_trans (by linarith : (s : ℝ) ≤ (s : ℝ) + 1)
      ((hstage s).trans (error_ratio_mono_exponent (he s) (hd s) hs hpstage))
  · exact tendsto_natCast_atTop_atTop

end KungTraub
