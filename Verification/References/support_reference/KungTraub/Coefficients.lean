import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic

/-!
# Polynomial coefficient estimates

Supporting estimates for Lemma 2.2 of Matthew J. Colbrook's
`kung_traub_solution.tex`. The Euclidean coefficient norm and the inverse
constant-coordinate scaling are explicit. The argument is adapted from the
author's proof; general norm and arithmetic facts are supplied by Mathlib.

The estimates include the numerical series identity used in the derivative bound.
-/

namespace KungTraub

noncomputable section

open scoped BigOperators

/-- The coefficient vector of a degree-at-most-`n` polynomial, with the
Euclidean norm rather than the supremum norm of a function space. -/
def coefficientVector (n : ℕ) (q : Polynomial ℂ) :
    EuclideanSpace ℂ (Fin (n + 1)) :=
  WithLp.toLp 2 (fun i => q.coeff i.val)

/-- Inverse of the scaling of the constant coefficient by a real number. -/
def inverseConstantScale {n : ℕ} (ε : ℝ)
    (b : EuclideanSpace ℂ (Fin (n + 1))) :
    EuclideanSpace ℂ (Fin (n + 1)) :=
  WithLp.toLp 2 (fun i => if i = 0 then b i / (ε : ℂ) else b i)

/-- The Euclidean norm is bounded by the sum of coordinate norms. -/
theorem euclidean_norm_le_sum {ι : Type*} [Fintype ι]
    (b : EuclideanSpace ℂ ι) : ‖b‖ ≤ ∑ i, ‖b i‖ := by
  sorry

/-- The elementary coefficient bound needed in the product estimate.
This uses Mathlib's `Polynomial.norm_coeff_le_choose_mul_mahlerMeasure`,
in the module by Fabrizio Barroero and Kevin H. Wilson. -/
theorem coefficientVector_norm_le_mahler {n : ℕ} (q : Polynomial ℂ)
    (hq : q.natDegree ≤ n) :
    ‖coefficientVector n q‖ ≤ 2 ^ q.natDegree * q.mahlerMeasure := by
  sorry

/-- A single normalized root factor on the closed half-unit disc. -/
theorem root_factor_bound {a β : ℂ} (ha : ‖a‖ ≤ 1 / 2) :
    max 1 ‖β‖ * min 1 ‖a - β‖ ≤ 2 * ‖a - β‖ := by
  sorry

/-- The root-factor bound with roots counted with multiplicity. -/
theorem root_product_bound (s : Multiset ℂ) {a : ℂ} (ha : ‖a‖ ≤ 1 / 2) :
    (s.map (fun β => max 1 ‖β‖)).prod *
      (s.map (fun β => min 1 ‖a - β‖)).prod ≤
    2 ^ s.card * ‖(s.map (fun β => a - β)).prod‖ := by
  sorry

/-- Lemma 2.2's product estimate, in division form, on the full stated domain. -/
theorem polynomial_product_estimate {n : ℕ} (q : Polynomial ℂ)
    (hq : q.natDegree ≤ n) (hnorm : ‖coefficientVector n q‖ = 1)
    {a : ℂ} (ha : ‖a‖ ≤ 1 / 2) :
    (q.roots.map (fun β => min 1 ‖a - β‖)).prod / 4 ^ q.natDegree ≤
      ‖q.eval a‖ := by
  sorry

/-- Coordinatewise domination implies domination of the Euclidean norm. -/
theorem euclidean_norm_mono {ι : Type*} [Fintype ι]
    (b c : EuclideanSpace ℂ ι) (h : ∀ i, ‖b i‖ ≤ ‖c i‖) : ‖b‖ ≤ ‖c‖ := by
  sorry

/-- Scaling only the constant coordinate gives the required dimension-free bound. -/
theorem inverseConstantScale_norm_le {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (b : EuclideanSpace ℂ (Fin (n + 1))) :
    ‖inverseConstantScale ε b‖ ≤ ‖b 0‖ / ε + ‖b‖ := by
  sorry

/-- A nonzero coefficient vector remains nonzero under positive inverse scaling. -/
theorem inverseConstantScale_norm_pos {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (b : EuclideanSpace ℂ (Fin (n + 1))) (hb : ‖b‖ = 1) :
    0 < ‖inverseConstantScale ε b‖ := by
  sorry

/-- A finite geometric sum on the closed half-unit interval. -/
theorem sum_powers_le_two {r : ℝ} (hr : 0 ≤ r) (hrhalf : r ≤ 1 / 2) (n : ℕ) :
    ∑ k ∈ Finset.range n, r ^ k ≤ 2 := by
  sorry

/-- The numerical series in the manuscript's derivative estimate, reindexed from zero. -/
theorem derivative_coefficient_series :
    HasSum (fun k : ℕ => ((k : ℝ) + 1) ^ 2 * (1 / 2 : ℝ) ^ (2 * k))
      (80 / 27 : ℝ) := by
  sorry

theorem derivative_coefficient_series_sqrt_lt_two :
    Real.sqrt (80 / 27 : ℝ) < 2 := by
  sorry

/-- Unit Euclidean coefficient norm controls the change from the constant term.
A finite geometric sum suffices here; no derivative regularity is assumed. -/
theorem polynomial_eval_sub_constant_le {n : ℕ} (q : Polynomial ℂ)
    (hq : q.natDegree ≤ n) (hnorm : ‖coefficientVector n q‖ = 1)
    {a : ℂ} (ha : ‖a‖ ≤ 1 / 2) :
    ‖q.eval a - q.coeff 0‖ ≤ 2 * ‖a‖ := by
  sorry

/-- The final real inequality in the scaled-norm estimate. -/
theorem scaled_ratio_bound {x D ε R : ℝ} (hx : 0 ≤ x) (hD : 0 < D)
    (hε : 0 < ε) (hR : 0 ≤ R) (hbound : D ≤ x / ε + 2 * R + 1) :
    min ε x / (2 * R + 2) ≤ x / D := by
  sorry

/-- Lemma 2.2's scaled estimate, including degree zero and all positive scales. -/
theorem polynomial_scaled_estimate {n : ℕ} (q : Polynomial ℂ)
    (hq : q.natDegree ≤ n) (hnorm : ‖coefficientVector n q‖ = 1)
    {a : ℂ} {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R)
    (ha : ‖a‖ ≤ R * ε) (hhalf : R * ε ≤ 1 / 2) :
    min ε ‖q.eval a‖ / (2 * R + 2) ≤
      ‖q.eval a‖ / ‖inverseConstantScale ε (coefficientVector n q)‖ := by
  sorry

end

end KungTraub
