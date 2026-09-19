import support_reference.KungTraub.PolynomialLocalization
import support_reference.KungTraub.PolynomialInformation
import support_reference.KungTraub.Exponents
import Mathlib.Data.Multiset.Sort

/-!
# Polynomial estimates for the remaining sensitivity

This module develops the lower bound in Section 3.3 of the manuscript. Localization
constants are chosen once for each degree and dimension, then maximized over a finite
set determined only by `n`. No constant is chosen from an algorithm or a transcript.
Root multiplicities are represented by root multisets.
-/

noncomputable section

open Polynomial Filter
open scoped BigOperators Topology

namespace KungTraub

/-- A fixed choice of the proved localization constant; ineligible degree/dimension
pairs receive `1`, which does not change the later maximum with `1`. -/
def wronskianLocalizationConstant (d m : ℕ) : ℝ :=
  if h : 0 < m ∧ m ≤ d then
    (polynomialWronskian_uniform_localization h.1 h.2).choose
  else 1

theorem wronskianLocalizationConstant_pos (d m : ℕ) :
    0 < wronskianLocalizationConstant d m := by
  sorry

theorem wronskianLocalizationConstant_spec {m d : ℕ} (hm : 0 < m) (hmd : m ≤ d)
    (p : Fin m → Polynomial ℂ) (hp : LinearIndependent ℂ p)
    (hdeg : ∀ i, (p i).natDegree ≤ d) (a : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (q : Polynomial ℂ) (hqmem : q ∈ Submodule.span ℂ (Set.range p)) (hqzero : q ≠ 0)
    (hroots : ∃ z : Fin m → ℂ, (∀ i, ‖z i - a‖ ≤ r) ∧
      (List.ofFn z : Multiset ℂ) ≤ q.roots) :
    ∃ z : ℂ, ‖z - a‖ ≤ wronskianLocalizationConstant d m * r ∧
      (polynomialWronskian p).eval z = 0 := by
  sorry

/-- The paper's `C_*`: the maximum of `1` and all localization constants with
`1 ≤ m ≤ d ≤ n`. The other pairs in this finite square contribute only `1`. -/
def uniformWronskianConstant (n : ℕ) : ℝ :=
  max 1 (Finset.univ.sup' Finset.univ_nonempty
    (fun dm : Fin (n + 1) × Fin (n + 1) => wronskianLocalizationConstant dm.1.val dm.2.val))

theorem one_le_uniformWronskianConstant (n : ℕ) : 1 ≤ uniformWronskianConstant n := by
  sorry

theorem uniformWronskianConstant_pos (n : ℕ) : 0 < uniformWronskianConstant n := by
  sorry

theorem wronskianLocalizationConstant_le_uniform {n d m : ℕ} (hmd : m ≤ d) (hdn : d ≤ n) :
    wronskianLocalizationConstant d m ≤ uniformWronskianConstant n := by
  sorry

/-- The fixed maximum works uniformly for every eligible degree and dimension. -/
theorem uniformWronskianConstant_spec {n m d : ℕ}
    (hm : 0 < m) (hmd : m ≤ d) (hdn : d ≤ n)
    (p : Fin m → Polynomial ℂ) (hp : LinearIndependent ℂ p)
    (hdeg : ∀ i, (p i).natDegree ≤ d) (a : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (q : Polynomial ℂ) (hqmem : q ∈ Submodule.span ℂ (Set.range p)) (hqzero : q ≠ 0)
    (hroots : ∃ z : Fin m → ℂ, (∀ i, ‖z i - a‖ ≤ r) ∧
      (List.ofFn z : Multiset ℂ) ≤ q.roots) :
    ∃ z : ℂ, ‖z - a‖ ≤ uniformWronskianConstant n * r ∧
      (polynomialWronskian p).eval z = 0 := by
  sorry

/-- Avoidance of all Wronskian zeros forces a lower bound on a disc containing `m`
roots of the nonzero member, counted with multiplicity. This is the localization
step behind the individual distance bounds in equation `eq:rhobound`. -/
theorem root_radius_lower_bound_of_wronskian_avoidance {n m d : ℕ}
    (hm : 0 < m) (hmd : m ≤ d) (hdn : d ≤ n)
    (p : Fin m → Polynomial ℂ) (hp : LinearIndependent ℂ p)
    (hdeg : ∀ i, (p i).natDegree ≤ d) (a : ℂ) (r δ : ℝ) (hr : 0 ≤ r)
    (q : Polynomial ℂ) (hqmem : q ∈ Submodule.span ℂ (Set.range p)) (hqzero : q ≠ 0)
    (hroots : ∃ z : Fin m → ℂ, (∀ i, ‖z i - a‖ ≤ r) ∧
      (List.ofFn z : Multiset ℂ) ≤ q.roots)
    (havoid : ∀ z : ℂ, (polynomialWronskian p).eval z = 0 → δ ≤ ‖z - a‖) :
    δ / uniformWronskianConstant n ≤ r := by
  sorry

/-- All roots can be enumerated by decreasing distance from the evaluation point,
with repeated roots retained. No separation or simple-root hypothesis is imposed. -/
theorem exists_roots_ordered_by_distance (q : Polynomial ℂ) (a : ℂ) :
    ∃ β : Fin q.natDegree → ℂ,
      (List.ofFn β : Multiset ℂ) = q.roots ∧ Antitone (fun i => ‖a - β i‖) := by
  sorry

/-- The final `d-k` entries of a distance-ordered root tuple are exactly a tuple
of that many nearest roots in the required closed disc. -/
theorem ordered_roots_suffix_in_disc {d : ℕ} (q : Polynomial ℂ) (a : ℂ)
    (β : Fin d → ℂ) (hβ : (List.ofFn β : Multiset ℂ) = q.roots)
    (hsort : Antitone (fun i => ‖a - β i‖)) (k : Fin d) :
    ∃ z : Fin (d - k.val) → ℂ, (∀ i, ‖z i - a‖ ≤ ‖a - β k‖) ∧
      (List.ofFn z : Multiset ℂ) ≤ q.roots := by
  sorry

/-- The explicit constant `c_j` from the manuscript. Here `γ i` denotes the bound
for observation `i+1`, because the oracle and prefix APIs use zero-based indices. -/
def sensitivityPolynomialConstant (n : ℕ) (γ : ℕ → ℝ) (j : ℕ) : ℝ :=
  ((4 : ℝ) ^ n)⁻¹ * ∏ i ∈ Finset.range j, min 1 (γ i / uniformWronskianConstant n)

theorem sensitivityPolynomialConstant_pos {n j : ℕ} (γ : ℕ → ℝ)
    (hγ : ∀ i < j, 0 < γ i) : 0 < sensitivityPolynomialConstant n γ j := by
  sorry

theorem sensitivityPolynomialConstant_le_one {n j : ℕ} (γ : ℕ → ℝ)
    (hγ : ∀ i < j, 0 < γ i) : sensitivityPolynomialConstant n γ j ≤ 1 := by
  sorry

/-- Distinct rank-increase indices use at most the full Kung--Traub exponent. -/
theorem sum_orderBound_selected_le {j d : ℕ} (hj : 0 < j)
    (indices : Fin d → Fin j) (hinj : Function.Injective indices) :
    (∑ k : Fin d, orderBound (indices k).val) ≤ orderBound j := by
  sorry

/-- Adding the unused positive factors, all at most one, only reduces the product. -/
theorem sensitivityPolynomialConstant_le_selected {n j d : ℕ} (hdn : d ≤ n)
    (γ : ℕ → ℝ) (hγ : ∀ i < j, 0 < γ i)
    (indices : Fin d → Fin j) (hinj : Function.Injective indices) :
    sensitivityPolynomialConstant n γ j ≤ ((4 : ℝ) ^ d)⁻¹ *
      ∏ k : Fin d, min 1 (γ (indices k).val / uniformWronskianConstant n) := by
  sorry

/-- Truncation of a root distance at one preserves its scale power. -/
theorem truncated_distance_scale_lower_bound {v t ρ : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hρ : v * t ≤ ρ) :
    min 1 v * t ≤ min 1 ρ := by
  sorry

/-- Exact product and exponent arithmetic after the individual, counted root distances
have been obtained from localization. The constant includes every observation index. -/
theorem polynomial_value_lower_bound_of_root_distances {n j d : ℕ}
    (hj : 0 < j) (hdn : d ≤ n) (q : Polynomial ℂ) (hdegree : q.natDegree = d)
    (hnorm : ‖coefficientVector n q‖ = 1) (a : ℂ) (ha : ‖a‖ ≤ 1 / 2)
    (β : Fin d → ℂ) (hβ : (List.ofFn β : Multiset ℂ) = q.roots)
    (γ : ℕ → ℝ) (hγ : ∀ i < j, 0 < γ i)
    (indices : Fin d → Fin j) (hinj : Function.Injective indices)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hdist : ∀ k, γ (indices k).val / uniformWronskianConstant n *
      ε ^ orderBound (indices k).val ≤ ‖a - β k‖) :
    sensitivityPolynomialConstant n γ j * ε ^ orderBound j ≤ ‖q.eval a‖ := by
  sorry

/-- The inverse constant-coordinate scaling costs exactly the denominator `2R+2`
from the manuscript. The input value bound is supplied by the preceding root argument. -/
theorem polynomial_inverse_scale_lower_bound {n j : ℕ}
    (q : Polynomial ℂ) (hq : q.natDegree ≤ n) (hnorm : ‖coefficientVector n q‖ = 1)
    (γ : ℕ → ℝ) (hγ : ∀ i < j, 0 < γ i)
    {a : ℂ} {ε R : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 < R)
    (ha : ‖a‖ ≤ R * ε) (hhalf : R * ε ≤ 1 / 2)
    (hvalue : sensitivityPolynomialConstant n γ j * ε ^ orderBound j ≤ ‖q.eval a‖) :
    (sensitivityPolynomialConstant n γ j / (2 * R + 2)) * ε ^ orderBound j ≤
      ‖q.eval a‖ / ‖inverseConstantScale ε (coefficientVector n q)‖ := by
  sorry

/-- Multiplication by the nonvanishing family weight gives exactly the positive
constant `A_j = w_* c_j / (2R+2)`. This is an algebraic estimate; a real admissible
direction requires the real-coefficient bridge in addition. -/
theorem weighted_polynomial_inverse_scale_lower_bound {n j : ℕ}
    (q : Polynomial ℂ) (hq : q.natDegree ≤ n) (hnorm : ‖coefficientVector n q‖ = 1)
    (γ : ℕ → ℝ) (hγ : ∀ i < j, 0 < γ i)
    {a w : ℂ} {ε R wmin : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 < R)
    (hwmin : 0 < wmin) (hw : wmin ≤ ‖w‖)
    (ha : ‖a‖ ≤ R * ε) (hhalf : R * ε ≤ 1 / 2)
    (hvalue : sensitivityPolynomialConstant n γ j * ε ^ orderBound j ≤ ‖q.eval a‖) :
    (wmin * sensitivityPolynomialConstant n γ j / (2 * R + 2)) * ε ^ orderBound j ≤
      ‖w * q.eval a‖ / ‖inverseConstantScale ε (coefficientVector n q)‖ := by
  sorry

end KungTraub
