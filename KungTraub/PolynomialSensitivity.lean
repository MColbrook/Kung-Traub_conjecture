import KungTraub.PolynomialLocalization
import KungTraub.PolynomialInformation
import KungTraub.Exponents
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
  unfold wronskianLocalizationConstant
  split_ifs with h
  · exact (polynomialWronskian_uniform_localization h.1 h.2).choose_spec.1
  · norm_num

theorem wronskianLocalizationConstant_spec {m d : ℕ} (hm : 0 < m) (hmd : m ≤ d)
    (p : Fin m → Polynomial ℂ) (hp : LinearIndependent ℂ p)
    (hdeg : ∀ i, (p i).natDegree ≤ d) (a : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (q : Polynomial ℂ) (hqmem : q ∈ Submodule.span ℂ (Set.range p)) (hqzero : q ≠ 0)
    (hroots : ∃ z : Fin m → ℂ, (∀ i, ‖z i - a‖ ≤ r) ∧
      (List.ofFn z : Multiset ℂ) ≤ q.roots) :
    ∃ z : ℂ, ‖z - a‖ ≤ wronskianLocalizationConstant d m * r ∧
      (polynomialWronskian p).eval z = 0 := by
  rw [wronskianLocalizationConstant, dif_pos (show 0 < m ∧ m ≤ d from ⟨hm, hmd⟩)]
  exact (polynomialWronskian_uniform_localization hm hmd).choose_spec.2
    p hp hdeg a r hr q hqmem hqzero hroots

/-- The paper's `C_*`: the maximum of `1` and all localization constants with
`1 ≤ m ≤ d ≤ n`. The other pairs in this finite square contribute only `1`. -/
def uniformWronskianConstant (n : ℕ) : ℝ :=
  max 1 (Finset.univ.sup' Finset.univ_nonempty
    (fun dm : Fin (n + 1) × Fin (n + 1) => wronskianLocalizationConstant dm.1.val dm.2.val))

theorem one_le_uniformWronskianConstant (n : ℕ) : 1 ≤ uniformWronskianConstant n :=
  le_max_left _ _

theorem uniformWronskianConstant_pos (n : ℕ) : 0 < uniformWronskianConstant n :=
  zero_lt_one.trans_le (one_le_uniformWronskianConstant n)

theorem wronskianLocalizationConstant_le_uniform {n d m : ℕ} (hmd : m ≤ d) (hdn : d ≤ n) :
    wronskianLocalizationConstant d m ≤ uniformWronskianConstant n := by
  let dm : Fin (n + 1) × Fin (n + 1) := ⟨⟨d, by omega⟩, ⟨m, by omega⟩⟩
  have h := Finset.le_sup'
    (fun dm : Fin (n + 1) × Fin (n + 1) => wronskianLocalizationConstant dm.1.val dm.2.val)
    (Finset.mem_univ dm)
  exact h.trans (le_max_right _ _)

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
  obtain ⟨z, hz, hW⟩ := wronskianLocalizationConstant_spec hm hmd p hp hdeg a r hr q hqmem hqzero hroots
  exact ⟨z, hz.trans (mul_le_mul_of_nonneg_right
    (wronskianLocalizationConstant_le_uniform hmd hdn) hr), hW⟩

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
  obtain ⟨z, hz, hW⟩ := uniformWronskianConstant_spec hm hmd hdn p hp hdeg a r hr q hqmem hqzero hroots
  apply (div_le_iff₀ (uniformWronskianConstant_pos n)).mpr
  simpa only [mul_comm] using (havoid z hW).trans hz

/-- All roots can be enumerated by decreasing distance from the evaluation point,
with repeated roots retained. No separation or simple-root hypothesis is imposed. -/
theorem exists_roots_ordered_by_distance (q : Polynomial ℂ) (a : ℂ) :
    ∃ β : Fin q.natDegree → ℂ,
      (List.ofFn β : Multiset ℂ) = q.roots ∧ Antitone (fun i => ‖a - β i‖) := by
  classical
  let rel : ℂ → ℂ → Prop := fun z w => ‖a - w‖ ≤ ‖a - z‖
  let : IsTrans ℂ rel := ⟨fun _ _ _ h₁ h₂ => h₂.trans h₁⟩
  let : Std.Total rel := ⟨fun _ _ => le_total _ _⟩
  let : Std.Refl rel := ⟨fun _ => le_refl _⟩
  let l := q.roots.toList.mergeSort (fun z w => decide (rel z w))
  have hlroots : (l : Multiset ℂ) = q.roots := by
    calc
      (l : Multiset ℂ) = (q.roots.toList : Multiset ℂ) :=
        Quot.sound (List.mergeSort_perm _ _)
      _ = q.roots := Multiset.coe_toList _
  have hlen : l.length = q.natDegree := by
    have h := congrArg Multiset.card hlroots
    simpa only [Multiset.coe_card, Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits q)] using h
  let β : Fin q.natDegree → ℂ := fun i => l.get (Fin.cast hlen.symm i)
  have hβ : List.ofFn β = l := by
    apply List.ext_getElem
    · simp only [List.length_ofFn, hlen]
    · intro i hi₁ hi₂
      simp [β]
  refine ⟨β, by rw [hβ, hlroots], ?_⟩
  intro i j hij
  have hsorted : l.Pairwise rel := List.pairwise_mergeSort' rel q.roots.toList
  exact hsorted.rel_get_of_le (show Fin.cast hlen.symm i ≤ Fin.cast hlen.symm j from hij)

/-- The final `d-k` entries of a distance-ordered root tuple are exactly a tuple
of that many nearest roots in the required closed disc. -/
theorem ordered_roots_suffix_in_disc {d : ℕ} (q : Polynomial ℂ) (a : ℂ)
    (β : Fin d → ℂ) (hβ : (List.ofFn β : Multiset ℂ) = q.roots)
    (hsort : Antitone (fun i => ‖a - β i‖)) (k : Fin d) :
    ∃ z : Fin (d - k.val) → ℂ, (∀ i, ‖z i - a‖ ≤ ‖a - β k‖) ∧
      (List.ofFn z : Multiset ℂ) ≤ q.roots := by
  let z : Fin (d - k.val) → ℂ := fun i => β ⟨k.val + i.val, by have := i.isLt; omega⟩
  have hzlist : List.ofFn z = (List.ofFn β).drop k.val := by
    apply List.ext_getElem
    · simp
    · intro i hi₁ hi₂
      simp [z, List.getElem_drop]
  refine ⟨z, ?_, ?_⟩
  · intro i
    rw [norm_sub_rev]
    exact hsort (show k ≤ (⟨k.val + i.val, by have := i.isLt; omega⟩ : Fin d) by
      change k.val ≤ k.val + i.val
      omega)
  · rw [hzlist, ← hβ]
    exact (List.drop_sublist k.val (List.ofFn β)).subperm

/-- The explicit constant `c_j` from the manuscript. Here `γ i` denotes the bound
for observation `i+1`, because the oracle and prefix APIs use zero-based indices. -/
def sensitivityPolynomialConstant (n : ℕ) (γ : ℕ → ℝ) (j : ℕ) : ℝ :=
  ((4 : ℝ) ^ n)⁻¹ * ∏ i ∈ Finset.range j, min 1 (γ i / uniformWronskianConstant n)

theorem sensitivityPolynomialConstant_pos {n j : ℕ} (γ : ℕ → ℝ)
    (hγ : ∀ i < j, 0 < γ i) : 0 < sensitivityPolynomialConstant n γ j := by
  apply mul_pos (by positivity)
  apply Finset.prod_pos
  intro i hi
  exact lt_min zero_lt_one (div_pos (hγ i (Finset.mem_range.mp hi)) (uniformWronskianConstant_pos n))

theorem sensitivityPolynomialConstant_le_one {n j : ℕ} (γ : ℕ → ℝ)
    (hγ : ∀ i < j, 0 < γ i) : sensitivityPolynomialConstant n γ j ≤ 1 := by
  have hprodnonneg : 0 ≤ ∏ i ∈ Finset.range j, min 1 (γ i / uniformWronskianConstant n) := by
    apply Finset.prod_nonneg
    intro i hi
    exact le_min zero_le_one (div_nonneg (hγ i (Finset.mem_range.mp hi)).le
      (uniformWronskianConstant_pos n).le)
  have hprodle : (∏ i ∈ Finset.range j, min 1 (γ i / uniformWronskianConstant n)) ≤ 1 :=
    Finset.prod_le_one (fun i hi => le_min zero_le_one
      (div_nonneg (hγ i (Finset.mem_range.mp hi)).le (uniformWronskianConstant_pos n).le))
      (fun _ _ => min_le_left _ _)
  have hinv : ((4 : ℝ) ^ n)⁻¹ ≤ 1 := by
    calc
      ((4 : ℝ) ^ n)⁻¹ ≤ (1 : ℝ)⁻¹ := (inv_le_inv₀ (by positivity) (by positivity)).mpr
        (one_le_pow₀ (show (1 : ℝ) ≤ 4 by norm_num))
      _ = 1 := by norm_num
  exact mul_le_one₀ hinv hprodnonneg hprodle

/-- Distinct rank-increase indices use at most the full Kung--Traub exponent. -/
theorem sum_orderBound_selected_le {j d : ℕ} (hj : 0 < j)
    (indices : Fin d → Fin j) (hinj : Function.Injective indices) :
    (∑ k : Fin d, orderBound (indices k).val) ≤ orderBound j := by
  classical
  let s := Finset.univ.image (fun k : Fin d => (indices k).val)
  have hs : s ⊆ Finset.range j := by
    intro i hi
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_range.mpr (indices k).isLt
  have h := sum_orderBound_le hj s hs
  have heq : (∑ i ∈ s, orderBound i) = ∑ k : Fin d, orderBound (indices k).val := by
    exact Finset.sum_image (by intro k _ l _ hkl; exact hinj (Fin.ext hkl))
  rwa [heq] at h

/-- Adding the unused positive factors, all at most one, only reduces the product. -/
theorem sensitivityPolynomialConstant_le_selected {n j d : ℕ} (hdn : d ≤ n)
    (γ : ℕ → ℝ) (hγ : ∀ i < j, 0 < γ i)
    (indices : Fin d → Fin j) (hinj : Function.Injective indices) :
    sensitivityPolynomialConstant n γ j ≤ ((4 : ℝ) ^ d)⁻¹ *
      ∏ k : Fin d, min 1 (γ (indices k).val / uniformWronskianConstant n) := by
  classical
  let s := Finset.univ.image (fun k : Fin d => (indices k).val)
  have hs : s ⊆ Finset.range j := by
    intro i hi
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_range.mpr (indices k).isLt
  have hf (i : ℕ) (hi : i ∈ Finset.range j) :
      0 ≤ min 1 (γ i / uniformWronskianConstant n) :=
    le_min zero_le_one (div_nonneg (hγ i (Finset.mem_range.mp hi)).le
      (uniformWronskianConstant_pos n).le)
  have hprod := Finset.prod_le_prod_of_subset_of_le_one hs hf
    (fun _ _ _ => min_le_left 1 _)
  have heq : (∏ i ∈ s, min 1 (γ i / uniformWronskianConstant n)) =
      ∏ k : Fin d, min 1 (γ (indices k).val / uniformWronskianConstant n) := by
    exact Finset.prod_image (by intro k _ l _ hkl; exact hinj (Fin.ext hkl))
  rw [heq] at hprod
  have hpow : ((4 : ℝ) ^ n)⁻¹ ≤ ((4 : ℝ) ^ d)⁻¹ := by
    apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hdn
  exact mul_le_mul hpow hprod (Finset.prod_nonneg hf) (by positivity)

/-- Truncation of a root distance at one preserves its scale power. -/
theorem truncated_distance_scale_lower_bound {v t ρ : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hρ : v * t ≤ ρ) :
    min 1 v * t ≤ min 1 ρ := by
  apply le_min
  · exact (mul_le_mul_of_nonneg_right (min_le_left 1 v) ht).trans (by simpa using ht1)
  · exact (mul_le_mul_of_nonneg_right (min_le_right 1 v) ht).trans hρ

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
  have hnonneg (k : Fin d) : 0 ≤ min 1 (γ (indices k).val / uniformWronskianConstant n) :=
    le_min zero_le_one (div_nonneg (hγ _ (indices k).isLt).le
      (uniformWronskianConstant_pos n).le)
  have hprod : (∏ k : Fin d, min 1 (γ (indices k).val / uniformWronskianConstant n) *
      ε ^ orderBound (indices k).val) ≤ ∏ k : Fin d, min 1 ‖a - β k‖ := by
    apply Finset.prod_le_prod
    · intro k _
      exact mul_nonneg (hnonneg k) (pow_nonneg hε.le _)
    · intro k _
      exact truncated_distance_scale_lower_bound (pow_nonneg hε.le _)
        (pow_le_one₀ hε.le hε1) (hdist k)
  have hpower : ε ^ orderBound j ≤ ε ^ (∑ k : Fin d, orderBound (indices k).val) :=
    pow_le_pow_of_le_one hε.le hε1 (sum_orderBound_selected_le hj indices hinj)
  have hrootprod : (∏ k : Fin d, min 1 ‖a - β k‖) =
      (q.roots.map (fun z => min 1 ‖a - z‖)).prod := by
    rw [← hβ]
    simp only [Multiset.map_coe, List.map_ofFn, Multiset.prod_coe, List.prod_ofFn, Function.comp_def]
  calc
    sensitivityPolynomialConstant n γ j * ε ^ orderBound j ≤
        sensitivityPolynomialConstant n γ j * ε ^ (∑ k : Fin d, orderBound (indices k).val) :=
      mul_le_mul_of_nonneg_left hpower (sensitivityPolynomialConstant_pos γ hγ).le
    _ ≤ (((4 : ℝ) ^ d)⁻¹ * ∏ k : Fin d, min 1 (γ (indices k).val / uniformWronskianConstant n)) *
        ε ^ (∑ k : Fin d, orderBound (indices k).val) :=
      mul_le_mul_of_nonneg_right (sensitivityPolynomialConstant_le_selected hdn γ hγ indices hinj)
        (pow_nonneg hε.le _)
    _ = (∏ k : Fin d, min 1 (γ (indices k).val / uniformWronskianConstant n) *
        ε ^ orderBound (indices k).val) / 4 ^ d := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
      ring
    _ ≤ (∏ k : Fin d, min 1 ‖a - β k‖) / 4 ^ d :=
      div_le_div_of_nonneg_right hprod (by positivity)
    _ = (q.roots.map (fun z => min 1 ‖a - z‖)).prod / 4 ^ q.natDegree := by rw [hrootprod, hdegree]
    _ ≤ ‖q.eval a‖ := polynomial_product_estimate q (hdegree.trans_le hdn) hnorm ha

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
  have hpow : ε ^ orderBound j ≤ ε :=
    pow_le_of_le_one hε.le hε1 (orderBound_pos j).ne'
  have hscale : sensitivityPolynomialConstant n γ j * ε ^ orderBound j ≤ ε :=
    (mul_le_mul_of_nonneg_right (sensitivityPolynomialConstant_le_one γ hγ)
      (pow_nonneg hε.le _)).trans (by simpa using hpow)
  have hmin : sensitivityPolynomialConstant n γ j * ε ^ orderBound j ≤ min ε ‖q.eval a‖ :=
    le_min hscale hvalue
  calc
    (sensitivityPolynomialConstant n γ j / (2 * R + 2)) * ε ^ orderBound j =
        (sensitivityPolynomialConstant n γ j * ε ^ orderBound j) / (2 * R + 2) := by ring
    _ ≤ min ε ‖q.eval a‖ / (2 * R + 2) :=
      div_le_div_of_nonneg_right hmin (by positivity)
    _ ≤ ‖q.eval a‖ / ‖inverseConstantScale ε (coefficientVector n q)‖ :=
      polynomial_scaled_estimate q hq hnorm hε hR ha hhalf

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
  have hscaled := polynomial_inverse_scale_lower_bound q hq hnorm γ hγ hε hε1 hR ha hhalf hvalue
  rw [norm_mul]
  calc
    (wmin * sensitivityPolynomialConstant n γ j / (2 * R + 2)) * ε ^ orderBound j =
        wmin * ((sensitivityPolynomialConstant n γ j / (2 * R + 2)) * ε ^ orderBound j) := by ring
    _ ≤ wmin * (‖q.eval a‖ / ‖inverseConstantScale ε (coefficientVector n q)‖) :=
      mul_le_mul_of_nonneg_left hscaled hwmin.le
    _ ≤ ‖w‖ * (‖q.eval a‖ / ‖inverseConstantScale ε (coefficientVector n q)‖) :=
      mul_le_mul_of_nonneg_right hw (div_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = (‖w‖ * ‖q.eval a‖) / ‖inverseConstantScale ε (coefficientVector n q)‖ := by ring

end KungTraub
