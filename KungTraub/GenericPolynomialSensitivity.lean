import KungTraub.RealPolynomialSensitivity

/-!
# Polynomial sensitivity for a prescribed exponent sequence

The supplied exponents may be constant over each evaluation group. The target
exponent is justified by the sum over actual injective rank-increase indices.
All localization constants, multiplicities, and coefficient normalizations are
the same as in the scalar proof.
-/

noncomputable section
open Polynomial
open scoped BigOperators
namespace KungTraub

theorem polynomial_value_lower_bound_of_root_distances_exponents {n j d B : ℕ}
    (E : ℕ → ℕ) (hdn : d ≤ n) (q : Polynomial ℂ) (hdegree : q.natDegree = d)
    (hnorm : ‖coefficientVector n q‖ = 1) (a : ℂ) (ha : ‖a‖ ≤ 1 / 2)
    (β : Fin d → ℂ) (hβ : (List.ofFn β : Multiset ℂ) = q.roots)
    (γ : ℕ → ℝ) (hγ : ∀ i < j, 0 < γ i)
    (indices : Fin d → Fin j) (hinj : Function.Injective indices)
    (hE : (∑ k : Fin d, E (indices k).val) ≤ B)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hdist : ∀ k, γ (indices k).val / uniformWronskianConstant n *
      ε ^ E (indices k).val ≤ ‖a - β k‖) :
    sensitivityPolynomialConstant n γ j * ε ^ B ≤ ‖q.eval a‖ := by
  have hnonneg (k : Fin d) : 0 ≤ min 1 (γ (indices k).val / uniformWronskianConstant n) :=
    le_min zero_le_one (div_nonneg (hγ _ (indices k).isLt).le
      (uniformWronskianConstant_pos n).le)
  have hprod : (∏ k : Fin d, min 1 (γ (indices k).val / uniformWronskianConstant n) *
      ε ^ E (indices k).val) ≤ ∏ k : Fin d, min 1 ‖a - β k‖ := by
    apply Finset.prod_le_prod
    · intro k _
      exact mul_nonneg (hnonneg k) (pow_nonneg hε.le _)
    · intro k _
      exact truncated_distance_scale_lower_bound (pow_nonneg hε.le _)
        (pow_le_one₀ hε.le hε1) (hdist k)
  have hpower : ε ^ B ≤ ε ^ (∑ k : Fin d, E (indices k).val) :=
    pow_le_pow_of_le_one hε.le hε1 hE
  have hrootprod : (∏ k : Fin d, min 1 ‖a - β k‖) =
      (q.roots.map (fun z => min 1 ‖a - z‖)).prod := by
    rw [← hβ]
    simp only [Multiset.map_coe, List.map_ofFn, Multiset.prod_coe, List.prod_ofFn, Function.comp_def]
  calc
    sensitivityPolynomialConstant n γ j * ε ^ B ≤
        sensitivityPolynomialConstant n γ j * ε ^ (∑ k : Fin d, E (indices k).val) :=
      mul_le_mul_of_nonneg_left hpower (sensitivityPolynomialConstant_pos γ hγ).le
    _ ≤ (((4 : ℝ) ^ d)⁻¹ * ∏ k : Fin d, min 1 (γ (indices k).val / uniformWronskianConstant n)) *
        ε ^ (∑ k : Fin d, E (indices k).val) :=
      mul_le_mul_of_nonneg_right (sensitivityPolynomialConstant_le_selected hdn γ hγ indices hinj)
        (pow_nonneg hε.le _)
    _ = (∏ k : Fin d, min 1 (γ (indices k).val / uniformWronskianConstant n) *
        ε ^ E (indices k).val) / 4 ^ d := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
      ring
    _ ≤ (∏ k : Fin d, min 1 ‖a - β k‖) / 4 ^ d :=
      div_le_div_of_nonneg_right hprod (by positivity)
    _ = (q.roots.map (fun z => min 1 ‖a - z‖)).prod / 4 ^ q.natDegree := by rw [hrootprod, hdegree]
    _ ≤ ‖q.eval a‖ := polynomial_product_estimate q (hdegree.trans_le hdn) hnorm ha

theorem polynomial_inverse_scale_lower_bound_exponent {n j B : ℕ} (hB : 0 < B)
    (q : Polynomial ℂ) (hq : q.natDegree ≤ n) (hnorm : ‖coefficientVector n q‖ = 1)
    (γ : ℕ → ℝ) (hγ : ∀ i < j, 0 < γ i)
    {a : ℂ} {ε R : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 < R)
    (ha : ‖a‖ ≤ R * ε) (hhalf : R * ε ≤ 1 / 2)
    (hvalue : sensitivityPolynomialConstant n γ j * ε ^ B ≤ ‖q.eval a‖) :
    (sensitivityPolynomialConstant n γ j / (2 * R + 2)) * ε ^ B ≤
      ‖q.eval a‖ / ‖inverseConstantScale ε (coefficientVector n q)‖ := by
  have hpow : ε ^ B ≤ ε :=
    pow_le_of_le_one hε.le hε1 hB.ne'
  have hscale : sensitivityPolynomialConstant n γ j * ε ^ B ≤ ε :=
    (mul_le_mul_of_nonneg_right (sensitivityPolynomialConstant_le_one γ hγ)
      (pow_nonneg hε.le _)).trans (by simpa using hpow)
  have hmin : sensitivityPolynomialConstant n γ j * ε ^ B ≤ min ε ‖q.eval a‖ :=
    le_min hscale hvalue
  calc
    (sensitivityPolynomialConstant n γ j / (2 * R + 2)) * ε ^ B =
        (sensitivityPolynomialConstant n γ j * ε ^ B) / (2 * R + 2) := by ring
    _ ≤ min ε ‖q.eval a‖ / (2 * R + 2) :=
      div_le_div_of_nonneg_right hmin (by positivity)
    _ ≤ ‖q.eval a‖ / ‖inverseConstantScale ε (coefficientVector n q)‖ :=
      polynomial_scaled_estimate q hq hnorm hε hR ha hhalf

theorem weighted_polynomial_inverse_scale_lower_bound_exponent {n j B : ℕ} (hB : 0 < B)
    (q : Polynomial ℂ) (hq : q.natDegree ≤ n) (hnorm : ‖coefficientVector n q‖ = 1)
    (γ : ℕ → ℝ) (hγ : ∀ i < j, 0 < γ i)
    {a w : ℂ} {ε R wmin : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 < R)
    (hwmin : 0 < wmin) (hw : wmin ≤ ‖w‖)
    (ha : ‖a‖ ≤ R * ε) (hhalf : R * ε ≤ 1 / 2)
    (hvalue : sensitivityPolynomialConstant n γ j * ε ^ B ≤ ‖q.eval a‖) :
    (wmin * sensitivityPolynomialConstant n γ j / (2 * R + 2)) * ε ^ B ≤
      ‖w * q.eval a‖ / ‖inverseConstantScale ε (coefficientVector n q)‖ := by
  have hscaled := polynomial_inverse_scale_lower_bound_exponent hB q hq hnorm γ hγ hε hε1 hR ha hhalf hvalue
  rw [norm_mul]
  calc
    (wmin * sensitivityPolynomialConstant n γ j / (2 * R + 2)) * ε ^ B =
        wmin * ((sensitivityPolynomialConstant n γ j / (2 * R + 2)) * ε ^ B) := by ring
    _ ≤ wmin * (‖q.eval a‖ / ‖inverseConstantScale ε (coefficientVector n q)‖) :=
      mul_le_mul_of_nonneg_left hscaled hwmin.le
    _ ≤ ‖w‖ * (‖q.eval a‖ / ‖inverseConstantScale ε (coefficientVector n q)‖) :=
      mul_le_mul_of_nonneg_right hw (div_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = (‖w‖ * ‖q.eval a‖) / ‖inverseConstantScale ε (coefficientVector n q)‖ := by ring

theorem minimum_degree_kernel_root_distance_bounds_exponents {n j : ℕ} (E : ℕ → ℕ)
    (L : ℕ → Polynomial ℂ →ₗ[ℂ] ℂ) (q : Polynomial ℂ) (hq : q ≠ 0)
    (hLq : ∀ i < j, L i q = 0)
    (hmin : ∀ r : Polynomial ℂ, r ≠ 0 → (∀ i < j, L i r = 0) → q.natDegree ≤ r.natDegree)
    (hdn : q.natDegree ≤ n) (α x : ℂ) (γ : ℕ → ℝ) (ε : ℝ)
    (query : ℕ → Option ℂ)
    (havoid : ∀ i < j, ∀ z ∈ polynomialKernelForbiddenSet L (i + 1) n x (query i),
      γ i * ε ^ E i ≤ ‖α - z‖) :
    ∃ indices : Fin q.natDegree → Fin j, StrictMono indices ∧
      ∃ β : Fin q.natDegree → ℂ, (List.ofFn β : Multiset ℂ) = q.roots ∧
        Antitone (fun k => ‖(α - x) - β k‖) ∧
        ∀ k, γ (indices k).val / uniformWronskianConstant n *
          ε ^ E (indices k).val ≤ ‖(α - x) - β k‖ := by
  obtain ⟨indices, hindices, _, hdim⟩ := minimum_degree_kernel_rank_indices L j q hq hLq hmin
  obtain ⟨β, hβ, hsort⟩ := exists_roots_ordered_by_distance q (α - x)
  refine ⟨indices, hindices, β, hβ, hsort, fun k => ?_⟩
  have hdim' : polynomialKernelDimension L ((indices k).val + 1) q.natDegree = q.natDegree - k.val :=
    hdim k
  have hm : 0 < polynomialKernelDimension L ((indices k).val + 1) q.natDegree := by
    rw [hdim']
    have := k.isLt
    omega
  have hmd : polynomialKernelDimension L ((indices k).val + 1) q.natDegree ≤ q.natDegree := by
    rw [hdim']
    omega
  have hqmem : q ∈ Submodule.span ℂ
      (Set.range (polynomialKernelFamily L ((indices k).val + 1) q.natDegree)) := by
    apply (mem_span_polynomialKernelFamily _ _ _ _).mpr
    refine ⟨le_rfl, fun i hi => hLq i ?_⟩
    have := (indices k).isLt
    omega
  have hroots : ∃ z : Fin (polynomialKernelDimension L ((indices k).val + 1) q.natDegree) → ℂ,
      (∀ i, ‖z i - (α - x)‖ ≤ ‖(α - x) - β k‖) ∧
      (List.ofFn z : Multiset ℂ) ≤ q.roots := by
    rw [hdim']
    exact ordered_roots_suffix_in_disc q (α - x) β hβ hsort k
  have hWavoid : ∀ z : ℂ,
      (polynomialWronskian (polynomialKernelFamily L ((indices k).val + 1) q.natDegree)).eval z = 0 →
      γ (indices k).val * ε ^ E (indices k).val ≤ ‖z - (α - x)‖ := by
    intro z hz
    have hmem := polynomialKernelForbiddenSet_contains_wronskian_zero L ((indices k).val + 1)
      n q.natDegree (by have := k.isLt; omega) hdn x z (query (indices k).val) hz
    have h := havoid (indices k).val (indices k).isLt (x + z) hmem
    have heq : ‖α - (x + z)‖ = ‖z - (α - x)‖ := by
      rw [← norm_neg (z - (α - x))]
      congr 1
      ring
    rwa [heq] at h
  have hbound := root_radius_lower_bound_of_wronskian_avoidance hm hmd hdn
    (polynomialKernelFamily L ((indices k).val + 1) q.natDegree)
    (polynomialKernelFamily_linearIndependent L ((indices k).val + 1) q.natDegree)
    (polynomialKernelFamily_degree_le L ((indices k).val + 1) q.natDegree)
    (α - x) ‖(α - x) - β k‖ (γ (indices k).val * ε ^ E (indices k).val)
    (norm_nonneg _) q hqmem hq hroots hWavoid
  convert hbound using 1
  ring

theorem minimum_degree_kernel_value_lower_bound_exponents {n j B : ℕ}
    (E : ℕ → ℕ)
    (hE : ∀ {d : ℕ} (indices : Fin d → Fin j), Function.Injective indices →
      (∑ k : Fin d, E (indices k).val) ≤ B)
    (L : ℕ → Polynomial ℂ →ₗ[ℂ] ℂ) (q : Polynomial ℂ) (hq : q ≠ 0)
    (hLq : ∀ i < j, L i q = 0)
    (hmin : ∀ r : Polynomial ℂ, r ≠ 0 → (∀ i < j, L i r = 0) → q.natDegree ≤ r.natDegree)
    (hdn : q.natDegree ≤ n) (hnorm : ‖coefficientVector n q‖ = 1)
    (α x : ℂ) (ha : ‖α - x‖ ≤ 1 / 2) (γ : ℕ → ℝ) (hγ : ∀ i < j, 0 < γ i)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (query : ℕ → Option ℂ)
    (havoid : ∀ i < j, ∀ z ∈ polynomialKernelForbiddenSet L (i + 1) n x (query i),
      γ i * ε ^ E i ≤ ‖α - z‖) :
    sensitivityPolynomialConstant n γ j * ε ^ B ≤ ‖q.eval (α - x)‖ := by
  obtain ⟨indices, hindices, β, hβ, _, hdist⟩ :=
    minimum_degree_kernel_root_distance_bounds_exponents E L q hq hLq hmin hdn α x γ ε query havoid
  exact polynomial_value_lower_bound_of_root_distances_exponents E hdn q rfl hnorm (α - x) ha β hβ
    γ hγ indices hindices.injective (hE indices hindices.injective) hε hε1 hdist

end KungTraub

