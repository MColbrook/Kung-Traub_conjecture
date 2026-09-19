import KungTraub.PolynomialSensitivity
import KungTraub.ForbiddenWronskians

/-!
# Sensitivity from the actual prefix polynomial kernels

The rank-increase indices and kernel dimensions come from the actual observation maps.
The forbidden sets are the proved finite sets of shifted Wronskian roots. This module
connects their avoidance to each counted root distance and to the explicit polynomial
value bound.
-/

noncomputable section
open Polynomial
open scoped BigOperators

namespace KungTraub

/-- The manuscript's rank-increase root-distance bounds, with the actual prefix kernels,
their canonical Wronskians, and the actual shifted forbidden sets. -/
theorem minimum_degree_kernel_root_distance_bounds {n j : ℕ}
    (L : ℕ → Polynomial ℂ →ₗ[ℂ] ℂ) (q : Polynomial ℂ) (hq : q ≠ 0)
    (hLq : ∀ i < j, L i q = 0)
    (hmin : ∀ r : Polynomial ℂ, r ≠ 0 → (∀ i < j, L i r = 0) → q.natDegree ≤ r.natDegree)
    (hdn : q.natDegree ≤ n) (α x : ℂ) (γ : ℕ → ℝ) (ε : ℝ)
    (query : ℕ → Option ℂ)
    (havoid : ∀ i < j, ∀ z ∈ polynomialKernelForbiddenSet L (i + 1) n x (query i),
      γ i * ε ^ orderBound i ≤ ‖α - z‖) :
    ∃ indices : Fin q.natDegree → Fin j, StrictMono indices ∧
      ∃ β : Fin q.natDegree → ℂ, (List.ofFn β : Multiset ℂ) = q.roots ∧
        Antitone (fun k => ‖(α - x) - β k‖) ∧
        ∀ k, γ (indices k).val / uniformWronskianConstant n *
          ε ^ orderBound (indices k).val ≤ ‖(α - x) - β k‖ := by
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
      γ (indices k).val * ε ^ orderBound (indices k).val ≤ ‖z - (α - x)‖ := by
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
    (α - x) ‖(α - x) - β k‖ (γ (indices k).val * ε ^ orderBound (indices k).val)
    (norm_nonneg _) q hqmem hq hroots hWavoid
  convert hbound using 1
  ring

/-- The explicit `c_j ε^B_j` bound follows from minimum degree and avoidance of
the actual prefix forbidden sets, including all multiplicities and all unused factors. -/
theorem minimum_degree_kernel_value_lower_bound {n j : ℕ} (hj : 0 < j)
    (L : ℕ → Polynomial ℂ →ₗ[ℂ] ℂ) (q : Polynomial ℂ) (hq : q ≠ 0)
    (hLq : ∀ i < j, L i q = 0)
    (hmin : ∀ r : Polynomial ℂ, r ≠ 0 → (∀ i < j, L i r = 0) → q.natDegree ≤ r.natDegree)
    (hdn : q.natDegree ≤ n) (hnorm : ‖coefficientVector n q‖ = 1)
    (α x : ℂ) (ha : ‖α - x‖ ≤ 1 / 2) (γ : ℕ → ℝ) (hγ : ∀ i < j, 0 < γ i)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (query : ℕ → Option ℂ)
    (havoid : ∀ i < j, ∀ z ∈ polynomialKernelForbiddenSet L (i + 1) n x (query i),
      γ i * ε ^ orderBound i ≤ ‖α - z‖) :
    sensitivityPolynomialConstant n γ j * ε ^ orderBound j ≤ ‖q.eval (α - x)‖ := by
  obtain ⟨indices, hindices, β, hβ, _, hdist⟩ :=
    minimum_degree_kernel_root_distance_bounds L q hq hLq hmin hdn α x γ ε query havoid
  exact polynomial_value_lower_bound_of_root_distances hj hdn q rfl hnorm (α - x) ha β hβ
    γ hγ indices hindices.injective hε hε1 hdist

/-- The positive-stage coefficient has the exact formula in the manuscript and
is at most `wmin`, so the same coefficient also covers constant kernel polynomials. -/
theorem sensitivityStageCoefficient_bounds {n j : ℕ} (γ : ℕ → ℝ)
    (hγ : ∀ i < j, 0 < γ i) {wmin R : ℝ} (hwmin : 0 < wmin) (hR : 0 < R) :
    0 < wmin * sensitivityPolynomialConstant n γ j / (2 * R + 2) ∧
      wmin * sensitivityPolynomialConstant n γ j / (2 * R + 2) ≤ wmin := by
  have hden : 0 < 2 * R + 2 := by positivity
  constructor
  · exact div_pos (mul_pos hwmin (sensitivityPolynomialConstant_pos γ hγ)) hden
  · apply (div_le_iff₀ hden).mpr
    have hsmall := mul_le_mul_of_nonneg_left (sensitivityPolynomialConstant_le_one (n := n) γ hγ) hwmin.le
    have hlarge : wmin ≤ wmin * (2 * R + 2) :=
      le_mul_of_one_le_right hwmin.le (by linarith)
    rw [mul_one] at hsmall
    exact hsmall.trans hlarge

/-- The complex polynomial estimate from avoidance of the prefix forbidden sets. -/
theorem minimum_degree_kernel_weighted_inverse_scale_lower_bound {n j : ℕ} (hj : 0 < j)
    (L : ℕ → Polynomial ℂ →ₗ[ℂ] ℂ) (q : Polynomial ℂ) (hq : q ≠ 0)
    (hLq : ∀ i < j, L i q = 0)
    (hmin : ∀ r : Polynomial ℂ, r ≠ 0 → (∀ i < j, L i r = 0) → q.natDegree ≤ r.natDegree)
    (hdn : q.natDegree ≤ n) (hnorm : ‖coefficientVector n q‖ = 1)
    (α x w : ℂ) (γ : ℕ → ℝ) (hγ : ∀ i < j, 0 < γ i)
    {ε R wmin : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 < R)
    (hwmin : 0 < wmin) (hw : wmin ≤ ‖w‖)
    (ha : ‖α - x‖ ≤ R * ε) (hhalf : R * ε ≤ 1 / 2) (query : ℕ → Option ℂ)
    (havoid : ∀ i < j, ∀ z ∈ polynomialKernelForbiddenSet L (i + 1) n x (query i),
      γ i * ε ^ orderBound i ≤ ‖α - z‖) :
    (wmin * sensitivityPolynomialConstant n γ j / (2 * R + 2)) * ε ^ orderBound j ≤
      ‖w * q.eval (α - x)‖ / ‖inverseConstantScale ε (coefficientVector n q)‖ := by
  apply weighted_polynomial_inverse_scale_lower_bound q hdn hnorm γ hγ hε hε1 hR hwmin hw ha hhalf
  exact minimum_degree_kernel_value_lower_bound hj L q hq hLq hmin hdn hnorm
    α x (ha.trans hhalf) γ hγ hε hε1 query havoid

end KungTraub
