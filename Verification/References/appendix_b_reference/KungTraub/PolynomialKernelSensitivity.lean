import appendix_b_reference.KungTraub.PolynomialSensitivity
import appendix_b_reference.KungTraub.ForbiddenWronskians

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
  sorry

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
  sorry

/-- The positive-stage coefficient has the exact formula in the manuscript and
is at most `wmin`, so the same coefficient also covers constant kernel polynomials. -/
theorem sensitivityStageCoefficient_bounds {n j : ℕ} (γ : ℕ → ℝ)
    (hγ : ∀ i < j, 0 < γ i) {wmin R : ℝ} (hwmin : 0 < wmin) (hR : 0 < R) :
    0 < wmin * sensitivityPolynomialConstant n γ j / (2 * R + 2) ∧
      wmin * sensitivityPolynomialConstant n γ j / (2 * R + 2) ≤ wmin := by
  sorry

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
  sorry

end KungTraub
