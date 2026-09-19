import support_reference.KungTraub.RealPolynomialSensitivity

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
  sorry

theorem polynomial_inverse_scale_lower_bound_exponent {n j B : ℕ} (hB : 0 < B)
    (q : Polynomial ℂ) (hq : q.natDegree ≤ n) (hnorm : ‖coefficientVector n q‖ = 1)
    (γ : ℕ → ℝ) (hγ : ∀ i < j, 0 < γ i)
    {a : ℂ} {ε R : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 < R)
    (ha : ‖a‖ ≤ R * ε) (hhalf : R * ε ≤ 1 / 2)
    (hvalue : sensitivityPolynomialConstant n γ j * ε ^ B ≤ ‖q.eval a‖) :
    (sensitivityPolynomialConstant n γ j / (2 * R + 2)) * ε ^ B ≤
      ‖q.eval a‖ / ‖inverseConstantScale ε (coefficientVector n q)‖ := by
  sorry

theorem weighted_polynomial_inverse_scale_lower_bound_exponent {n j B : ℕ} (hB : 0 < B)
    (q : Polynomial ℂ) (hq : q.natDegree ≤ n) (hnorm : ‖coefficientVector n q‖ = 1)
    (γ : ℕ → ℝ) (hγ : ∀ i < j, 0 < γ i)
    {a w : ℂ} {ε R wmin : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 < R)
    (hwmin : 0 < wmin) (hw : wmin ≤ ‖w‖)
    (ha : ‖a‖ ≤ R * ε) (hhalf : R * ε ≤ 1 / 2)
    (hvalue : sensitivityPolynomialConstant n γ j * ε ^ B ≤ ‖q.eval a‖) :
    (wmin * sensitivityPolynomialConstant n γ j / (2 * R + 2)) * ε ^ B ≤
      ‖w * q.eval a‖ / ‖inverseConstantScale ε (coefficientVector n q)‖ := by
  sorry

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
  sorry

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
  sorry

end KungTraub

