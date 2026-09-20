import KungTraub.Model
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic

/-!
# Interpolation with one derivative condition

This is the polynomial construction in Appendix A of Matthew J. Colbrook's
manuscript. It reuses Mathlib's Lagrange interpolant and nodal polynomial
(Kenny Lau and Wrenna Robson). A multiple of the nodal polynomial changes the
derivative at the distinguished node without changing any observed values.

-/

noncomputable section

open Polynomial

namespace KungTraubAppendices

variable {𝕜 ι : Type*} [Field 𝕜] [DecidableEq ι]

/-- Distinct interpolation nodes make the derivative correction denominator nonzero. -/
theorem nodal_derivative_ne_zero_at_node {s : Finset ι} {nodes : ι → 𝕜}
    (hnodes : Set.InjOn nodes s) {i : ι} (hi : i ∈ s) :
    (Lagrange.nodal s nodes).derivative.eval (nodes i) ≠ 0 := by
  rw [Lagrange.eval_nodal_derivative_eval_node_eq hi, Lagrange.eval_nodal]
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  apply sub_ne_zero.mpr
  intro heq
  exact (Finset.mem_erase.mp hj).1
    (hnodes hi (Finset.mem_of_mem_erase hj) heq).symm

/-- The nodal correction preserves all prescribed values. -/
theorem hermiteWithDerivative_eval {s : Finset ι} {nodes : ι → 𝕜}
    (values : ι → 𝕜) (i : ι) (d : 𝕜) (hnodes : Set.InjOn nodes s)
    {j : ι} (hj : j ∈ s) :
    (hermiteWithDerivative s nodes values i d).eval (nodes j) = values j := by
  simp only [hermiteWithDerivative, eval_add, eval_mul, eval_C,
    Lagrange.eval_nodal_at_node hj, mul_zero, add_zero]
  exact Lagrange.eval_interpolate_at_node values hnodes hj

/-- The correction gives precisely the derivative at the distinguished node. -/
theorem hermiteWithDerivative_derivative {s : Finset ι} {nodes : ι → 𝕜}
    (values : ι → 𝕜) (d : 𝕜) (hnodes : Set.InjOn nodes s)
    {i : ι} (hi : i ∈ s) :
    (hermiteWithDerivative s nodes values i d).derivative.eval (nodes i) = d := by
  have hdenominator := nodal_derivative_ne_zero_at_node hnodes hi
  simp only [hermiteWithDerivative, derivative_add, derivative_mul, derivative_C,
    zero_mul, zero_add, eval_add, eval_mul, eval_C]
  rw [div_mul_cancel₀ _ hdenominator]
  ring

/-- With one extra derivative condition, the degree is at most the number of nodes. -/
theorem hermiteWithDerivative_degree_le {s : Finset ι} {nodes : ι → 𝕜}
    (values : ι → 𝕜) (i : ι) (d : 𝕜) (hnodes : Set.InjOn nodes s) :
    (hermiteWithDerivative s nodes values i d).degree ≤ (s.card : WithBot ℕ) := by
  unfold hermiteWithDerivative
  apply (degree_add_le _ _).trans
  apply max_le
  · exact (Lagrange.degree_interpolate_lt values hnodes).le
  · apply le_trans (degree_mul_le _ _)
    rw [Lagrange.degree_nodal]
    simpa only [zero_add, add_zero, add_comm] using
      add_le_add_right (degree_C_le (a :=
        (d - (Lagrange.interpolate s nodes values).derivative.eval (nodes i)) /
          (Lagrange.nodal s nodes).derivative.eval (nodes i))) (s.card : WithBot ℕ)

/-- One value and one derivative reproduce the initial linear Hermite interpolant. -/
theorem hermiteWithDerivative_singleton (nodes values : ι → 𝕜) (i : ι) (d : 𝕜) :
    hermiteWithDerivative {i} nodes values i d =
      C (values i) + C d * (X - C (nodes i)) := by
  simp [hermiteWithDerivative, Lagrange.nodal]

end KungTraubAppendices
