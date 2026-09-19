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

/-- Interpolate the values at distinct nodes and one prescribed derivative at `i`.
The formula is total on arbitrary data; its characteristic properties require
the stated membership and injectivity hypotheses. -/
def hermiteWithDerivative (s : Finset ι) (nodes values : ι → 𝕜)
    (i : ι) (d : 𝕜) : 𝕜[X] :=
  Lagrange.interpolate s nodes values +
    C ((d - (Lagrange.interpolate s nodes values).derivative.eval (nodes i)) /
      (Lagrange.nodal s nodes).derivative.eval (nodes i)) * Lagrange.nodal s nodes

/-- Distinct interpolation nodes make the derivative correction denominator nonzero. -/
theorem nodal_derivative_ne_zero_at_node {s : Finset ι} {nodes : ι → 𝕜}
    (hnodes : Set.InjOn nodes s) {i : ι} (hi : i ∈ s) :
    (Lagrange.nodal s nodes).derivative.eval (nodes i) ≠ 0 := by
  sorry

/-- The nodal correction preserves all prescribed values. -/
theorem hermiteWithDerivative_eval {s : Finset ι} {nodes : ι → 𝕜}
    (values : ι → 𝕜) (i : ι) (d : 𝕜) (hnodes : Set.InjOn nodes s)
    {j : ι} (hj : j ∈ s) :
    (hermiteWithDerivative s nodes values i d).eval (nodes j) = values j := by
  sorry

/-- The correction gives precisely the derivative at the distinguished node. -/
theorem hermiteWithDerivative_derivative {s : Finset ι} {nodes : ι → 𝕜}
    (values : ι → 𝕜) (d : 𝕜) (hnodes : Set.InjOn nodes s)
    {i : ι} (hi : i ∈ s) :
    (hermiteWithDerivative s nodes values i d).derivative.eval (nodes i) = d := by
  sorry

/-- With one extra derivative condition, the degree is at most the number of nodes. -/
theorem hermiteWithDerivative_degree_le {s : Finset ι} {nodes : ι → 𝕜}
    (values : ι → 𝕜) (i : ι) (d : 𝕜) (hnodes : Set.InjOn nodes s) :
    (hermiteWithDerivative s nodes values i d).degree ≤ (s.card : WithBot ℕ) := by
  sorry

/-- One value and one derivative reproduce the initial linear Hermite interpolant. -/
theorem hermiteWithDerivative_singleton (nodes values : ι → 𝕜) (i : ι) (d : 𝕜) :
    hermiteWithDerivative {i} nodes values i d =
      C (values i) + C d * (X - C (nodes i)) := by
  sorry

end KungTraubAppendices
