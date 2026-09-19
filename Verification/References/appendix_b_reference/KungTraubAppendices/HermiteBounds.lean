import appendix_b_reference.KungTraubAppendices.HermiteRemainder

/-!
# Exact remainder and uniform bound for the constructed interpolant

The evaluation point may coincide with any interpolation node. The distinguished
node contributes the squared factor in the error bound at zero.
-/

noncomputable section

open Polynomial Set

namespace KungTraubAppendices

variable {ι : Type*} [DecidableEq ι]

/-- The actual interpolation polynomial satisfies the factorial remainder on
the entire closed interval, including evaluation at an existing node. -/
theorem hermiteWithDerivative_remainder {s : Finset ι} {nodes : ι → ℝ}
    (hnodes : Set.InjOn nodes s) {i : ι} (hi : i ∈ s)
    {a b t : ℝ} {g : ℝ → ℝ} (hg : AnalyticOnNhd ℝ g (Icc a b))
    (hxin : ∀ j ∈ s, nodes j ∈ Icc a b) (htin : t ∈ Icc a b) :
    ∃ c ∈ Icc a b, g t -
        (hermiteWithDerivative s nodes (fun j => g (nodes j)) i (deriv g (nodes i))).eval t =
      iteratedDeriv (s.card + 1) g c / ((s.card + 1).factorial : ℝ) *
        (doubleNodal s nodes i).eval t := by
  sorry

/-- A uniform bound on the normalized derivative gives the same bound on the
Hermite remainder coefficient, with the same factorial constant. -/
theorem hermiteWithDerivative_error_bound {s : Finset ι} {nodes : ι → ℝ}
    (hnodes : Set.InjOn nodes s) {i : ι} (hi : i ∈ s)
    {a b t D : ℝ} {g : ℝ → ℝ} (hg : AnalyticOnNhd ℝ g (Icc a b))
    (hxin : ∀ j ∈ s, nodes j ∈ Icc a b) (htin : t ∈ Icc a b)
    (hbound : ∀ c ∈ Icc a b,
      |iteratedDeriv (s.card + 1) g c| / ((s.card + 1).factorial : ℝ) ≤ D) :
    |g t - (hermiteWithDerivative s nodes (fun j => g (nodes j))
        i (deriv g (nodes i))).eval t| ≤ D * |(doubleNodal s nodes i).eval t| := by
  sorry

/-- At zero the repeated distinguished node supplies precisely its square. -/
theorem doubleNodal_zero_abs {s : Finset ι} (nodes : ι → ℝ) {i : ι} (hi : i ∈ s) :
    |(doubleNodal s nodes i).eval 0| =
      (nodes i) ^ 2 * ∏ j ∈ s.erase i, |nodes j| := by
  sorry

/-- The uniform inverse Hermite error estimate used in the induction. -/
theorem hermiteWithDerivative_error_bound_zero {s : Finset ι} {nodes : ι → ℝ}
    (hnodes : Set.InjOn nodes s) {i : ι} (hi : i ∈ s)
    {a b D : ℝ} {g : ℝ → ℝ} (hg : AnalyticOnNhd ℝ g (Icc a b))
    (hxin : ∀ j ∈ s, nodes j ∈ Icc a b) (hzero : (0 : ℝ) ∈ Icc a b)
    (hbound : ∀ c ∈ Icc a b,
      |iteratedDeriv (s.card + 1) g c| / ((s.card + 1).factorial : ℝ) ≤ D) :
    |(hermiteWithDerivative s nodes (fun j => g (nodes j))
        i (deriv g (nodes i))).eval 0 - g 0| ≤
      D * (nodes i) ^ 2 * ∏ j ∈ s.erase i, |nodes j| := by
  sorry

/-- The sign at zero is exactly the sign in the remainder formula. -/
theorem doubleNodal_zero_neg {s : Finset ι} (nodes : ι → ℝ) {i : ι} (hi : i ∈ s) :
    -(doubleNodal s nodes i).eval 0 =
      (-1 : ℝ) ^ s.card * (nodes i) ^ 2 * ∏ j ∈ s.erase i, nodes j := by
  sorry

/-- The signed remainder at zero, including the case of a single value node.
For `s.card = j + 1` this gives exactly `(-1)^(j+1)` and `(j+2)!`. -/
theorem hermiteWithDerivative_remainder_zero {s : Finset ι} {nodes : ι → ℝ}
    (hnodes : Set.InjOn nodes s) {i : ι} (hi : i ∈ s)
    {a b : ℝ} {g : ℝ → ℝ} (hg : AnalyticOnNhd ℝ g (Icc a b))
    (hxin : ∀ j ∈ s, nodes j ∈ Icc a b) (hzero : (0 : ℝ) ∈ Icc a b) :
    ∃ c ∈ Icc a b,
      (hermiteWithDerivative s nodes (fun j => g (nodes j))
        i (deriv g (nodes i))).eval 0 - g 0 =
      (-1 : ℝ) ^ s.card *
        (iteratedDeriv (s.card + 1) g c / ((s.card + 1).factorial : ℝ)) *
        (nodes i) ^ 2 * ∏ j ∈ s.erase i, nodes j := by
  sorry

end KungTraubAppendices
