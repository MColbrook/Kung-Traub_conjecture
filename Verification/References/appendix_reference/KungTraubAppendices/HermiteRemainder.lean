import appendix_reference.KungTraubAppendices.HermiteNodal

/-!
# The inverse Hermite remainder on a closed interval

Subtracting a multiple of the monic nodal polynomial makes the error vanish
at the evaluation point as well as at the interpolation nodes. Rolle's theorem,
with the initial node counted twice, gives the precise factorial normalization.
The inverse function need only be analytic near the specified interval.
-/

noncomputable section

open Polynomial Set

namespace KungTraubAppendices

variable {ι : Type*}

/-- The exact mean-value remainder for arbitrary distinct value nodes and one
derivative condition, evaluated at a new point in the same closed interval. -/
theorem hermite_remainder_at_new_point {s : Finset ι} {nodes : ι → ℝ}
    (hnodes : Set.InjOn nodes s) {i : ι} (hi : i ∈ s)
    {a b t : ℝ} {g : ℝ → ℝ} (hg : AnalyticOnNhd ℝ g (Icc a b))
    (hxin : ∀ j ∈ s, nodes j ∈ Icc a b) (htin : t ∈ Icc a b)
    (ht : ∀ j ∈ s, t ≠ nodes j) {P : ℝ[X]}
    (hdegree : P.degree ≤ (s.card : WithBot ℕ))
    (hvalues : ∀ j ∈ s, P.eval (nodes j) = g (nodes j))
    (hderivative : P.derivative.eval (nodes i) = deriv g (nodes i)) :
    ∃ c ∈ Icc a b, g t - P.eval t =
      iteratedDeriv (s.card + 1) g c / ((s.card + 1).factorial : ℝ) *
        (doubleNodal s nodes i).eval t := by
  sorry

end KungTraubAppendices
