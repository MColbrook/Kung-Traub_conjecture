import appendix_reference.KungTraubAppendices.HermiteInterpolation
import appendix_reference.KungTraubAppendices.HermiteCalculus

/-! The nodal factor with the distinguished node repeated once. -/

noncomputable section

open Polynomial

namespace KungTraubAppendices

variable {ι : Type*}

def doubleNodal (s : Finset ι) (nodes : ι → ℝ) (i : ι) : ℝ[X] :=
  (X - C (nodes i)) * Lagrange.nodal s nodes

theorem doubleNodal_monic (s : Finset ι) (nodes : ι → ℝ) (i : ι) :
    (doubleNodal s nodes i).Monic := by
  sorry

theorem doubleNodal_natDegree (s : Finset ι) (nodes : ι → ℝ) (i : ι) :
    (doubleNodal s nodes i).natDegree = s.card + 1 := by
  sorry

theorem doubleNodal_eval (s : Finset ι) (nodes : ι → ℝ) (i : ι) (t : ℝ) :
    (doubleNodal s nodes i).eval t = (t - nodes i) * ∏ j ∈ s, (t - nodes j) := by
  sorry

theorem doubleNodal_eval_at_node {s : Finset ι} (nodes : ι → ℝ) (i : ι)
    {j : ι} (hj : j ∈ s) : (doubleNodal s nodes i).eval (nodes j) = 0 := by
  sorry

theorem doubleNodal_derivative_at_node {s : Finset ι} (nodes : ι → ℝ)
    {i : ι} (hi : i ∈ s) : (doubleNodal s nodes i).derivative.eval (nodes i) = 0 := by
  sorry

theorem doubleNodal_eval_ne_zero {s : Finset ι} (nodes : ι → ℝ)
    {i : ι} (hi : i ∈ s) {t : ℝ} (ht : ∀ j ∈ s, t ≠ nodes j) :
    (doubleNodal s nodes i).eval t ≠ 0 := by
  sorry

theorem doubleNodal_top_derivative (s : Finset ι) (nodes : ι → ℝ) (i : ι) (t : ℝ) :
    iteratedDeriv (s.card + 1) (fun z => (doubleNodal s nodes i).eval z) t =
      ((s.card + 1).factorial : ℝ) := by
  sorry

end KungTraubAppendices
