import KungTraubAppendices.HermiteInterpolation
import KungTraubAppendices.HermiteCalculus

/-! The nodal factor with the distinguished node repeated once. -/

noncomputable section

open Polynomial

namespace KungTraubAppendices

variable {ι : Type*}

def doubleNodal (s : Finset ι) (nodes : ι → ℝ) (i : ι) : ℝ[X] :=
  (X - C (nodes i)) * Lagrange.nodal s nodes

theorem doubleNodal_monic (s : Finset ι) (nodes : ι → ℝ) (i : ι) :
    (doubleNodal s nodes i).Monic :=
  (monic_X_sub_C _).mul Lagrange.nodal_monic

theorem doubleNodal_natDegree (s : Finset ι) (nodes : ι → ℝ) (i : ι) :
    (doubleNodal s nodes i).natDegree = s.card + 1 := by
  rw [doubleNodal, natDegree_mul (X_sub_C_ne_zero _) Lagrange.nodal_ne_zero,
    natDegree_X_sub_C, Lagrange.natDegree_nodal, add_comm]

theorem doubleNodal_eval (s : Finset ι) (nodes : ι → ℝ) (i : ι) (t : ℝ) :
    (doubleNodal s nodes i).eval t = (t - nodes i) * ∏ j ∈ s, (t - nodes j) := by
  simp [doubleNodal, Lagrange.eval_nodal]

theorem doubleNodal_eval_at_node {s : Finset ι} (nodes : ι → ℝ) (i : ι)
    {j : ι} (hj : j ∈ s) : (doubleNodal s nodes i).eval (nodes j) = 0 := by
  simp [doubleNodal, Lagrange.eval_nodal_at_node hj]

theorem doubleNodal_derivative_at_node {s : Finset ι} (nodes : ι → ℝ)
    {i : ι} (hi : i ∈ s) : (doubleNodal s nodes i).derivative.eval (nodes i) = 0 := by
  simp [doubleNodal, derivative_mul, Lagrange.eval_nodal_at_node hi]

theorem doubleNodal_eval_ne_zero {s : Finset ι} (nodes : ι → ℝ)
    {i : ι} (hi : i ∈ s) {t : ℝ} (ht : ∀ j ∈ s, t ≠ nodes j) :
    (doubleNodal s nodes i).eval t ≠ 0 := by
  rw [doubleNodal_eval]
  exact mul_ne_zero (sub_ne_zero.mpr (ht i hi))
    (Finset.prod_ne_zero_iff.mpr (fun j hj => sub_ne_zero.mpr (ht j hj)))

theorem doubleNodal_top_derivative (s : Finset ι) (nodes : ι → ℝ) (i : ι) (t : ℝ) :
    iteratedDeriv (s.card + 1) (fun z => (doubleNodal s nodes i).eval z) t =
      ((s.card + 1).factorial : ℝ) :=
  iteratedDeriv_monic_polynomial (doubleNodal_monic s nodes i)
    (doubleNodal_natDegree s nodes i) t

end KungTraubAppendices
