import KungTraubAppendices.NewtonDividedRemainder
import KungTraubAppendices.HermiteUniqueness
import KungTraubAppendices.HermiteBounds

/-!
# The divided difference in the actual inverse Hermite remainder

The Newton polynomial on the repeated initial node and the full list of value
nodes satisfies exactly the observed Hermite conditions. Uniqueness identifies
it with the separately constructed polynomial used by the observation method.
-/

noncomputable section

open Polynomial Set

namespace KungTraubAppendices

/-- The analytical Newton construction is the actual one-derivative Hermite
interpolant whenever the value nodes are distinct. -/
theorem newtonPolynomial_eq_hermiteWithDerivative {n : ℕ} {g : ℝ → ℝ}
    (nodes : Fin (n + 1) → ℝ) (hnodes : Function.Injective nodes)
    (hg : ∀ i, AnalyticAt ℝ g (nodes i)) :
    newtonPolynomial g (nodes 0 :: List.ofFn nodes) =
      hermiteWithDerivative Finset.univ nodes (fun i => g (nodes i)) 0
        (deriv g (nodes 0)) := by
  classical
  let xs := nodes 0 :: List.ofFn nodes
  have hmem : ∀ i, nodes i ∈ List.ofFn nodes := fun i => List.mem_ofFn.mpr ⟨i, rfl⟩
  apply hermiteWithDerivative_unique (fun i => g (nodes i)) (deriv g (nodes 0))
    hnodes.injOn (Finset.mem_univ (0 : Fin (n + 1)))
  · apply degree_le_natDegree.trans
    have h := newtonPolynomial_natDegree_le g xs
    simp only [xs, List.length_cons, List.length_ofFn, Nat.add_sub_cancel] at h
    simpa only [Finset.card_univ, Fintype.card_fin] using (show ((newtonPolynomial g xs).natDegree : WithBot ℕ) ≤ (n + 1 : ℕ) by
      exact_mod_cast h)
  · intro i _
    have hk : 0 < xs.count (nodes i) :=
      List.count_pos_iff.mpr (List.mem_cons_of_mem _ (hmem i))
    simpa only [iteratedDeriv_zero] using newtonPolynomial_jet_eq xs (hg i) hk
  · have hcount : 0 < (List.ofFn nodes).count (nodes 0) := List.count_pos_iff.mpr (hmem 0)
    have hk : 1 < xs.count (nodes 0) := by
      change 1 < (nodes 0 :: List.ofFn nodes).count (nodes 0)
      rw [List.count_cons_self]
      omega
    have hjet := newtonPolynomial_jet_eq xs (hg 0) hk
    simpa only [iteratedDeriv_one, Polynomial.deriv] using hjet

/-- The Hermite remainder coefficient is the canonical divided difference
on the evaluation point and all value nodes, with the initial node repeated. -/
theorem hermiteWithDerivative_dividedDifference_remainder {n : ℕ} {g : ℝ → ℝ}
    (nodes : Fin (n + 1) → ℝ) (hnodes : Function.Injective nodes)
    (hg : ∀ i, AnalyticAt ℝ g (nodes i)) (t : ℝ) (hgt : AnalyticAt ℝ g t) :
    g t - (hermiteWithDerivative Finset.univ nodes (fun i => g (nodes i)) 0
        (deriv g (nodes 0))).eval t =
      confluentDividedDifference g (t :: nodes 0 :: List.ofFn nodes) *
        (doubleNodal Finset.univ nodes 0).eval t := by
  have ha : ∀ z ∈ t :: nodes 0 :: List.ofFn nodes, AnalyticAt ℝ g z := by
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hgt
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hg 0
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
    exact hg i
  have heq := newtonPolynomial_dividedDifference_remainder
    (nodes 0 :: List.ofFn nodes) t ha
  rw [newtonPolynomial_eq_hermiteWithDerivative nodes hnodes hg] at heq
  rw [doubleNodal_eval]
  simpa only [List.map_cons, List.prod_cons, List.map_ofFn, List.prod_ofFn, Function.comp_apply] using heq

/-- At zero this is the signed coefficient formula of Appendix A, with
order `n+2`, exactly `n+3` nodes, and the distinguished square. -/
theorem hermiteWithDerivative_dividedDifference_remainder_zero {n : ℕ} {g : ℝ → ℝ}
    (nodes : Fin (n + 1) → ℝ) (hnodes : Function.Injective nodes)
    (hg : ∀ i, AnalyticAt ℝ g (nodes i)) (hgzero : AnalyticAt ℝ g 0) :
    (hermiteWithDerivative Finset.univ nodes (fun i => g (nodes i)) 0
        (deriv g (nodes 0))).eval 0 - g 0 =
      (-1 : ℝ) ^ (n + 1) *
        confluentDividedDifference g (0 :: nodes 0 :: List.ofFn nodes) *
        (nodes 0) ^ 2 * ∏ i ∈ (Finset.univ : Finset (Fin (n + 1))).erase 0, nodes i := by
  have heq := hermiteWithDerivative_dividedDifference_remainder nodes hnodes hg 0 hgzero
  have hneg := doubleNodal_zero_neg nodes (Finset.mem_univ (0 : Fin (n + 1)))
  simp only [Finset.card_univ, Fintype.card_fin] at hneg
  calc
    _ = -(g 0 - (hermiteWithDerivative Finset.univ nodes (fun i => g (nodes i)) 0
        (deriv g (nodes 0))).eval 0) := by ring
    _ = confluentDividedDifference g (0 :: nodes 0 :: List.ofFn nodes) *
        (-(doubleNodal Finset.univ nodes 0).eval 0) := by rw [heq]; ring
    _ = _ := by rw [hneg]; ring

end KungTraubAppendices
