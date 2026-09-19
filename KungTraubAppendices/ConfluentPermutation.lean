import KungTraubAppendices.ConfluentUniqueness
import KungTraubAppendices.DividedDifferences

/-! The constructed Newton interpolant is independent of node ordering. -/

noncomputable section

open Polynomial Set

namespace KungTraubAppendices

/-- Uniqueness expressed on an arbitrary nonempty list, retaining every
prescribed derivative through its actual occurrence count. -/
theorem newtonPolynomial_unique_sorted_list {n : ℕ} {f : ℝ → ℝ}
    (xs : List ℝ) (hlen : xs.length = n + 1)
    (hf : ∀ z ∈ xs, AnalyticAt ℝ f z) {P : ℝ[X]}
    (hdegree : P.degree ≤ (n : WithBot ℕ))
    (hdata : ∀ z ∈ xs, ∀ k : ℕ, k < xs.count z →
      iteratedDeriv k (fun t => P.eval t) z = iteratedDeriv k f z) :
    P = newtonPolynomial f (xs.mergeSort (· ≤ ·)) := by
  let ys := xs.mergeSort (· ≤ ·)
  have hylen : ys.length = n + 1 := by simpa [ys] using hlen
  let x : Fin (n + 1) → ℝ := fun i => ys[i.val]'(by rw [hylen]; exact i.isLt)
  have hlist : List.ofFn x = ys := by
    apply List.ext_getElem
    · simpa using hylen.symm
    · intro k hk hk'
      simp only [List.getElem_ofFn]
      rfl
  have hx : Monotone x := by
    intro i j hij
    exact (List.sortedLE_mergeSort (l := xs)).monotone_get
      (show (⟨i.val, by rw [hylen]; exact i.isLt⟩ : Fin ys.length) ≤
        ⟨j.val, by rw [hylen]; exact j.isLt⟩ from hij)
  have hxmem : ∀ i, x i ∈ xs := by
    intro i
    have hm : x i ∈ ys := List.getElem_mem _
    simpa [ys] using hm
  have hcount : ∀ z, ys.count z = xs.count z :=
    (List.mergeSort_perm xs (· ≤ ·)).count_eq
  have heq := newtonPolynomial_unique n x hx (fun i => hf _ (hxmem i)) hdegree
    (fun i k hk => by
      have hk' : k < (List.ofFn x).count (x i) := hk
      rw [hlist, hcount] at hk'
      exact hdata _ (hxmem i) k hk')
  simpa only [hlist] using heq

/-- Sorting changes no interpolation condition and hence no polynomial. -/
theorem newtonPolynomial_eq_mergeSort {f : ℝ → ℝ} (xs : List ℝ)
    (hf : ∀ z ∈ xs, AnalyticAt ℝ f z) :
    newtonPolynomial f xs = newtonPolynomial f (xs.mergeSort (· ≤ ·)) := by
  cases xs with
  | nil => simp
  | cons a xs =>
    apply newtonPolynomial_unique_sorted_list (n := xs.length) (a :: xs) (by simp) hf
    · apply degree_le_natDegree.trans
      have h := newtonPolynomial_natDegree_le f (a :: xs)
      simp only [List.length_cons, Nat.add_sub_cancel] at h
      exact_mod_cast h
    · intro z hz k hk
      exact newtonPolynomial_jet_eq (a :: xs) (hf z hz) hk

/-- The canonical divided difference is the coefficient in any ordering. -/
theorem confluentDividedDifference_eq_coeff {f : ℝ → ℝ} (xs : List ℝ)
    (hf : ∀ z ∈ xs, AnalyticAt ℝ f z) :
    confluentDividedDifference f xs = (newtonPolynomial f xs).coeff (xs.length - 1) := by
  rw [confluentDividedDifference, ← newtonPolynomial_eq_mergeSort xs hf]

/-- The canonical definition retains only the node multiset, including all
multiplicities. This identity itself requires no regularity assumption. -/
theorem confluentDividedDifference_perm (f : ℝ → ℝ) {xs ys : List ℝ}
    (h : xs.Perm ys) : confluentDividedDifference f xs = confluentDividedDifference f ys := by
  have hsort : xs.mergeSort (· ≤ ·) = ys.mergeSort (· ≤ ·) :=
    ((List.mergeSort_perm xs (· ≤ ·)).trans (h.trans
      (List.mergeSort_perm ys (· ≤ ·)).symm)).eq_of_pairwise'
      (List.sortedLE_mergeSort (l := xs)).pairwise
      (List.sortedLE_mergeSort (l := ys)).pairwise
  simp only [confluentDividedDifference, hsort, h.length_eq]

end KungTraubAppendices
