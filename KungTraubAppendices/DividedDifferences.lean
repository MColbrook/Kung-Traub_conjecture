import KungTraubAppendices.ConfluentInterpolation
import Mathlib.Data.List.Sort

/-!
# Confluent divided differences on arbitrary lists

The divided difference is the top coefficient of the Newton interpolation
polynomial, with the nodes sorted and their multiplicities retained. The empty
list receives an arbitrary total value; every mathematical assertion below
specifies a nonempty list. Nodes may coincide.
-/

noncomputable section

open Polynomial Set

namespace KungTraubAppendices

def confluentDividedDifference (f : ℝ → ℝ) (xs : List ℝ) : ℝ :=
  (newtonPolynomial f (xs.mergeSort (· ≤ ·))).coeff (xs.length - 1)

/-- Sorting preserves every node and its multiplicity, so the full confluent
mean-value formula holds without a prescribed ordering or distinctness. -/
theorem confluentDividedDifference_mean_value {n : ℕ} {f : ℝ → ℝ} {a b : ℝ}
    (hf : AnalyticOnNhd ℝ f (Icc a b)) (xs : List ℝ) (hlen : xs.length = n + 1)
    (hxin : ∀ z ∈ xs, z ∈ Icc a b) :
    ∃ c ∈ Icc a b, confluentDividedDifference f xs =
      iteratedDeriv n f c / (n.factorial : ℝ) := by
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
  have hxin' : ∀ i, x i ∈ Icc a b := by
    intro i
    have hmem : x i ∈ ys := List.getElem_mem _
    exact hxin _ (by simpa [ys] using hmem)
  obtain ⟨c, hc, heq⟩ := newtonPolynomial_coefficient_mean_value n hf x hx hxin'
  rw [hlist] at heq
  refine ⟨c, hc, ?_⟩
  have hindex : xs.length - 1 = n := by omega
  simpa only [confluentDividedDifference, hindex] using heq

/-- The factorial-normalized uniform bound includes arbitrary coincident nodes. -/
theorem confluentDividedDifference_abs_le {n : ℕ} {f : ℝ → ℝ} {a b D : ℝ}
    (hf : AnalyticOnNhd ℝ f (Icc a b)) (xs : List ℝ) (hlen : xs.length = n + 1)
    (hxin : ∀ z ∈ xs, z ∈ Icc a b)
    (hbound : ∀ c ∈ Icc a b, |iteratedDeriv n f c| / (n.factorial : ℝ) ≤ D) :
    |confluentDividedDifference f xs| ≤ D := by
  obtain ⟨c, hc, heq⟩ := confluentDividedDifference_mean_value hf xs hlen hxin
  rw [heq, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (n.factorial : ℝ))]
  exact hbound c hc

/-- On the full diagonal the definition gives the exact derivative convention. -/
theorem confluentDividedDifference_replicate (n : ℕ) {f : ℝ → ℝ} {a : ℝ}
    (hf : AnalyticAt ℝ f a) :
    confluentDividedDifference f (List.replicate (n + 1) a) =
      iteratedDeriv n f a / (n.factorial : ℝ) := by
  have hlocal : AnalyticOnNhd ℝ f (Icc a a) := by
    intro z hz
    have hz' : z = a := le_antisymm hz.2 hz.1
    simpa [hz'] using hf
  obtain ⟨c, hc, heq⟩ := confluentDividedDifference_mean_value (n := n) hlocal
    (List.replicate (n + 1) a) (by simp) (fun z hz => by
      have hz' := List.eq_of_mem_replicate hz
      simp [hz'])
  have hc' : c = a := le_antisymm hc.2 hc.1
  simpa [hc'] using heq

end KungTraubAppendices
