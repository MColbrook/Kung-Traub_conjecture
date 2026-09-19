import appendix_reference.KungTraubAppendices.RepeatedRolle

/-!
# Rolle's theorem with arbitrary node multiplicities

A nondecreasing list represents repeated nodes. For each constant block, all
derivatives below its length vanish. Differentiation removes one occurrence
from each block and adds one zero in each strict gap. This retains the complete
closed interval, including when every node coincides.
-/

noncomputable section

open Set

namespace KungTraubAppendices

/-- Equal entries from index `i` through index `j` prescribe the corresponding
vanishing derivative. For a monotone list this describes every multiplicity. -/
def OrderedVanishingJets {n : ℕ} (f : ℝ → ℝ) (x : Fin n → ℝ) : Prop :=
  ∀ i j, i ≤ j → x i = x j → iteratedDeriv (j.val - i.val) f (x i) = 0

theorem OrderedVanishingJets.value {n : ℕ} {f : ℝ → ℝ} {x : Fin n → ℝ}
    (h : OrderedVanishingJets f x) (i : Fin n) : f (x i) = 0 := by
  sorry

/-- A derivative has the full decremented multiplicities, as well as a zero
between each pair of unequal consecutive nodes. -/
theorem exists_derivative_ordered_vanishing_jets {n : ℕ} {f : ℝ → ℝ} {a b : ℝ}
    (x : Fin (n + 1) → ℝ) (hx : Monotone x)
    (hxin : ∀ i, x i ∈ Icc a b) (hf : ContinuousOn f (Icc a b))
    (hjets : OrderedVanishingJets f x) :
    ∃ y : Fin n → ℝ, Monotone y ∧ (∀ i, y i ∈ Icc a b) ∧
      OrderedVanishingJets (deriv f) y := by
  sorry

/-- `n + 1` zeros counted with their full multiplicities force a zero of the
`n`th derivative in the same interval. Arbitrary coincidences are allowed. -/
theorem exists_iteratedDeriv_zero_of_ordered_vanishing_jets (n : ℕ)
    {f : ℝ → ℝ} {a b : ℝ} (x : Fin (n + 1) → ℝ) (hx : Monotone x)
    (hxin : ∀ i, x i ∈ Icc a b) (hjets : OrderedVanishingJets f x)
    (hcont : ∀ k < n, ContinuousOn (iteratedDeriv k f) (Icc a b)) :
    ∃ c ∈ Icc a b, iteratedDeriv n f c = 0 := by
  sorry

end KungTraubAppendices
