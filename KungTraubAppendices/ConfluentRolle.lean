import KungTraubAppendices.RepeatedRolle

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
  simpa using h i i le_rfl rfl

/-- A derivative has the full decremented multiplicities, as well as a zero
between each pair of unequal consecutive nodes. -/
theorem exists_derivative_ordered_vanishing_jets {n : ℕ} {f : ℝ → ℝ} {a b : ℝ}
    (x : Fin (n + 1) → ℝ) (hx : Monotone x)
    (hxin : ∀ i, x i ∈ Icc a b) (hf : ContinuousOn f (Icc a b))
    (hjets : OrderedVanishingJets f x) :
    ∃ y : Fin n → ℝ, Monotone y ∧ (∀ i, y i ∈ Icc a b) ∧
      OrderedVanishingJets (deriv f) y := by
  have hex : ∀ i : Fin n, ∃ c,
      x i.castSucc ≤ c ∧ c ≤ x i.succ ∧
      (x i.castSucc < x i.succ → x i.castSucc < c ∧ c < x i.succ) ∧
      deriv f c = 0 := by
    intro i
    have hstep : x i.castSucc ≤ x i.succ :=
      hx (Fin.le_iff_val_le_val.mpr (Nat.le_succ i.val))
    by_cases heq : x i.castSucc = x i.succ
    · refine ⟨x i.castSucc, le_rfl, hstep, ?_, ?_⟩
      · intro hlt
        exact False.elim (hlt.ne heq)
      · have hj := hjets i.castSucc i.succ
          (Fin.le_iff_val_le_val.mpr (Nat.le_succ i.val)) heq
        simpa using hj
    · obtain ⟨c, hc, hd⟩ := exists_deriv_eq_zero (lt_of_le_of_ne hstep heq)
        (hf.mono (fun z hz => ⟨(hxin i.castSucc).1.trans hz.1,
          hz.2.trans (hxin i.succ).2⟩))
        ((hjets.value i.castSucc).trans (hjets.value i.succ).symm)
      exact ⟨c, hc.1.le, hc.2.le, fun _ => hc, hd⟩
  choose y hy using hex
  refine ⟨y, ?_, ?_, ?_⟩
  · intro i j hij
    rcases lt_or_eq_of_le hij with hij | rfl
    · have hmid : x i.succ ≤ x j.castSucc := hx (by simpa using hij)
      exact (hy i).2.1.trans (hmid.trans (hy j).1)
    · exact le_rfl
  · intro i
    exact ⟨(hxin i.castSucc).1.trans (hy i).1,
      (hy i).2.1.trans (hxin i.succ).2⟩
  · intro i j hij heq
    rcases lt_or_eq_of_le hij with hlt | rfl
    · have hmid : x i.succ ≤ x j.castSucc := hx (by simpa using hlt)
      have hfirst : x i.castSucc = x i.succ := by
        by_contra hne
        have hstrict := (hy i).2.2.1 (lt_of_le_of_ne
          (hx (Fin.le_iff_val_le_val.mpr (Nat.le_succ i.val))) hne)
        have hjleft := (hy j).1
        linarith
      have hlast : x j.castSucc = x j.succ := by
        by_contra hne
        have hstrict := (hy j).2.2.1 (lt_of_le_of_ne
          (hx (Fin.le_iff_val_le_val.mpr (Nat.le_succ j.val))) hne)
        have hiright := (hy i).2.1
        linarith
      have hleft : x i.castSucc = y i := by
        have hl := (hy i).1
        have hr := (hy i).2.1
        linarith
      have hright : x j.succ = y j := by
        have hl := (hy j).1
        have hr := (hy j).2.1
        linarith
      have horder : i.castSucc ≤ j.succ := by
        change i.val ≤ j.val + 1
        have := Fin.le_iff_val_le_val.mp hij
        omega
      have hnode : x i.castSucc = x j.succ := by rw [hleft, hright, heq]
      have hj := hjets i.castSucc j.succ horder hnode
      have hindex : j.val + 1 - i.val = (j.val - i.val) + 1 := by
        have := Fin.le_iff_val_le_val.mp hij
        omega
      change iteratedDeriv (j.val + 1 - i.val) f (x i.castSucc) = 0 at hj
      rw [hindex, iteratedDeriv_succ', hleft] at hj
      exact hj
    · simpa using (hy i).2.2.2

/-- `n + 1` zeros counted with their full multiplicities force a zero of the
`n`th derivative in the same interval. Arbitrary coincidences are allowed. -/
theorem exists_iteratedDeriv_zero_of_ordered_vanishing_jets (n : ℕ)
    {f : ℝ → ℝ} {a b : ℝ} (x : Fin (n + 1) → ℝ) (hx : Monotone x)
    (hxin : ∀ i, x i ∈ Icc a b) (hjets : OrderedVanishingJets f x)
    (hcont : ∀ k < n, ContinuousOn (iteratedDeriv k f) (Icc a b)) :
    ∃ c ∈ Icc a b, iteratedDeriv n f c = 0 := by
  induction n generalizing f with
  | zero => exact ⟨x 0, hxin 0, by simpa using hjets.value 0⟩
  | succ n ih =>
    obtain ⟨y, hy, hyin, hyjets⟩ := exists_derivative_ordered_vanishing_jets x hx hxin
      (by simpa using hcont 0 (Nat.zero_lt_succ n)) hjets
    obtain ⟨c, hc, hderiv⟩ := ih y hy hyin hyjets (fun k hk => by
      rw [← iteratedDeriv_succ']
      exact hcont (k + 1) (by omega))
    exact ⟨c, hc, by simpa only [iteratedDeriv_succ'] using hderiv⟩

end KungTraubAppendices
