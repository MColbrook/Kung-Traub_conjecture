import KungTraub.DiagonalEstimates

/-!
# Extending a finite budget prefix

A newly selected positive budget changes only the future of a history. The
extension keeps every earlier value exactly and supplies a geometric tail,
so it is a complete positive sequence available to the next induction step.
-/

noncomputable section

namespace KungTraub

def extendBudget (b : ℕ → ℝ) (s : ℕ) (next : ℝ) (i : ℕ) : ℝ :=
  if i ≤ s then b i else next * (1 / 2) ^ (i - (s + 1))

theorem extendBudget_agrees {b : ℕ → ℝ} {s i : ℕ} (next : ℝ) (hi : i ≤ s) :
    extendBudget b s next i = b i := if_pos hi

theorem extendBudget_next (b : ℕ → ℝ) (s : ℕ) (next : ℝ) :
    extendBudget b s next (s + 1) = next := by simp [extendBudget]

theorem extendBudget_pos {b : ℕ → ℝ} {s : ℕ} {next : ℝ}
    (hb : ∀ i, 0 < b i) (hnext : 0 < next) (i : ℕ) :
    0 < extendBudget b s next i := by
  unfold extendBudget
  split_ifs with hi
  · exact hb i
  · positivity

theorem extendBudget_half {b : ℕ → ℝ} {s : ℕ} {next : ℝ}
    (hb : ∀ i, b (i + 1) ≤ b i / 2) (hnext : next ≤ b s / 2) (i : ℕ) :
    extendBudget b s next (i + 1) ≤ extendBudget b s next i / 2 := by
  rcases lt_trichotomy i s with hi | hi | hi
  · rw [extendBudget_agrees next (by omega : i + 1 ≤ s), extendBudget_agrees next hi.le]
    exact hb i
  · subst i
    rw [extendBudget_next, extendBudget_agrees next le_rfl]
    exact hnext
  · have hpow : i + 1 - (s + 1) = (i - (s + 1)) + 1 := by omega
    rw [extendBudget, if_neg (by omega : ¬ i + 1 ≤ s), extendBudget,
      if_neg (by omega : ¬ i ≤ s), hpow, pow_succ]
    exact le_of_eq (by ring)

theorem extendBudget_initial (b : ℕ → ℝ) (s : ℕ) (next : ℝ) :
    extendBudget b s next 0 = b 0 := extendBudget_agrees next (Nat.zero_le s)

theorem extendBudget_initial_bound {b : ℕ → ℝ} {s : ℕ} {next C : ℝ}
    (hb : b 0 ≤ C) : extendBudget b s next 0 ≤ C := by
  rw [extendBudget_initial]
  exact hb

end KungTraub
