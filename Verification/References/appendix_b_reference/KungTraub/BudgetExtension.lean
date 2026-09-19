import appendix_b_reference.KungTraub.DiagonalEstimates

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
    extendBudget b s next i = b i := by
  sorry

theorem extendBudget_next (b : ℕ → ℝ) (s : ℕ) (next : ℝ) :
    extendBudget b s next (s + 1) = next := by
  sorry

theorem extendBudget_pos {b : ℕ → ℝ} {s : ℕ} {next : ℝ}
    (hb : ∀ i, 0 < b i) (hnext : 0 < next) (i : ℕ) :
    0 < extendBudget b s next i := by
  sorry

theorem extendBudget_half {b : ℕ → ℝ} {s : ℕ} {next : ℝ}
    (hb : ∀ i, b (i + 1) ≤ b i / 2) (hnext : next ≤ b s / 2) (i : ℕ) :
    extendBudget b s next (i + 1) ≤ extendBudget b s next i / 2 := by
  sorry

theorem extendBudget_initial (b : ℕ → ℝ) (s : ℕ) (next : ℝ) :
    extendBudget b s next 0 = b 0 := by
  sorry

theorem extendBudget_initial_bound {b : ℕ → ℝ} {s : ℕ} {next C : ℝ}
    (hb : b 0 ≤ C) : extendBudget b s next 0 ≤ C := by
  sorry

end KungTraub
