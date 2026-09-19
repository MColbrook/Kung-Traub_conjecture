import appendix_b_reference.KungTraubAppendices.HermiteBounds
import Mathlib.Topology.Order.Compact

/-!
# The uniform derivative constant in Appendix A

The constant is the maximum of the normalized derivative suprema. Compactness
ensures that each supremum is finite.
-/

noncomputable section

open Set

namespace KungTraubAppendices

/-- The uniform derivative constant `D` of Appendix A. -/
def inverseHermiteDerivativeBound (n : ℕ) (hn : 2 ≤ n) (g : ℝ → ℝ) (K : Set ℝ) : ℝ :=
  max 1 ((Finset.range (n - 1)).sup'
    (Finset.nonempty_range_iff.mpr (by omega))
    (fun j => sSup ((fun t => |iteratedDeriv (j + 2) g t|) '' K) /
      ((j + 2).factorial : ℝ)))

/-- Compactness and local analyticity justify every supremum in the definition. -/
theorem hermite_derivative_image_bddAbove {g : ℝ → ℝ} {K : Set ℝ}
    (hK : IsCompact K) (hg : AnalyticOnNhd ℝ g K) (j : ℕ) :
    BddAbove ((fun t => |iteratedDeriv (j + 2) g t|) '' K) := by
  sorry

theorem one_le_inverseHermiteDerivativeBound (n : ℕ) (hn : 2 ≤ n)
    (g : ℝ → ℝ) (K : Set ℝ) : 1 ≤ inverseHermiteDerivativeBound n hn g K := by
  sorry

theorem inverseHermiteDerivativeBound_pos (n : ℕ) (hn : 2 ≤ n)
    (g : ℝ → ℝ) (K : Set ℝ) : 0 < inverseHermiteDerivativeBound n hn g K := by
  sorry

/-- The full index range has the stated factorial-normalized bound. -/
theorem normalized_derivative_le_inverseHermiteDerivativeBound
    (n : ℕ) (hn : 2 ≤ n) {g : ℝ → ℝ} {K : Set ℝ}
    (hK : IsCompact K) (hg : AnalyticOnNhd ℝ g K)
    {j : ℕ} (hj : j ≤ n - 2) {t : ℝ} (ht : t ∈ K) :
    |iteratedDeriv (j + 2) g t| / ((j + 2).factorial : ℝ) ≤
      inverseHermiteDerivativeBound n hn g K := by
  sorry

end KungTraubAppendices
