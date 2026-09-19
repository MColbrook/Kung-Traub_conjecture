import appendix_b_reference.KungTraubAppendices.ComplexPolynomialCorrections
import appendix_b_reference.KungTraubAppendices.ComplexRoots

/-!
# Roots and spatial bounds of the actual polynomial stage family

The budgets control the base and each correction separately. Their sum
bounds the actual stage polynomial and its derivative on the whole closed unit
disc. The contraction theorem then gives the selected simple root and
its exact 1/16 location bound, for every parameter in the full unit ball.
-/
noncomputable section
open Polynomial
namespace KungTraubAppendices

/-- Near-identity bounds add on the complete unit disc. -/
theorem complexPolynomial_add_near_identity (f g : Polynomial ℂ) {B b : ℝ}
    (hf : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖f.eval z - z‖ ≤ B ∧ ‖f.derivative.eval z - 1‖ ≤ B)
    (hg : ComplexPolynomialDiscBound g 1 b) (hbudget : B + b ≤ 1 / 16) :
    (∀ z : ℂ, ‖z‖ ≤ 1 → ‖(f + g).eval z - z‖ ≤ (1 / 16 : ℝ)) ∧
    (∀ z : ℂ, ‖z‖ ≤ 1 → ‖deriv (fun t => (f + g).eval t) z - 1‖ ≤ (1 / 16 : ℝ)) := by
  sorry

/-- The constants 1/2 and 3/2 follow on the full closed unit disc. -/
theorem complexPolynomial_add_spatial_bounds (f g : Polynomial ℂ) {B b : ℝ}
    (hf : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖f.eval z - z‖ ≤ B ∧ ‖f.derivative.eval z - 1‖ ≤ B)
    (hg : ComplexPolynomialDiscBound g 1 b) (hbudget : B + b ≤ 1 / 16)
    {z t : ℂ} (hz : ‖z‖ ≤ 1) (ht : ‖t‖ ≤ 1) :
    (1 / 2 : ℝ) * ‖z - t‖ ≤ ‖(f + g).eval z - (f + g).eval t‖ ∧
      ‖(f + g).eval z - (f + g).eval t‖ ≤ (3 / 2 : ℝ) * ‖z - t‖ := by
  sorry

/-- Actual correction families have selected simple roots uniformly over the entire
complex unit parameter ball; values outside that ball need no geometric property. -/
theorem exists_complexPolynomialCorrectionFamily_roots (f p : Polynomial ℂ)
    (n : ℕ) (lam ε : ℝ) (x : ℂ) {B b : ℝ}
    (hf : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖f.eval z - z‖ ≤ B ∧ ‖f.derivative.eval z - 1‖ ≤ B)
    (hg : ∀ u : EuclideanSpace ℂ (Fin (n + 1)), ‖u‖ ≤ 1 →
      ComplexPolynomialDiscBound (C (lam : ℂ) * complexCorrectionPolynomial p n ε x u) 1 b)
    (hbudget : B + b ≤ 1 / 16) :
    ∃ root : EuclideanSpace ℂ (Fin (n + 1)) → ℂ,
      ∀ u, ‖u‖ ≤ 1 →
        ‖root u‖ ≤ (1 / 16 : ℝ) ∧
        SimpleComplexRoot (fun z => (f + C (lam : ℂ) * complexCorrectionPolynomial p n ε x u).eval z) (root u) ∧
        ∀ z : ℂ, ‖z‖ ≤ 1 →
          (f + C (lam : ℂ) * complexCorrectionPolynomial p n ε x u).eval z = 0 → z = root u := by
  sorry

end KungTraubAppendices
