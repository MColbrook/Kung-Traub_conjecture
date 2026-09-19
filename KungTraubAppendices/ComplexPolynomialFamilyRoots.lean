import KungTraubAppendices.ComplexPolynomialCorrections
import KungTraubAppendices.ComplexRoots

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
  constructor
  · intro z hz
    have heq : (f + g).eval z - z = (f.eval z - z) + g.eval z := by
      rw [Polynomial.eval_add]; ring
    rw [heq]
    exact (norm_add_le _ _).trans ((add_le_add (hf z hz).1 (hg.1 z hz)).trans hbudget)
  · intro z hz
    rw [(f + g).deriv, Polynomial.derivative_add, Polynomial.eval_add]
    have heq : f.derivative.eval z + g.derivative.eval z - 1 =
        (f.derivative.eval z - 1) + g.derivative.eval z := by ring
    rw [heq]
    exact (norm_add_le _ _).trans ((add_le_add (hf z hz).2 (hg.2 z hz)).trans hbudget)

/-- The constants 1/2 and 3/2 follow on the full closed unit disc. -/
theorem complexPolynomial_add_spatial_bounds (f g : Polynomial ℂ) {B b : ℝ}
    (hf : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖f.eval z - z‖ ≤ B ∧ ‖f.derivative.eval z - 1‖ ≤ B)
    (hg : ComplexPolynomialDiscBound g 1 b) (hbudget : B + b ≤ 1 / 16)
    {z t : ℂ} (hz : ‖z‖ ≤ 1) (ht : ‖t‖ ≤ 1) :
    (1 / 2 : ℝ) * ‖z - t‖ ≤ ‖(f + g).eval z - (f + g).eval t‖ ∧
      ‖(f + g).eval z - (f + g).eval t‖ ≤ (3 / 2 : ℝ) * ‖z - t‖ := by
  have hnear := complexPolynomial_add_near_identity f g hf hg hbudget
  have hdiff : Differentiable ℂ (fun z => (f + g).eval z) :=
    fun z => (f + g).differentiableAt
  have h := near_identity_bilipschitz_on_unit_disc hdiff (1 / 16) (by simpa using hnear.2) hz ht
  norm_num at h
  simp only [Polynomial.eval_add]
  constructor <;> nlinarith [norm_nonneg (z - t)]

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
  have hex : ∀ u : EuclideanSpace ℂ (Fin (n + 1)), ∃ α : ℂ,
      ‖u‖ ≤ 1 → ‖α‖ ≤ (1 / 16 : ℝ) ∧
      SimpleComplexRoot (fun z => (f + C (lam : ℂ) * complexCorrectionPolynomial p n ε x u).eval z) α ∧
      ∀ z : ℂ, ‖z‖ ≤ 1 →
        (f + C (lam : ℂ) * complexCorrectionPolynomial p n ε x u).eval z = 0 → z = α := by
    intro u
    by_cases hu : ‖u‖ ≤ 1
    · have hnear := complexPolynomial_add_near_identity f _ hf (hg u hu) hbudget
      obtain ⟨α, hα⟩ := exists_unique_simple_root_on_unit_disc
        (f := fun z => (f + C (lam : ℂ) * complexCorrectionPolynomial p n ε x u).eval z)
        (fun z => (f + C (lam : ℂ) * complexCorrectionPolynomial p n ε x u).differentiableAt)
        hnear.1 hnear.2
      exact ⟨α, fun _ => hα⟩
    · exact ⟨0, fun h => False.elim (hu h)⟩
  choose root hroot using hex
  exact ⟨root, hroot⟩

end KungTraubAppendices
