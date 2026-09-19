import appendix_b_reference.KungTraubAppendices.ComplexPolynomialCorrections
import appendix_b_reference.KungTraubAppendices.ComplexDerivativeObservations
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Analytic

/-!
# Exact observations of complex polynomial corrections

The original polynomial factor makes every prescribed complex jet vanish.
Mathlib's analytic power-factor derivative theorem (Michail Karatarakis) is
used over ℂ. The polynomial basis is identified
with the previously proved complex affine derivative family; all query orders
and locations, including points outside the unit disc, remain unrestricted.
-/

noncomputable section

open Polynomial
open scoped BigOperators

namespace KungTraubAppendices

/-- A complex linear factor of multiplicity k+1 annihilates the kth derivative at the prescribed node. -/
theorem complexPolynomial_iteratedDeriv_eq_zero {p : Polynomial ℂ} {a : ℂ} {k : ℕ}
    (hdiv : (X - C a) ^ (k + 1) ∣ p) :
    iteratedDeriv k (fun z => p.eval z) a = 0 := by
  sorry

/-- Every saved derivative through the prescribed order vanishes for the exact scaled correction. -/
theorem scaled_complexCorrectionPolynomial_jet_zero {p : Polynomial ℂ} {a : ℂ} {m k : ℕ}
    (hdiv : (X - C a) ^ (m + 1) ∣ p) (hk : k ≤ m)
    (n : ℕ) (ε lam : ℝ) (x : ℂ) (u : EuclideanSpace ℂ (Fin (n + 1))) :
    iteratedDeriv k
      (fun z => (C (lam : ℂ) * complexCorrectionPolynomial p n ε x u).eval z) a = 0 := by
  sorry

/-- Adding the concrete correction preserves an old jet exactly, under only
local differentiability of the old input through that requested order. -/
theorem complexCorrectionPolynomial_preserves_jet {f : ℂ → ℂ} {p : Polynomial ℂ}
    {a : ℂ} {m k : ℕ} (hf : ContDiffAt ℂ k f a)
    (hdiv : (X - C a) ^ (m + 1) ∣ p) (hk : k ≤ m)
    (n : ℕ) (ε lam : ℝ) (x : ℂ) (u : EuclideanSpace ℂ (Fin (n + 1))) :
    iteratedDeriv k (fun z => f z +
      (C (lam : ℂ) * complexCorrectionPolynomial p n ε x u).eval z) a =
      iteratedDeriv k f a := by
  sorry

/-- The polynomial basis for the complete scaled correction, independent of the coefficients. -/
def complexCorrectionPolynomialBasis (p : Polynomial ℂ) (n : ℕ) (lam ε : ℝ) (x : ℂ)
    (i : Fin (n + 1)) : Polynomial ℂ :=
  C (lam : ℂ) * C (if i = 0 then (ε : ℂ) else 1) * (p * (X - C x) ^ i.val)

/-- The actual scaled correction is the linear combination of its concrete polynomial basis. -/
theorem scaled_complexCorrectionPolynomial_eq_basis_sum (p : Polynomial ℂ) (n : ℕ)
    (lam ε : ℝ) (x : ℂ) (u : EuclideanSpace ℂ (Fin (n + 1))) :
    C (lam : ℂ) * complexCorrectionPolynomial p n ε x u =
      ∑ i : Fin (n + 1), C (u i) * complexCorrectionPolynomialBasis p n lam ε x i := by
  sorry

/-- The finite affine family is exactly the polynomial stage member, as a function on all of ℂ. -/
theorem complexFiniteAffineFamily_correction (f₀ p : Polynomial ℂ) (n : ℕ)
    (lam ε : ℝ) (x : ℂ) (u : EuclideanSpace ℂ (Fin (n + 1))) :
    complexFiniteAffineFamily (fun z => f₀.eval z)
      (fun i z => (complexCorrectionPolynomialBasis p n lam ε x i).eval z) u =
      fun z => (f₀ + C (lam : ℂ) * complexCorrectionPolynomial p n ε x u).eval z := by
  sorry

/-- Every actual derivative or idle answer has the exact affine form for this correction family. -/
theorem complexCorrectionPolynomial_affine_answer (f₀ p : Polynomial ℂ) (n : ℕ)
    (lam ε : ℝ) (x : ℂ) (u : EuclideanSpace ℂ (Fin (n + 1))) (q : ComplexQuery) :
    (complexDerivativeAffineObservation (fun z => f₀.eval z)
      (fun i z => (complexCorrectionPolynomialBasis p n lam ε x i).eval z) q).answer u =
      q.answer (fun z => (f₀ + C (lam : ℂ) * complexCorrectionPolynomial p n ε x u).eval z) := by
  sorry

/-- The affine execution and the actual complex polynomial execution have identical output. -/
theorem ComplexAlgorithm.complexCorrectionFamily_run {budget : ℕ} (A : ComplexAlgorithm budget)
    (f₀ p : Polynomial ℂ) (n : ℕ) (lam ε : ℝ) (x start : ℂ)
    (u : EuclideanSpace ℂ (Fin (n + 1))) :
    (A.toAffine (complexDerivativeAffineObservation (fun z => f₀.eval z)
      (fun i z => (complexCorrectionPolynomialBasis p n lam ε x i).eval z))).run u start =
      A.run (fun z => (f₀ + C (lam : ℂ) * complexCorrectionPolynomial p n ε x u).eval z) start := by
  sorry

/-- The embedding preserves each actual query location for the concrete correction family. -/
theorem ComplexAlgorithm.complexCorrectionFamily_actual_location {budget : ℕ}
    (A : ComplexAlgorithm budget) (f₀ p : Polynomial ℂ) (n : ℕ)
    (lam ε : ℝ) (x start : ℂ) (u : EuclideanSpace ℂ (Fin (n + 1))) (j : Fin budget) :
    ((A.toAffine (complexDerivativeAffineObservation (fun z => f₀.eval z)
      (fun i z => (complexCorrectionPolynomialBasis p n lam ε x i).eval z))).actualObservation u start j).location =
      (A.actualQuery (fun z => (f₀ + C (lam : ℂ) * complexCorrectionPolynomial p n ε x u).eval z)
        start j).location := by
  sorry

end KungTraubAppendices
