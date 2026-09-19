import KungTraubAppendices.ComplexPolynomialCorrections
import KungTraubAppendices.ComplexDerivativeObservations
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
  obtain ⟨q, rfl⟩ := hdiv
  have hq : ∀ z, AnalyticAt ℂ (fun t => q.eval t) z :=
    fun z => AnalyticOnNhd.eval_polynomial q z (Set.mem_univ z)
  obtain ⟨r, _, hr⟩ := iteratedDeriv_mul_pow_sub_of_analytic (k := k) (t := 1)
    (z₀ := a) hq (R := fun z => (((X - C a) ^ (k + 1)) * q).eval z)
    (by intro z; simp)
  simpa using hr a

/-- Every saved derivative through the prescribed order vanishes for the exact scaled correction. -/
theorem scaled_complexCorrectionPolynomial_jet_zero {p : Polynomial ℂ} {a : ℂ} {m k : ℕ}
    (hdiv : (X - C a) ^ (m + 1) ∣ p) (hk : k ≤ m)
    (n : ℕ) (ε lam : ℝ) (x : ℂ) (u : EuclideanSpace ℂ (Fin (n + 1))) :
    iteratedDeriv k
      (fun z => (C (lam : ℂ) * complexCorrectionPolynomial p n ε x u).eval z) a = 0 := by
  apply complexPolynomial_iteratedDeriv_eq_zero
  exact ((pow_dvd_pow _ (Nat.add_le_add_right hk 1)).trans hdiv).trans
    (scaled_complexCorrectionPolynomial_dvd p n ε lam x u)

/-- Adding the concrete correction preserves an old jet exactly, under only
local differentiability of the old input through that requested order. -/
theorem complexCorrectionPolynomial_preserves_jet {f : ℂ → ℂ} {p : Polynomial ℂ}
    {a : ℂ} {m k : ℕ} (hf : ContDiffAt ℂ k f a)
    (hdiv : (X - C a) ^ (m + 1) ∣ p) (hk : k ≤ m)
    (n : ℕ) (ε lam : ℝ) (x : ℂ) (u : EuclideanSpace ℂ (Fin (n + 1))) :
    iteratedDeriv k (fun z => f z +
      (C (lam : ℂ) * complexCorrectionPolynomial p n ε x u).eval z) a =
      iteratedDeriv k f a := by
  have hg : AnalyticAt ℂ
      (fun z => (C (lam : ℂ) * complexCorrectionPolynomial p n ε x u).eval z) a :=
    AnalyticOnNhd.eval_polynomial _ a (Set.mem_univ a)
  rw [iteratedDeriv_fun_add hf hg.contDiffAt,
    scaled_complexCorrectionPolynomial_jet_zero hdiv hk n ε lam x u, add_zero]

/-- The polynomial basis for the complete scaled correction, independent of the coefficients. -/
def complexCorrectionPolynomialBasis (p : Polynomial ℂ) (n : ℕ) (lam ε : ℝ) (x : ℂ)
    (i : Fin (n + 1)) : Polynomial ℂ :=
  C (lam : ℂ) * C (if i = 0 then (ε : ℂ) else 1) * (p * (X - C x) ^ i.val)

/-- The actual scaled correction is the linear combination of its concrete polynomial basis. -/
theorem scaled_complexCorrectionPolynomial_eq_basis_sum (p : Polynomial ℂ) (n : ℕ)
    (lam ε : ℝ) (x : ℂ) (u : EuclideanSpace ℂ (Fin (n + 1))) :
    C (lam : ℂ) * complexCorrectionPolynomial p n ε x u =
      ∑ i : Fin (n + 1), C (u i) * complexCorrectionPolynomialBasis p n lam ε x i := by
  rw [complexCorrectionPolynomial_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i = 0 <;> simp [complexCorrectionPolynomialBasis, hi, map_mul] <;> ring

/-- The finite affine family is exactly the polynomial stage member, as a function on all of ℂ. -/
theorem complexFiniteAffineFamily_correction (f₀ p : Polynomial ℂ) (n : ℕ)
    (lam ε : ℝ) (x : ℂ) (u : EuclideanSpace ℂ (Fin (n + 1))) :
    complexFiniteAffineFamily (fun z => f₀.eval z)
      (fun i z => (complexCorrectionPolynomialBasis p n lam ε x i).eval z) u =
      fun z => (f₀ + C (lam : ℂ) * complexCorrectionPolynomial p n ε x u).eval z := by
  ext z
  rw [Polynomial.eval_add, scaled_complexCorrectionPolynomial_eq_basis_sum,
    Polynomial.eval_finsetSum]
  simp only [complexFiniteAffineFamily, Polynomial.eval_mul, Polynomial.eval_C]

/-- Every actual derivative or idle answer has the exact affine form for this correction family. -/
theorem complexCorrectionPolynomial_affine_answer (f₀ p : Polynomial ℂ) (n : ℕ)
    (lam ε : ℝ) (x : ℂ) (u : EuclideanSpace ℂ (Fin (n + 1))) (q : ComplexQuery) :
    (complexDerivativeAffineObservation (fun z => f₀.eval z)
      (fun i z => (complexCorrectionPolynomialBasis p n lam ε x i).eval z) q).answer u =
      q.answer (fun z => (f₀ + C (lam : ℂ) * complexCorrectionPolynomial p n ε x u).eval z) := by
  simpa only [complexFiniteAffineFamily_correction] using
    complexPolynomialAffineObservation_answer f₀ (complexCorrectionPolynomialBasis p n lam ε x) q u

/-- The affine execution and the actual complex polynomial execution have identical output. -/
theorem ComplexAlgorithm.complexCorrectionFamily_run {budget : ℕ} (A : ComplexAlgorithm budget)
    (f₀ p : Polynomial ℂ) (n : ℕ) (lam ε : ℝ) (x start : ℂ)
    (u : EuclideanSpace ℂ (Fin (n + 1))) :
    (A.toAffine (complexDerivativeAffineObservation (fun z => f₀.eval z)
      (fun i z => (complexCorrectionPolynomialBasis p n lam ε x i).eval z))).run u start =
      A.run (fun z => (f₀ + C (lam : ℂ) * complexCorrectionPolynomial p n ε x u).eval z) start :=
  A.toAffine_run_eq _ (fun q => complexCorrectionPolynomial_affine_answer f₀ p n lam ε x u q) start

/-- The embedding preserves each actual query location for the concrete correction family. -/
theorem ComplexAlgorithm.complexCorrectionFamily_actual_location {budget : ℕ}
    (A : ComplexAlgorithm budget) (f₀ p : Polynomial ℂ) (n : ℕ)
    (lam ε : ℝ) (x start : ℂ) (u : EuclideanSpace ℂ (Fin (n + 1))) (j : Fin budget) :
    ((A.toAffine (complexDerivativeAffineObservation (fun z => f₀.eval z)
      (fun i z => (complexCorrectionPolynomialBasis p n lam ε x i).eval z))).actualObservation u start j).location =
      (A.actualQuery (fun z => (f₀ + C (lam : ℂ) * complexCorrectionPolynomial p n ε x u).eval z)
        start j).location :=
  A.toAffine_actual_location_eq _
    (fun q => complexCorrectionPolynomial_affine_answer f₀ p n lam ε x u q)
    (fun q => complexDerivativeAffineObservation_location _ _ q) start j

end KungTraubAppendices
