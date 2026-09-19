import KungTraub.PolynomialFrames
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

/-!
# Normalizing polynomial spaces in coefficient norm

These lemmas construct the required orthonormal coefficient frame from every
independent bounded-degree family, and normalize any nonzero member without changing
its roots. Gram--Schmidt and its span theorem are reused from Mathlib's implementation
by Jiale Miao, Kevin Buzzard and Alexander Bentkamp.
-/

noncomputable section

open Polynomial InnerProductSpace
open scoped BigOperators

namespace KungTraub

/-- Bounded-degree coefficient extraction preserves linear independence. -/
theorem polynomial_coefficientVector_linearIndependent {m d : ℕ}
    (p : Fin m → Polynomial ℂ) (hp : LinearIndependent ℂ p)
    (hdeg : ∀ i, (p i).natDegree ≤ d) :
    LinearIndependent ℂ (fun i => coefficientVector d (p i)) := by
  apply LinearIndependent.of_comp (polynomialOfCoefficientsLinearMap d)
  change LinearIndependent ℂ (fun i => polynomialOfCoefficients (coefficientVector d (p i)))
  simpa only [fun i => polynomialOfCoefficients_coefficientVector (p i) (hdeg i)] using hp

/-- Every independent bounded-degree polynomial family admits a coefficient-orthonormal
family of the same size and with exactly the same span. -/
theorem exists_polynomial_coefficient_orthonormal_frame {m d : ℕ}
    (p : Fin m → Polynomial ℂ) (hp : LinearIndependent ℂ p)
    (hdeg : ∀ i, (p i).natDegree ≤ d) :
    ∃ q : Fin m → Polynomial ℂ, (∀ i, (q i).natDegree ≤ d) ∧
      Orthonormal ℂ (fun i => coefficientVector d (q i)) ∧
      LinearIndependent ℂ q ∧
      Submodule.span ℂ (Set.range q) = Submodule.span ℂ (Set.range p) := by
  classical
  let v : Fin m → EuclideanSpace ℂ (Fin (d + 1)) := fun i => coefficientVector d (p i)
  let w := gramSchmidtNormed ℂ v
  have hv : LinearIndependent ℂ v := polynomial_coefficientVector_linearIndependent p hp hdeg
  have hw : Orthonormal ℂ w := gramSchmidtNormed_orthonormal hv
  have hspan : Submodule.span ℂ (Set.range w) = Submodule.span ℂ (Set.range v) := by
    exact (span_gramSchmidtNormed_range (𝕜 := ℂ) v).trans (span_gramSchmidt ℂ v)
  let q : Fin m → Polynomial ℂ := fun i => polynomialOfCoefficients (w i)
  have hqortho : Orthonormal ℂ (fun i => coefficientVector d (q i)) := by
    simpa only [q, coefficientVector_polynomialOfCoefficients] using hw
  have hqind : LinearIndependent ℂ q := by
    apply LinearIndependent.of_comp (polynomialCoefficientLinearMap d)
    exact hqortho.linearIndependent
  have hmap := congrArg (Submodule.map (polynomialOfCoefficientsLinearMap d)) hspan
  rw [Submodule.map_span, Submodule.map_span, ← Set.range_comp, ← Set.range_comp] at hmap
  have hqspan : Submodule.span ℂ (Set.range q) = Submodule.span ℂ (Set.range p) := by
    simpa only [Function.comp_def, polynomialOfCoefficientsLinearMap_apply, v,
      fun i => polynomialOfCoefficients_coefficientVector (p i) (hdeg i)] using hmap
  exact ⟨q, fun i => polynomialOfCoefficients_natDegree_le (w i), hqortho, hqind, hqspan⟩

/-- A nonzero bounded-degree polynomial has a nonzero coefficient vector. -/
theorem coefficientVector_ne_zero_of_natDegree_le {d : ℕ} (q : Polynomial ℂ)
    (hq : q ≠ 0) (hdeg : q.natDegree ≤ d) : coefficientVector d q ≠ 0 := by
  intro hz
  apply hq
  rw [← polynomialOfCoefficients_coefficientVector q hdeg, hz]
  change polynomialOfCoefficientsLinearMap d 0 = 0
  exact map_zero _

/-- Scalar normalization preserves the degree bound and complete root multiset. -/
theorem exists_polynomial_unit_coefficient_norm {d : ℕ} (q : Polynomial ℂ)
    (hq : q ≠ 0) (hdeg : q.natDegree ≤ d) :
    ∃ (c : ℂ) (r : Polynomial ℂ), c ≠ 0 ∧ r = c • q ∧
      r.natDegree ≤ d ∧ ‖coefficientVector d r‖ = 1 ∧ r.roots = q.roots := by
  let c : ℂ := (‖coefficientVector d q‖ : ℂ)⁻¹
  have hn : ‖coefficientVector d q‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (coefficientVector_ne_zero_of_natDegree_le q hq hdeg)
  have hc : c ≠ 0 := inv_ne_zero (by exact_mod_cast hn)
  refine ⟨c, c • q, hc, rfl, (Polynomial.natDegree_smul_le c q).trans hdeg, ?_,
    Polynomial.roots_smul_nonzero q hc⟩
  change ‖polynomialCoefficientLinearMap d (c • q)‖ = 1
  rw [map_smul, norm_smul]
  simp only [c, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
    polynomialCoefficientLinearMap_apply]
  exact inv_mul_cancel₀ hn

/-- A member of the span of degree-bounded polynomials obeys the same bound. -/
theorem polynomial_natDegree_le_of_mem_span {m d : ℕ}
    (p : Fin m → Polynomial ℂ) (hdeg : ∀ i, (p i).natDegree ≤ d)
    {q : Polynomial ℂ} (hq : q ∈ Submodule.span ℂ (Set.range p)) : q.natDegree ≤ d := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hq
  rw [← hc]
  exact Polynomial.natDegree_sum_le_of_forall_le _ _
    (fun i _ => (Polynomial.natDegree_smul_le (c i) (p i)).trans (hdeg i))

end KungTraub
