import appendix_b_reference.KungTraub.PolynomialFrames
import appendix_b_reference.KungTraub.PolynomialBases
import appendix_b_reference.KungTraub.PolynomialNormalization

/-!
# Uniform localisation of polynomial Wronskians

The compactness argument in Section 2.1 is assembled from actual subsequence,
root-multiplicity retention, root-persistence, and Wronskian classification theorems.
The unit-disc result is first proved for orthonormal coefficient frames. Gram--Schmidt
and scalar normalization remove those restrictions. The final result treats arbitrary
closed discs, including radius zero, and arbitrary bases of bounded-degree spaces.
Affine root transport reuses Mathlib's polynomial algebra automorphism and exact
root-multiplicity and root-multiset formulas.
-/

noncomputable section

open Filter Polynomial
open scoped BigOperators Topology

namespace KungTraub

/-- Uniform localisation in the unit disc for coefficient-orthonormal frames and a
normalized member. The constant depends only on the dimension and degree bound. -/
theorem polynomialWronskian_uniform_localization_normalized {m d : ℕ}
    (hm : 0 < m) (hmd : m ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Fin m → Polynomial ℂ) (q : Polynomial ℂ),
      (∀ i, (p i).natDegree ≤ d) → q.natDegree ≤ d →
      Orthonormal ℂ (fun i => coefficientVector d (p i)) →
      ‖coefficientVector d q‖ = 1 →
      q ∈ Submodule.span ℂ (Set.range p) →
      (∃ a : Fin m → ℂ, (∀ i, ‖a i‖ ≤ 1) ∧
        (List.ofFn a : Multiset ℂ) ≤ q.roots) →
      ∃ z : ℂ, ‖z‖ ≤ C ∧ (polynomialWronskian p).eval z = 0 := by
  sorry

/-- Removing the coefficient normalizations gives a uniform unit-disc statement for
every independent family. The member's degree bound follows from span membership. -/
theorem polynomialWronskian_uniform_localization_unitDisc {m d : ℕ}
    (hm : 0 < m) (hmd : m ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Fin m → Polynomial ℂ), LinearIndependent ℂ p →
      (∀ i, (p i).natDegree ≤ d) → ∀ q ∈ Submodule.span ℂ (Set.range p), q ≠ 0 →
      (∃ a : Fin m → ℂ, (∀ i, ‖a i‖ ≤ 1) ∧
        (List.ofFn a : Multiset ℂ) ≤ q.roots) →
      ∃ z : ℂ, ‖z‖ ≤ C ∧ (polynomialWronskian p).eval z = 0 := by
  sorry

/-- Composition with an invertible affine polynomial preserves family independence. -/
theorem polynomial_affine_family_linearIndependent {m : ℕ}
    (p : Fin m → Polynomial ℂ) (hp : LinearIndependent ℂ p)
    (a b : ℂ) (hb : b ≠ 0) :
    LinearIndependent ℂ (fun i => (p i).comp (Polynomial.C b * Polynomial.X + Polynomial.C a)) := by
  sorry

/-- An affine change of variable transports a Wronskian zero, via the intrinsic
root-multiplicity criterion. No determinant scaling formula is assumed. -/
theorem polynomialWronskian_affine_zero {m : ℕ} (hm : 0 < m)
    (p : Fin m → Polynomial ℂ) (hp : LinearIndependent ℂ p)
    (a b : ℂ) (hb : b ≠ 0) (z : ℂ)
    (hz : (polynomialWronskian
      (fun i => (p i).comp (Polynomial.C b * Polynomial.X + Polynomial.C a))).eval z = 0) :
    (polynomialWronskian p).eval (b * z + a) = 0 := by
  sorry

/-- The manuscript's uniform localization lemma for arbitrary closed discs, with
multiplicity counted in the root multiset. The radius may be zero. -/
theorem polynomialWronskian_uniform_localization {m d : ℕ}
    (hm : 0 < m) (hmd : m ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Fin m → Polynomial ℂ), LinearIndependent ℂ p →
      (∀ i, (p i).natDegree ≤ d) → ∀ (a : ℂ) (r : ℝ), 0 ≤ r →
      ∀ q ∈ Submodule.span ℂ (Set.range p), q ≠ 0 →
      (∃ z : Fin m → ℂ, (∀ i, ‖z i - a‖ ≤ r) ∧
        (List.ofFn z : Multiset ℂ) ≤ q.roots) →
      ∃ z : ℂ, ‖z - a‖ ≤ C * r ∧ (polynomialWronskian p).eval z = 0 := by
  sorry

/-- The space-and-basis formulation of uniform localization. The same constant works
for every `m`-dimensional space of polynomials of degree at most `d`, every chosen basis,
and every closed disc. -/
theorem polynomialWronskian_uniform_localization_basis {m d : ℕ}
    (hm : 0 < m) (hmd : m ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Submodule ℂ (Polynomial ℂ)),
      (∀ q ∈ V, q.natDegree ≤ d) → ∀ (b : Module.Basis (Fin m) ℂ V),
      ∀ (a : ℂ) (r : ℝ), 0 ≤ r → ∀ q ∈ V, q ≠ 0 →
      (∃ z : Fin m → ℂ, (∀ i, ‖z i - a‖ ≤ r) ∧
        (List.ofFn z : Multiset ℂ) ≤ q.roots) →
      ∃ z : ℂ, ‖z - a‖ ≤ C * r ∧
        (polynomialWronskian (fun i => (b i : Polynomial ℂ))).eval z = 0 := by
  sorry

end KungTraub
