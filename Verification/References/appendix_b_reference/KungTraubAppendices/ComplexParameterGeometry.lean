import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic

/-!
# Complex parameter projections for bilinear evaluations

The family evaluates parameters by the bilinear sum `∑ uᵢ*vᵢ`. Mathlib's complex
inner product is conjugate-linear in its first argument, so this sum is
`⟪conjVector v, u⟫`. Projection must therefore be applied to `conjVector v`.
The projection and root-displacement arguments adapt the real supporting lemmas
in `KungTraub.ParameterGeometry`; Mathlib supplies orthogonal projection and
Cauchy–Schwarz. All vector spaces here remain complex Euclidean spaces.
-/

noncomputable section

open scoped BigOperators InnerProductSpace

namespace KungTraubAppendices

/-- The complex bilinear evaluation used by the finite affine family. -/
def complexBilinearDot {m : ℕ} (u v : EuclideanSpace ℂ (Fin m)) : ℂ :=
  ∑ i, u i * v i

/-- Coordinatewise conjugation on the Euclidean space. -/
def complexConjVector {m : ℕ} (v : EuclideanSpace ℂ (Fin m)) :
    EuclideanSpace ℂ (Fin m) := WithLp.toLp 2 (fun i => star (v i))

@[simp] theorem complexConjVector_apply {m : ℕ} (v : EuclideanSpace ℂ (Fin m))
    (i : Fin m) : complexConjVector v i = star (v i) := by
  sorry

/-- Conjugating twice recovers the original complex parameter vector. -/
@[simp] theorem complexConjVector_involutive {m : ℕ} (v : EuclideanSpace ℂ (Fin m)) :
    complexConjVector (complexConjVector v) = v := by
  sorry

/-- Componentwise conjugation preserves subtraction. -/
theorem complexConjVector_sub {m : ℕ} (u v : EuclideanSpace ℂ (Fin m)) :
    complexConjVector (u - v) = complexConjVector u - complexConjVector v := by
  sorry

/-- Componentwise conjugation preserves the full complex Euclidean norm. -/
@[simp] theorem norm_complexConjVector {m : ℕ} (v : EuclideanSpace ℂ (Fin m)) :
    ‖complexConjVector v‖ = ‖v‖ := by
  sorry

/-- Conjugation preserves the norm of vector differences. -/
theorem norm_complexConjVector_sub {m : ℕ} (u v : EuclideanSpace ℂ (Fin m)) :
    ‖complexConjVector u - complexConjVector v‖ = ‖u - v‖ := by
  sorry

/-- The bilinear sum has the conjugated evaluation vector in the first
argument of Mathlib's Hermitian inner product. -/
theorem complexBilinearDot_eq_inner {m : ℕ} (u v : EuclideanSpace ℂ (Fin m)) :
    complexBilinearDot u v = ⟪complexConjVector v, u⟫_ℂ := by
  sorry

/-- Cauchy–Schwarz for the actual bilinear evaluation. -/
theorem norm_complexBilinearDot_le {m : ℕ} (u v : EuclideanSpace ℂ (Fin m)) :
    ‖complexBilinearDot u v‖ ≤ ‖v‖ * ‖u‖ := by
  sorry

/-- Restriction to the remaining complex directions projects the conjugated
evaluation vector, with no conjugation of the parameter direction. -/
theorem complexBilinearDot_eq_projected_inner {m : ℕ}
    (V : Submodule ℂ (EuclideanSpace ℂ (Fin m))) [V.HasOrthogonalProjection]
    {h : EuclideanSpace ℂ (Fin m)} (hh : h ∈ V) (v : EuclideanSpace ℂ (Fin m)) :
    complexBilinearDot h v = ⟪V.starProjection (complexConjVector v), h⟫_ℂ := by
  sorry

/-- The projected norm controls every actual bilinear evaluation in the
remaining complex subspace. -/
theorem norm_complexBilinearDot_le_projected {m : ℕ}
    (V : Submodule ℂ (EuclideanSpace ℂ (Fin m))) [V.HasOrthogonalProjection]
    {h : EuclideanSpace ℂ (Fin m)} (hh : h ∈ V) (v : EuclideanSpace ℂ (Fin m)) :
    ‖complexBilinearDot h v‖ ≤ ‖V.starProjection (complexConjVector v)‖ * ‖h‖ := by
  sorry

/-- A positive projected norm is attained as a positive real complex value
by a unit direction in the actual complex subspace. -/
theorem exists_complex_unit_direction_attaining_projected_norm {m : ℕ}
    (V : Submodule ℂ (EuclideanSpace ℂ (Fin m))) [V.HasOrthogonalProjection]
    (v : EuclideanSpace ℂ (Fin m)) (ha : 0 < ‖V.starProjection (complexConjVector v)‖) :
    ∃ e ∈ V, ‖e‖ = 1 ∧
      complexBilinearDot e v = (‖V.starProjection (complexConjVector v)‖ : ℂ) := by
  sorry

/-- Passing to a smaller complex direction space cannot increase the
projected norm of the conjugated evaluation vector. -/
theorem complex_projected_norm_mono_subspace {m : ℕ}
    {U V : Submodule ℂ (EuclideanSpace ℂ (Fin m))}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (hUV : U ≤ V)
    (v : EuclideanSpace ℂ (Fin m)) :
    ‖U.starProjection (complexConjVector v)‖ ≤ ‖V.starProjection (complexConjVector v)‖ := by
  sorry

/-- A spatial lower bound and the exact affine perturbation value yield the
root displacement estimate. -/
theorem complex_root_displacement_le_projected {d : ℕ}
    (V : Submodule ℂ (EuclideanSpace ℂ (Fin d))) [V.HasOrthogonalProjection]
    {g : ℂ → ℂ} {m : ℝ} {α β : ℂ} {h v : EuclideanSpace ℂ (Fin d)}
    (hh : h ∈ V) (hm : 0 < m)
    (hlower : m * ‖β - α‖ ≤ ‖g α‖) (hvalue : g α = complexBilinearDot h v) :
    ‖β - α‖ ≤ (‖V.starProjection (complexConjVector v)‖ / m) * ‖h‖ := by
  sorry

end KungTraubAppendices
