import support_reference.KungTraub.Coefficients
import support_reference.KungTraub.PolynomialCoefficientLimits
import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
# Compactness of orthonormal polynomial coefficient frames

The localisation argument takes a subsequence of orthonormal frames in a fixed finite
Euclidean coefficient space. Compactness below comes from finite products of closed unit
balls. Orthonormality follows at the limit by continuity of inner products.
A simultaneously selected unit member stays in the limiting
span by its finite orthonormal expansion, and remains nonzero.

The proofs reuse Mathlib's finite-dimensional compactness and inner-product continuity,
and its orthonormal expansion and independence facts from the module by Zhouhang Zhou,
Sébastien Gouëzel and Frédéric Dupuis.
-/

noncomputable section

open Filter Polynomial
open scoped BigOperators Topology ComplexInnerProductSpace

namespace KungTraub

/-- Pointwise norm limits of orthonormal frames are orthonormal. -/
theorem orthonormal_of_pointwise_tendsto {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {ι : Type*} {V : ℕ → ι → E} {v : ι → E}
    (hV : ∀ n, Orthonormal ℂ (V n))
    (hlim : ∀ i, Tendsto (fun n => V n i) atTop (𝓝 (v i))) : Orthonormal ℂ v := by
  sorry

/-- A member of a finite orthonormal span has its usual finite inner-product expansion. -/
theorem finite_orthonormal_sum_inner_of_mem_span {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {ι : Type*} [Fintype ι] {v : ι → E}
    (hv : Orthonormal ℂ v) {w : E} (hw : w ∈ Submodule.span ℂ (Set.range v)) :
    ∑ i, ⟪v i, w⟫ • v i = w := by
  sorry

/-- Simultaneous limits of orthonormal frames and members retain span membership.
The varying spans are handled by their explicit finite orthonormal expansions. -/
theorem mem_span_of_orthonormal_limits {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {ι : Type*} [Fintype ι]
    {V : ℕ → ι → E} {v : ι → E} {W : ℕ → E} {w : E}
    (hV : ∀ n, Orthonormal ℂ (V n))
    (hVlim : ∀ i, Tendsto (fun n => V n i) atTop (𝓝 (v i)))
    (hWlim : Tendsto W atTop (𝓝 w))
    (hmem : ∀ n, W n ∈ Submodule.span ℂ (Set.range (V n))) :
    w ∈ Submodule.span ℂ (Set.range v) := by
  sorry

/-- Orthonormal frames in a fixed finite Euclidean coefficient space have an orthonormal
subsequence limit. Independence and the exact dimension of the limiting span are explicit. -/
theorem exists_orthonormal_coefficient_frame_subseq {m d : ℕ}
    (V : ℕ → Fin m → EuclideanSpace ℂ (Fin (d + 1)))
    (hV : ∀ n, Orthonormal ℂ (V n)) :
    ∃ v : Fin m → EuclideanSpace ℂ (Fin (d + 1)),
      Orthonormal ℂ v ∧ LinearIndependent ℂ v ∧
      Module.finrank ℂ (Submodule.span ℂ (Set.range v)) = m ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ i, Tendsto (fun n => V (φ n) i) atTop (𝓝 (v i)) := by
  sorry

/-- A normalized member can converge along the same subsequence as the frame. Its unit
norm, nonvanishing, and membership in the limiting `m`-dimensional span are retained. -/
theorem exists_orthonormal_coefficient_frame_member_subseq {m d : ℕ}
    (V : ℕ → Fin m → EuclideanSpace ℂ (Fin (d + 1)))
    (W : ℕ → EuclideanSpace ℂ (Fin (d + 1)))
    (hV : ∀ n, Orthonormal ℂ (V n)) (hW : ∀ n, ‖W n‖ = 1)
    (hmem : ∀ n, W n ∈ Submodule.span ℂ (Set.range (V n))) :
    ∃ v : Fin m → EuclideanSpace ℂ (Fin (d + 1)),
      ∃ w : EuclideanSpace ℂ (Fin (d + 1)),
      Orthonormal ℂ v ∧ LinearIndependent ℂ v ∧
      Module.finrank ℂ (Submodule.span ℂ (Set.range v)) = m ∧
      ‖w‖ = 1 ∧ w ≠ 0 ∧ w ∈ Submodule.span ℂ (Set.range v) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        (∀ i, Tendsto (fun n => V (φ n) i) atTop (𝓝 (v i))) ∧
        Tendsto (W ∘ φ) atTop (𝓝 w) := by
  sorry

/-- Reconstruct a degree-bounded polynomial from its Euclidean coefficient vector. -/
def polynomialOfCoefficients {d : ℕ} (v : EuclideanSpace ℂ (Fin (d + 1))) : Polynomial ℂ :=
  ∑ i, Polynomial.monomial i.val (v i)

/-- The reconstruction has the specified coefficients and zero coefficients above `d`. -/
theorem polynomialOfCoefficients_coeff {d : ℕ}
    (v : EuclideanSpace ℂ (Fin (d + 1))) (k : ℕ) :
    (polynomialOfCoefficients v).coeff k =
      if h : k < d + 1 then v ⟨k, h⟩ else 0 := by
  sorry

theorem polynomialOfCoefficients_natDegree_le {d : ℕ}
    (v : EuclideanSpace ℂ (Fin (d + 1))) : (polynomialOfCoefficients v).natDegree ≤ d := by
  sorry

@[simp] theorem coefficientVector_polynomialOfCoefficients {d : ℕ}
    (v : EuclideanSpace ℂ (Fin (d + 1))) :
    coefficientVector d (polynomialOfCoefficients v) = v := by
  sorry

@[simp] theorem polynomialOfCoefficients_coefficientVector {d : ℕ} (p : Polynomial ℂ)
    (hp : p.natDegree ≤ d) : polynomialOfCoefficients (coefficientVector d p) = p := by
  sorry

/-- Coefficient extraction is linear even for polynomials of degree larger than the
chosen coefficient space; reconstruction is its inverse on the bounded-degree subspace. -/
def polynomialCoefficientLinearMap (d : ℕ) :
    Polynomial ℂ →ₗ[ℂ] EuclideanSpace ℂ (Fin (d + 1)) where
  toFun := coefficientVector d
  map_add' p q := by ext i; simp [coefficientVector]
  map_smul' c p := by ext i; simp [coefficientVector]

/-- Reconstruction is a linear map from coefficient vectors to polynomials. -/
def polynomialOfCoefficientsLinearMap (d : ℕ) :
    EuclideanSpace ℂ (Fin (d + 1)) →ₗ[ℂ] Polynomial ℂ where
  toFun := polynomialOfCoefficients
  map_add' v w := by
    ext k
    by_cases hk : k < d + 1 <;> simp [polynomialOfCoefficients_coeff, hk]
  map_smul' c v := by
    ext k
    by_cases hk : k < d + 1 <;> simp [polynomialOfCoefficients_coeff, hk]

@[simp] theorem polynomialCoefficientLinearMap_apply (d : ℕ) (p : Polynomial ℂ) :
    polynomialCoefficientLinearMap d p = coefficientVector d p := by
  sorry

@[simp] theorem polynomialOfCoefficientsLinearMap_apply (d : ℕ)
    (v : EuclideanSpace ℂ (Fin (d + 1))) :
    polynomialOfCoefficientsLinearMap d v = polynomialOfCoefficients v := by
  sorry

/-- Convergence in the finite Euclidean coefficient space gives convergence of every
coefficient of degree-bounded polynomials, including the identically zero tail. -/
theorem polynomial_coeff_tendsto_of_coefficientVector_tendsto {d : ℕ}
    {P : ℕ → Polynomial ℂ} {v : EuclideanSpace ℂ (Fin (d + 1))}
    (hdeg : ∀ n, (P n).natDegree ≤ d)
    (hlim : Tendsto (fun n => coefficientVector d (P n)) atTop (𝓝 v)) (k : ℕ) :
    Tendsto (fun n => (P n).coeff k) atTop (𝓝 ((polynomialOfCoefficients v).coeff k)) := by
  sorry

/-- The polynomial form of frame compactness used in Wronskian localisation. One
subsequence preserves all frame coefficients and a normalized member, with exact limiting
span dimension and a nonzero limiting member. -/
theorem exists_polynomial_frame_member_subseq {m d : ℕ}
    (P : ℕ → Fin m → Polynomial ℂ) (Q : ℕ → Polynomial ℂ)
    (hPdeg : ∀ n i, (P n i).natDegree ≤ d) (hQdeg : ∀ n, (Q n).natDegree ≤ d)
    (hP : ∀ n, Orthonormal ℂ (fun i => coefficientVector d (P n i)))
    (hQ : ∀ n, ‖coefficientVector d (Q n)‖ = 1)
    (hmem : ∀ n, Q n ∈ Submodule.span ℂ (Set.range (P n))) :
    ∃ p : Fin m → Polynomial ℂ, ∃ q : Polynomial ℂ,
      (∀ i, (p i).natDegree ≤ d) ∧ q.natDegree ≤ d ∧
      Orthonormal ℂ (fun i => coefficientVector d (p i)) ∧
      LinearIndependent ℂ p ∧ Module.finrank ℂ (Submodule.span ℂ (Set.range p)) = m ∧
      ‖coefficientVector d q‖ = 1 ∧ q ≠ 0 ∧ q ∈ Submodule.span ℂ (Set.range p) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        (∀ i k, Tendsto (fun n => (P (φ n) i).coeff k) atTop (𝓝 ((p i).coeff k))) ∧
        (∀ k, Tendsto (fun n => (Q (φ n)).coeff k) atTop (𝓝 (q.coeff k))) := by
  sorry

end KungTraub
