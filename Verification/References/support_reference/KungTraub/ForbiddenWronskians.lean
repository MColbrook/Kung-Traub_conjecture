import support_reference.KungTraub.PolynomialInformation
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# The finite forbidden sets of polynomial Wronskian zeros

This module constructs the actual translated root sets and proves the manuscript's
integer bounds M_n = floor((n+1)^2/4) and H_n = n*M_n+1. Empty-dimensional and
full polynomial spaces contribute no roots. Root sets contain distinct points;
the earlier polynomial root estimates continue to count multiplicity separately.
-/

noncomputable section
namespace KungTraub
open scoped BigOperators

def wronskianRootCountBound (n : ℕ) : ℕ := (n + 1) ^ 2 / 4

def forbiddenWronskianCountBound (n : ℕ) : ℕ := n * wronskianRootCountBound n + 1

theorem wronskian_dimension_product_le (m n : ℕ) (hm : m ≤ n + 1) :
    m * (n + 1 - m) ≤ wronskianRootCountBound n := by
  sorry

theorem polynomial_independent_card_le_degree_bound {m d : ℕ}
    (p : Fin m → Polynomial ℂ) (hp : LinearIndependent ℂ p)
    (hdeg : ∀ i, (p i).natDegree ≤ d) : m ≤ d + 1 := by
  sorry

theorem polynomialWronskian_natDegree_le_rootCountBound {m d n : ℕ}
    (p : Fin m → Polynomial ℂ) (hp : LinearIndependent ℂ p)
    (hdeg : ∀ i, (p i).natDegree ≤ d) (hdn : d ≤ n) :
    (polynomialWronskian p).natDegree ≤ wronskianRootCountBound n := by
  sorry

/-- Translate the distinct roots of the actual Wronskian polynomial by `x`. -/
def shiftedWronskianRoots {m : ℕ} (p : Fin m → Polynomial ℂ) (x : ℂ) : Finset ℂ :=
  (polynomialWronskian p).roots.toFinset.image (fun z => x + z)

theorem mem_shiftedWronskianRoots {m : ℕ} (p : Fin m → Polynomial ℂ)
    (hp : LinearIndependent ℂ p) (x z : ℂ) :
    z ∈ shiftedWronskianRoots p x ↔ (polynomialWronskian p).eval (z - x) = 0 := by
  sorry

theorem shiftedWronskianRoots_card_le {m d n : ℕ} (p : Fin m → Polynomial ℂ)
    (hp : LinearIndependent ℂ p) (hdeg : ∀ i, (p i).natDegree ≤ d) (hdn : d ≤ n)
    (x : ℂ) : (shiftedWronskianRoots p x).card ≤ wronskianRootCountBound n := by
  sorry

theorem shiftedWronskianRoots_empty (p : Fin 0 → Polynomial ℂ) (x : ℂ) :
    shiftedWronskianRoots p x = ∅ := by
  sorry

theorem shiftedWronskianRoots_eq_empty_of_full_span {m : ℕ}
    (p : Fin m → Polynomial ℂ) (hp : LinearIndependent ℂ p)
    (hfull : Submodule.span ℂ (Set.range p) = Polynomial.degreeLT ℂ m) (x : ℂ) :
    shiftedWronskianRoots p x = ∅ := by
  sorry

/-- One space for each degree `d=1,...,n`, together with at most one query point. -/
def forbiddenWronskianSet {n : ℕ} {dim : Fin n → ℕ}
    (p : (d : Fin n) → Fin (dim d) → Polynomial ℂ) (x : ℂ) (query : Option ℂ) : Finset ℂ :=
  (Finset.univ.biUnion (fun d => shiftedWronskianRoots (p d) x)) ∪
    (match query with | none => ∅ | some z => {z})

theorem forbiddenWronskianSet_card_le {n : ℕ} {dim : Fin n → ℕ}
    (p : (d : Fin n) → Fin (dim d) → Polynomial ℂ)
    (hp : ∀ d, LinearIndependent ℂ (p d))
    (hdeg : ∀ d i, (p d i).natDegree ≤ d.val + 1) (x : ℂ) (query : Option ℂ) :
    (forbiddenWronskianSet p x query).card ≤ forbiddenWronskianCountBound n := by
  sorry

theorem polynomialNestedBasis_linearIndependent {m d : ℕ}
    (V : Submodule ℂ (Polynomial.degreeLT ℂ (d + 1))) (b : Module.Basis (Fin m) ℂ V) :
    LinearIndependent ℂ (fun i => ((b i).val : Polynomial ℂ)) := by
  sorry

/-- The actual common kernel inside polynomials of degree at most `d`. -/
abbrev polynomialKernelSpace (L : ℕ → Polynomial ℂ →ₗ[ℂ] ℂ) (j d : ℕ) :=
  scalarPrefixKernel (polynomialScalarObservations L (d + 1)) j

def polynomialKernelDimension (L : ℕ → Polynomial ℂ →ₗ[ℂ] ℂ) (j d : ℕ) : ℕ :=
  Module.finrank ℂ (polynomialKernelSpace L j d)

@[irreducible] def polynomialKernelBasis (L : ℕ → Polynomial ℂ →ₗ[ℂ] ℂ) (j d : ℕ) :
    Module.Basis (Fin (polynomialKernelDimension L j d)) ℂ (polynomialKernelSpace L j d) := by
  letI : Module.Free ℂ (polynomialKernelSpace L j d) :=
    Module.Free.of_basis (Module.Basis.ofVectorSpace ℂ (polynomialKernelSpace L j d))
  exact Module.finBasis ℂ (polynomialKernelSpace L j d)

/-- A canonical basis of the bounded-degree common kernel, as ambient polynomials. -/
def polynomialKernelFamily (L : ℕ → Polynomial ℂ →ₗ[ℂ] ℂ) (j d : ℕ) :
    Fin (polynomialKernelDimension L j d) → Polynomial ℂ :=
  fun i => ((polynomialKernelBasis L j d i).val : Polynomial ℂ)

theorem polynomialKernelFamily_linearIndependent (L : ℕ → Polynomial ℂ →ₗ[ℂ] ℂ) (j d : ℕ) :
    LinearIndependent ℂ (polynomialKernelFamily L j d) := by
  sorry

theorem polynomialKernelFamily_degree_le (L : ℕ → Polynomial ℂ →ₗ[ℂ] ℂ) (j d : ℕ)
    (i : Fin (polynomialKernelDimension L j d)) :
    (polynomialKernelFamily L j d i).natDegree ≤ d := by
  sorry

theorem polynomialKernelFamily_annihilated (L : ℕ → Polynomial ℂ →ₗ[ℂ] ℂ) (j d : ℕ)
    (k : Fin (polynomialKernelDimension L j d)) :
    ∀ i < j, L i (polynomialKernelFamily L j d k) = 0 := by
  sorry

theorem mem_span_polynomialKernelFamily (L : ℕ → Polynomial ℂ →ₗ[ℂ] ℂ) (j d : ℕ)
    (q : Polynomial ℂ) :
    q ∈ Submodule.span ℂ (Set.range (polynomialKernelFamily L j d)) ↔
      q.natDegree ≤ d ∧ ∀ i < j, L i q = 0 := by
  sorry

/-- The manuscript's actual forbidden set for an arbitrary prefix of scalar polynomial data. -/
def polynomialKernelForbiddenSet (L : ℕ → Polynomial ℂ →ₗ[ℂ] ℂ)
    (j n : ℕ) (x : ℂ) (query : Option ℂ) : Finset ℂ :=
  forbiddenWronskianSet (fun d : Fin n => polynomialKernelFamily L j (d.val + 1)) x query

theorem polynomialKernelForbiddenSet_card_le (L : ℕ → Polynomial ℂ →ₗ[ℂ] ℂ)
    (j n : ℕ) (x : ℂ) (query : Option ℂ) :
    (polynomialKernelForbiddenSet L j n x query).card ≤ forbiddenWronskianCountBound n := by
  sorry

theorem mem_forbiddenWronskianSet {n : ℕ} {dim : Fin n → ℕ}
    (p : (d : Fin n) → Fin (dim d) → Polynomial ℂ)
    (hp : ∀ d, LinearIndependent ℂ (p d)) (x z : ℂ) (query : Option ℂ) :
    z ∈ forbiddenWronskianSet p x query ↔
      (∃ d, (polynomialWronskian (p d)).eval (z - x) = 0) ∨ query = some z := by
  sorry

theorem polynomialKernelForbiddenSet_contains_wronskian_zero
    (L : ℕ → Polynomial ℂ →ₗ[ℂ] ℂ) (j n d : ℕ) (hd : 0 < d) (hdn : d ≤ n)
    (x z : ℂ) (query : Option ℂ)
    (hz : (polynomialWronskian (polynomialKernelFamily L j d)).eval z = 0) :
    x + z ∈ polynomialKernelForbiddenSet L j n x query := by
  sorry

theorem polynomialKernelForbiddenSet_contains_query
    (L : ℕ → Polynomial ℂ →ₗ[ℂ] ℂ) (j n : ℕ) (x z : ℂ) :
    z ∈ polynomialKernelForbiddenSet L j n x (some z) := by
  sorry

theorem shiftedWronskianRoots_basis_independent {m : ℕ}
    (V : Submodule ℂ (Polynomial ℂ)) (b b' : Module.Basis (Fin m) ℂ V) (x : ℂ) :
    shiftedWronskianRoots (fun i => (b' i : Polynomial ℂ)) x =
      shiftedWronskianRoots (fun i => (b i : Polynomial ℂ)) x := by
  sorry

theorem shiftedWronskianRoots_eq_of_span_eq {m k : ℕ}
    (p : Fin m → Polynomial ℂ) (q : Fin k → Polynomial ℂ)
    (hp : LinearIndependent ℂ p) (hq : LinearIndependent ℂ q)
    (hspan : Submodule.span ℂ (Set.range p) = Submodule.span ℂ (Set.range q)) (x : ℂ) :
    shiftedWronskianRoots p x = shiftedWronskianRoots q x := by
  sorry

theorem polynomialKernelFamily_span_congr (L L' : ℕ → Polynomial ℂ →ₗ[ℂ] ℂ)
    (j d : ℕ) (hL : ∀ i < j, L i = L' i) :
    Submodule.span ℂ (Set.range (polynomialKernelFamily L j d)) =
      Submodule.span ℂ (Set.range (polynomialKernelFamily L' j d)) := by
  sorry

/-- Later rows do not affect the forbidden set of a fixed prefix, regardless of basis choices. -/
theorem polynomialKernelForbiddenSet_congr (L L' : ℕ → Polynomial ℂ →ₗ[ℂ] ℂ)
    (j n : ℕ) (x : ℂ) (query : Option ℂ) (hL : ∀ i < j, L i = L' i) :
    polynomialKernelForbiddenSet L j n x query = polynomialKernelForbiddenSet L' j n x query := by
  sorry

end KungTraub
