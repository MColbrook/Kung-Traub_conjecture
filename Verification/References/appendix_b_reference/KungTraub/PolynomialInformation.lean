import appendix_b_reference.KungTraub.PolynomialBases

/-!
# Scalar information on finite-dimensional polynomial spaces

The constraints are arbitrary linear functionals. Prefix ranks and their increments are
derived from the linear maps. The rank-nullity and submodule dimension formulas
are from Mathlib.
-/

noncomputable section
namespace KungTraub
open scoped BigOperators

section ScalarInformation
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The vector of the first `j` scalar observations. -/
def scalarPrefixMap (L : ℕ → V →ₗ[K] K) (j : ℕ) : V →ₗ[K] (Fin j → K) :=
  LinearMap.pi (fun i => L i.val)

@[simp] theorem scalarPrefixMap_apply (L : ℕ → V →ₗ[K] K) (j : ℕ) (v : V)
    (i : Fin j) : scalarPrefixMap L j v i = L i.val v := by
  sorry

/-- The actual common kernel of a finite prefix. -/
def scalarPrefixKernel (L : ℕ → V →ₗ[K] K) (j : ℕ) : Submodule K V :=
  (scalarPrefixMap L j).ker

theorem mem_scalarPrefixKernel (L : ℕ → V →ₗ[K] K) (j : ℕ) (v : V) :
    v ∈ scalarPrefixKernel L j ↔ ∀ i < j, L i v = 0 := by
  sorry

theorem scalarPrefixKernel_zero (L : ℕ → V →ₗ[K] K) :
    scalarPrefixKernel L 0 = ⊤ := by
  sorry

theorem scalarPrefixKernel_succ (L : ℕ → V →ₗ[K] K) (j : ℕ) :
    scalarPrefixKernel L (j + 1) = scalarPrefixKernel L j ⊓ (L j).ker := by
  sorry

theorem scalarPrefixKernel_antitone (L : ℕ → V →ₗ[K] K) :
    Antitone (scalarPrefixKernel L) := by
  sorry

/-- Rank is the dimension of the actual observation map's range. -/
def scalarPrefixRank (L : ℕ → V →ₗ[K] K) (j : ℕ) : ℕ :=
  Module.finrank K (scalarPrefixMap L j).range

variable [FiniteDimensional K V]

theorem scalarPrefixRank_add_finrank_kernel (L : ℕ → V →ₗ[K] K) (j : ℕ) :
    scalarPrefixRank L j + Module.finrank K (scalarPrefixKernel L j) =
      Module.finrank K V := by
  sorry

theorem scalarPrefixRank_zero (L : ℕ → V →ₗ[K] K) : scalarPrefixRank L 0 = 0 := by
  sorry

theorem scalarPrefixRank_mono (L : ℕ → V →ₗ[K] K) : Monotone (scalarPrefixRank L) := by
  sorry

/-- One scalar observation increases rank by at most one, including redundant observations. -/
theorem scalarPrefixRank_succ_le (L : ℕ → V →ₗ[K] K) (j : ℕ) :
    scalarPrefixRank L (j + 1) ≤ scalarPrefixRank L j + 1 := by
  sorry

theorem scalarPrefixRank_le_length (L : ℕ → V →ₗ[K] K) (j : ℕ) :
    scalarPrefixRank L j ≤ j := by
  sorry

theorem exists_first_scalar_rank_index (L : ℕ → V →ₗ[K] K) {j k : ℕ}
    (hk : 0 < k) (hkj : k ≤ scalarPrefixRank L j) :
    ∃ i, 0 < i ∧ i ≤ j ∧ scalarPrefixRank L i = k ∧
      ∀ t < i, scalarPrefixRank L t < k := by
  sorry

/-- Every rank level has a first scalar query index, and these indices strictly increase.
Indices are zero-based; the corresponding prefix lengths are `index + 1`. -/
theorem exists_scalar_rank_indices (L : ℕ → V →ₗ[K] K) {j d : ℕ}
    (hfinal : scalarPrefixRank L j = d) :
    ∃ indices : Fin d → Fin j, StrictMono indices ∧
      (∀ k, scalarPrefixRank L ((indices k).val + 1) = k.val + 1) ∧
      (∀ k t, t ≤ (indices k).val → scalarPrefixRank L t < k.val + 1) := by
  sorry

end ScalarInformation

section PolynomialInformation
variable {K : Type*} [Field K]

/-- Restrict arbitrary polynomial observations to polynomials of degree less than `N`. -/
def polynomialScalarObservations (L : ℕ → Polynomial K →ₗ[K] K) (N : ℕ) :
    ℕ → Polynomial.degreeLT K N →ₗ[K] K :=
  fun i => (L i).comp (Polynomial.degreeLT K N).subtype

theorem polynomial_degreeLT_finrank (N : ℕ) :
    Module.finrank K (Polynomial.degreeLT K N) = N := by
  sorry

/-- `j` scalar constraints always leave a nonzero polynomial of degree at most `j`. -/
theorem exists_polynomial_in_scalar_kernel (L : ℕ → Polynomial K →ₗ[K] K) (j : ℕ) :
    ∃ q : Polynomial K, q ≠ 0 ∧ q.natDegree ≤ j ∧ ∀ i < j, L i q = 0 := by
  sorry

/-- A minimum-degree nonzero kernel element exists, with the source's exact bound `d ≤ j`. -/
theorem exists_minimum_degree_kernel_polynomial
    (L : ℕ → Polynomial K →ₗ[K] K) (j : ℕ) :
    ∃ q : Polynomial K, q ≠ 0 ∧ q.natDegree ≤ j ∧
      (∀ i < j, L i q = 0) ∧
      ∀ r : Polynomial K, r ≠ 0 → (∀ i < j, L i r = 0) → q.natDegree ≤ r.natDegree := by
  sorry

/-- Minimality makes the observation map injective on all smaller polynomial degrees. -/
theorem minimum_degree_kernel_injective (L : ℕ → Polynomial K →ₗ[K] K) (j : ℕ)
    (q : Polynomial K)
    (hmin : ∀ r : Polynomial K, r ≠ 0 → (∀ i < j, L i r = 0) → q.natDegree ≤ r.natDegree) :
    Function.Injective (scalarPrefixMap (polynomialScalarObservations L q.natDegree) j) := by
  sorry

/-- At the minimum degree `d`, final rank is exactly `d` and the common kernel has dimension one. -/
theorem minimum_degree_kernel_rank (L : ℕ → Polynomial K →ₗ[K] K) (j : ℕ)
    (q : Polynomial K) (hq : q ≠ 0) (hLq : ∀ i < j, L i q = 0)
    (hmin : ∀ r : Polynomial K, r ≠ 0 → (∀ i < j, L i r = 0) → q.natDegree ≤ r.natDegree) :
    scalarPrefixRank (polynomialScalarObservations L (q.natDegree + 1)) j = q.natDegree ∧
      Module.finrank K (scalarPrefixKernel (polynomialScalarObservations L (q.natDegree + 1)) j)
        = 1 := by
  sorry

/-- At the first rank-`k` query, the kernel on degree at most `d` has dimension `d+1-k`. -/
theorem minimum_degree_kernel_rank_indices (L : ℕ → Polynomial K →ₗ[K] K) (j : ℕ)
    (q : Polynomial K) (hq : q ≠ 0) (hLq : ∀ i < j, L i q = 0)
    (hmin : ∀ r : Polynomial K, r ≠ 0 → (∀ i < j, L i r = 0) → q.natDegree ≤ r.natDegree) :
    ∃ indices : Fin q.natDegree → Fin j, StrictMono indices ∧
      (∀ k, scalarPrefixRank (polynomialScalarObservations L (q.natDegree + 1))
        ((indices k).val + 1) = k.val + 1) ∧
      (∀ k, Module.finrank K (scalarPrefixKernel
        (polynomialScalarObservations L (q.natDegree + 1)) ((indices k).val + 1))
          = q.natDegree - k.val) := by
  sorry

end PolynomialInformation

end KungTraub
