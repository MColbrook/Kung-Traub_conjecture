import KungTraub.PolynomialBases

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
    (i : Fin j) : scalarPrefixMap L j v i = L i.val v := rfl

/-- The actual common kernel of a finite prefix. -/
def scalarPrefixKernel (L : ℕ → V →ₗ[K] K) (j : ℕ) : Submodule K V :=
  (scalarPrefixMap L j).ker

theorem mem_scalarPrefixKernel (L : ℕ → V →ₗ[K] K) (j : ℕ) (v : V) :
    v ∈ scalarPrefixKernel L j ↔ ∀ i < j, L i v = 0 := by
  change (scalarPrefixMap L j v = 0) ↔ _
  constructor
  · intro h i hi
    exact congrFun h ⟨i, hi⟩
  · intro h
    funext i
    exact h i.val i.isLt

theorem scalarPrefixKernel_zero (L : ℕ → V →ₗ[K] K) :
    scalarPrefixKernel L 0 = ⊤ := by
  ext v
  simp [mem_scalarPrefixKernel]

theorem scalarPrefixKernel_succ (L : ℕ → V →ₗ[K] K) (j : ℕ) :
    scalarPrefixKernel L (j + 1) = scalarPrefixKernel L j ⊓ (L j).ker := by
  ext v
  simp only [mem_scalarPrefixKernel, Submodule.mem_inf, LinearMap.mem_ker]
  constructor
  · intro h
    exact ⟨fun i hi => h i (by omega), h j (by omega)⟩
  · rintro ⟨h, hj⟩ i hi
    by_cases hij : i < j
    · exact h i hij
    · have : i = j := by omega
      simpa [this] using hj

theorem scalarPrefixKernel_antitone (L : ℕ → V →ₗ[K] K) :
    Antitone (scalarPrefixKernel L) := by
  intro i j hij v hv
  rw [mem_scalarPrefixKernel] at hv ⊢
  exact fun k hk => hv k (lt_of_lt_of_le hk hij)

/-- Rank is the dimension of the actual observation map's range. -/
def scalarPrefixRank (L : ℕ → V →ₗ[K] K) (j : ℕ) : ℕ :=
  Module.finrank K (scalarPrefixMap L j).range

variable [FiniteDimensional K V]

theorem scalarPrefixRank_add_finrank_kernel (L : ℕ → V →ₗ[K] K) (j : ℕ) :
    scalarPrefixRank L j + Module.finrank K (scalarPrefixKernel L j) =
      Module.finrank K V :=
  (scalarPrefixMap L j).finrank_range_add_finrank_ker

theorem scalarPrefixRank_zero (L : ℕ → V →ₗ[K] K) : scalarPrefixRank L 0 = 0 := by
  have h := scalarPrefixRank_add_finrank_kernel L 0
  rw [scalarPrefixKernel_zero, finrank_top] at h
  omega

theorem scalarPrefixRank_mono (L : ℕ → V →ₗ[K] K) : Monotone (scalarPrefixRank L) := by
  intro i j hij
  have hdim := Submodule.finrank_mono (scalarPrefixKernel_antitone L hij)
  have hi := scalarPrefixRank_add_finrank_kernel L i
  have hj := scalarPrefixRank_add_finrank_kernel L j
  omega

/-- One scalar observation increases rank by at most one, including redundant observations. -/
theorem scalarPrefixRank_succ_le (L : ℕ → V →ₗ[K] K) (j : ℕ) :
    scalarPrefixRank L (j + 1) ≤ scalarPrefixRank L j + 1 := by
  have hdim := (scalarPrefixKernel L j).finrank_sup_add_finrank_inf_eq (L j).ker
  have hsup := (scalarPrefixKernel L j ⊔ (L j).ker).finrank_le
  have hrange : Module.finrank K (L j).range ≤ 1 := by
    simpa using (L j).range.finrank_le
  have hnull := (L j).finrank_range_add_finrank_ker
  have hj := scalarPrefixRank_add_finrank_kernel L j
  have hnext := scalarPrefixRank_add_finrank_kernel L (j + 1)
  rw [scalarPrefixKernel_succ] at hnext
  omega

theorem scalarPrefixRank_le_length (L : ℕ → V →ₗ[K] K) (j : ℕ) :
    scalarPrefixRank L j ≤ j := by
  induction j with
  | zero => rw [scalarPrefixRank_zero]
  | succ j ih => have := scalarPrefixRank_succ_le L j; omega

theorem exists_first_scalar_rank_index (L : ℕ → V →ₗ[K] K) {j k : ℕ}
    (hk : 0 < k) (hkj : k ≤ scalarPrefixRank L j) :
    ∃ i, 0 < i ∧ i ≤ j ∧ scalarPrefixRank L i = k ∧
      ∀ t < i, scalarPrefixRank L t < k := by
  classical
  have hex : ∃ i, k ≤ scalarPrefixRank L i := ⟨j, hkj⟩
  let i := Nat.find hex
  have hi : k ≤ scalarPrefixRank L i := Nat.find_spec hex
  have hij : i ≤ j := Nat.find_min' hex hkj
  have hfirst : ∀ t < i, scalarPrefixRank L t < k := by
    intro t ht
    exact Nat.lt_of_not_ge (Nat.find_min hex ht)
  have hi0 : 0 < i := by
    by_contra h
    have hz : i = 0 := by omega
    rw [hz, scalarPrefixRank_zero] at hi
    omega
  have hprev := hfirst (i - 1) (by omega)
  have hstep := scalarPrefixRank_succ_le L (i - 1)
  have hsucc : i - 1 + 1 = i := by omega
  rw [hsucc] at hstep
  exact ⟨i, hi0, hij, by omega, hfirst⟩

/-- Every rank level has a first scalar query index, and these indices strictly increase.
Indices are zero-based; the corresponding prefix lengths are `index + 1`. -/
theorem exists_scalar_rank_indices (L : ℕ → V →ₗ[K] K) {j d : ℕ}
    (hfinal : scalarPrefixRank L j = d) :
    ∃ indices : Fin d → Fin j, StrictMono indices ∧
      (∀ k, scalarPrefixRank L ((indices k).val + 1) = k.val + 1) ∧
      (∀ k t, t ≤ (indices k).val → scalarPrefixRank L t < k.val + 1) := by
  classical
  have hex (k : Fin d) := exists_first_scalar_rank_index L
    (show 0 < k.val + 1 by omega) (show k.val + 1 ≤ scalarPrefixRank L j by omega)
  choose i hi0 hij hri hfirst using hex
  let indices : Fin d → Fin j := fun k => ⟨i k - 1, by have := hi0 k; have := hij k; omega⟩
  have hidx : ∀ k, (indices k).val + 1 = i k := by
    intro k
    change i k - 1 + 1 = i k
    exact Nat.sub_add_cancel (hi0 k)
  refine ⟨indices, ?_, ?_, ?_⟩
  · intro k l hkl
    have hir : i k < i l := by
      by_contra hh
      have hle : i l ≤ i k := by omega
      have hmono := scalarPrefixRank_mono L hle
      rw [hri l, hri k] at hmono
      have : k.val < l.val := hkl
      omega
    change i k - 1 < i l - 1
    have := hi0 k
    omega
  · intro k
    rw [hidx, hri]
  · intro k t ht
    apply hfirst k t
    have := hidx k
    omega

end ScalarInformation

section PolynomialInformation
variable {K : Type*} [Field K]

/-- Restrict arbitrary polynomial observations to polynomials of degree less than `N`. -/
def polynomialScalarObservations (L : ℕ → Polynomial K →ₗ[K] K) (N : ℕ) :
    ℕ → Polynomial.degreeLT K N →ₗ[K] K :=
  fun i => (L i).comp (Polynomial.degreeLT K N).subtype

theorem polynomial_degreeLT_finrank (N : ℕ) :
    Module.finrank K (Polynomial.degreeLT K N) = N := by
  rw [Module.finrank_eq_card_basis (Polynomial.degreeLT.basis K N), Fintype.card_fin]

/-- `j` scalar constraints always leave a nonzero polynomial of degree at most `j`. -/
theorem exists_polynomial_in_scalar_kernel (L : ℕ → Polynomial K →ₗ[K] K) (j : ℕ) :
    ∃ q : Polynomial K, q ≠ 0 ∧ q.natDegree ≤ j ∧ ∀ i < j, L i q = 0 := by
  let f := scalarPrefixMap (polynomialScalarObservations L (j + 1)) j
  have hker : f.ker ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by
    rw [polynomial_degreeLT_finrank]
    simp)
  obtain ⟨q, hq, hqne⟩ := f.ker.ne_bot_iff.mp hker
  have hqval : (q : Polynomial K) ≠ 0 := by
    intro hzero
    apply hqne
    exact Subtype.ext hzero
  refine ⟨q, hqval, ?_, ?_⟩
  · have hdegree := Polynomial.mem_degreeLT.mp q.property
    rw [Polynomial.degree_eq_natDegree hqval] at hdegree
    have hlt : (q : Polynomial K).natDegree < j + 1 := by exact_mod_cast hdegree
    omega
  · have hmem : q ∈ scalarPrefixKernel (polynomialScalarObservations L (j + 1)) j := hq
    exact (mem_scalarPrefixKernel _ _ _).mp hmem

/-- A minimum-degree nonzero kernel element exists, with the source's exact bound `d ≤ j`. -/
theorem exists_minimum_degree_kernel_polynomial
    (L : ℕ → Polynomial K →ₗ[K] K) (j : ℕ) :
    ∃ q : Polynomial K, q ≠ 0 ∧ q.natDegree ≤ j ∧
      (∀ i < j, L i q = 0) ∧
      ∀ r : Polynomial K, r ≠ 0 → (∀ i < j, L i r = 0) → q.natDegree ≤ r.natDegree := by
  classical
  obtain ⟨p, hp, hbound, hLp⟩ := exists_polynomial_in_scalar_kernel L j
  have hex : ∃ d, ∃ q : Polynomial K, q ≠ 0 ∧ q.natDegree = d ∧ ∀ i < j, L i q = 0 :=
    ⟨p.natDegree, p, hp, rfl, hLp⟩
  obtain ⟨q, hq, hdegree, hLq⟩ := Nat.find_spec hex
  have hmin (r : Polynomial K) (hr : r ≠ 0) (hLr : ∀ i < j, L i r = 0) :
      q.natDegree ≤ r.natDegree := by
    rw [hdegree]
    exact Nat.find_min' hex ⟨r, hr, rfl, hLr⟩
  exact ⟨q, hq, (hmin p hp hLp).trans hbound, hLq, hmin⟩

/-- Minimality makes the observation map injective on all smaller polynomial degrees. -/
theorem minimum_degree_kernel_injective (L : ℕ → Polynomial K →ₗ[K] K) (j : ℕ)
    (q : Polynomial K)
    (hmin : ∀ r : Polynomial K, r ≠ 0 → (∀ i < j, L i r = 0) → q.natDegree ≤ r.natDegree) :
    Function.Injective (scalarPrefixMap (polynomialScalarObservations L q.natDegree) j) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro r hr
  apply Subtype.ext
  change (r : Polynomial K) = 0
  by_contra hrne
  have hLr : ∀ i < j, L i (r : Polynomial K) = 0 := by
    intro i hi
    exact congrFun hr ⟨i, hi⟩
  have hbound := hmin r hrne hLr
  have hdegree := Polynomial.mem_degreeLT.mp r.property
  rw [Polynomial.degree_eq_natDegree hrne] at hdegree
  have hlt : (r : Polynomial K).natDegree < q.natDegree := by exact_mod_cast hdegree
  omega

/-- At the minimum degree `d`, final rank is exactly `d` and the common kernel has dimension one. -/
theorem minimum_degree_kernel_rank (L : ℕ → Polynomial K →ₗ[K] K) (j : ℕ)
    (q : Polynomial K) (hq : q ≠ 0) (hLq : ∀ i < j, L i q = 0)
    (hmin : ∀ r : Polynomial K, r ≠ 0 → (∀ i < j, L i r = 0) → q.natDegree ≤ r.natDegree) :
    scalarPrefixRank (polynomialScalarObservations L (q.natDegree + 1)) j = q.natDegree ∧
      Module.finrank K (scalarPrefixKernel (polynomialScalarObservations L (q.natDegree + 1)) j)
        = 1 := by
  let d := q.natDegree
  let f := scalarPrefixMap (polynomialScalarObservations L d) j
  let g := scalarPrefixMap (polynomialScalarObservations L (d + 1)) j
  have hf : Module.finrank K f.range = d := by
    rw [LinearMap.finrank_range_of_inj (minimum_degree_kernel_injective L j q hmin),
      polynomial_degreeLT_finrank]
  have hrange : f.range ≤ g.range := by
    rintro y ⟨r, rfl⟩
    refine ⟨⟨r, Polynomial.degreeLT_mono (Nat.le_succ d) r.property⟩, rfl⟩
  have hlow : d ≤ Module.finrank K g.range := by
    calc
      d = Module.finrank K f.range := hf.symm
      _ ≤ Module.finrank K g.range := Submodule.finrank_mono hrange
  have hqmem : q ∈ Polynomial.degreeLT K (d + 1) := by
    apply Polynomial.mem_degreeLT.mpr
    rw [Polynomial.degree_eq_natDegree hq]
    exact_mod_cast Nat.lt_succ_self d
  let q' : Polynomial.degreeLT K (d + 1) := ⟨q, hqmem⟩
  have hq'ne : q' ≠ 0 := by
    intro hz
    apply hq
    exact congrArg Subtype.val hz
  have hq'ker : q' ∈ g.ker := by
    change scalarPrefixMap (polynomialScalarObservations L (d + 1)) j q' = 0
    funext i
    exact hLq i.val i.isLt
  have hker : g.ker ≠ ⊥ := g.ker.ne_bot_iff.mpr ⟨q', hq'ker, hq'ne⟩
  have hpositive : 1 ≤ Module.finrank K g.ker := Submodule.one_le_finrank_iff.mpr hker
  have hdim := g.finrank_range_add_finrank_ker
  rw [polynomial_degreeLT_finrank] at hdim
  change Module.finrank K g.range = d ∧ Module.finrank K g.ker = 1
  omega

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
  have hfinal := (minimum_degree_kernel_rank L j q hq hLq hmin).1
  obtain ⟨indices, hmono, hrank, _⟩ := exists_scalar_rank_indices _ hfinal
  refine ⟨indices, hmono, hrank, ?_⟩
  intro k
  have hdim := scalarPrefixRank_add_finrank_kernel
    (polynomialScalarObservations L (q.natDegree + 1)) ((indices k).val + 1)
  rw [hrank, polynomial_degreeLT_finrank] at hdim
  have := k.isLt
  omega

end PolynomialInformation

end KungTraub
