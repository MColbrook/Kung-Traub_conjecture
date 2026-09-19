import KungTraub.PolynomialInformation
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
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 4)).mpr
  have h := four_mul_le_sq_add m (n + 1 - m)
  rw [Nat.add_sub_of_le hm] at h
  simpa only [mul_comm, mul_left_comm, mul_assoc] using h

theorem polynomial_independent_card_le_degree_bound {m d : ℕ}
    (p : Fin m → Polynomial ℂ) (hp : LinearIndependent ℂ p)
    (hdeg : ∀ i, (p i).natDegree ≤ d) : m ≤ d + 1 := by
  have hle : Submodule.span ℂ (Set.range p) ≤ Polynomial.degreeLT ℂ (d + 1) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    apply Polynomial.mem_degreeLT.mpr
    rw [Polynomial.degree_eq_natDegree (hp.ne_zero i)]
    exact_mod_cast Nat.lt_succ_of_le (hdeg i)
  have hdim := Submodule.finrank_mono hle
  rw [Module.finrank_eq_card_basis (Module.Basis.span hp),
    polynomial_degreeLT_finrank, Fintype.card_fin] at hdim
  exact hdim

theorem polynomialWronskian_natDegree_le_rootCountBound {m d n : ℕ}
    (p : Fin m → Polynomial ℂ) (hp : LinearIndependent ℂ p)
    (hdeg : ∀ i, (p i).natDegree ≤ d) (hdn : d ≤ n) :
    (polynomialWronskian p).natDegree ≤ wronskianRootCountBound n := by
  by_cases hm : m = 0
  · subst m
    simp
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hdegn : ∀ i, (p i).natDegree ≤ n := fun i => (hdeg i).trans hdn
    have hmn := polynomial_independent_card_le_degree_bound p hp hdegn
    exact (polynomialWronskian_natDegree_le hmpos hmn p hp hdegn).trans
      (wronskian_dimension_product_le m n hmn)

/-- Translate the distinct roots of the actual Wronskian polynomial by `x`. -/
def shiftedWronskianRoots {m : ℕ} (p : Fin m → Polynomial ℂ) (x : ℂ) : Finset ℂ :=
  (polynomialWronskian p).roots.toFinset.image (fun z => x + z)

theorem mem_shiftedWronskianRoots {m : ℕ} (p : Fin m → Polynomial ℂ)
    (hp : LinearIndependent ℂ p) (x z : ℂ) :
    z ∈ shiftedWronskianRoots p x ↔ (polynomialWronskian p).eval (z - x) = 0 := by
  classical
  simp only [shiftedWronskianRoots, Finset.mem_image, Multiset.mem_toFinset,
    Polynomial.mem_roots (polynomialWronskian_ne_zero_of_linearIndependent p hp),
    Polynomial.IsRoot.def]
  constructor
  · rintro ⟨a, ha, hax⟩
    have heq : z - x = a := by rw [← hax]; ring
    simpa only [heq] using ha
  · intro h
    exact ⟨z - x, h, by ring⟩

theorem shiftedWronskianRoots_card_le {m d n : ℕ} (p : Fin m → Polynomial ℂ)
    (hp : LinearIndependent ℂ p) (hdeg : ∀ i, (p i).natDegree ≤ d) (hdn : d ≤ n)
    (x : ℂ) : (shiftedWronskianRoots p x).card ≤ wronskianRootCountBound n := by
  calc
    (shiftedWronskianRoots p x).card ≤ (polynomialWronskian p).roots.toFinset.card :=
      Finset.card_image_le
    _ ≤ (polynomialWronskian p).roots.card := Multiset.toFinset_card_le _
    _ ≤ (polynomialWronskian p).natDegree := Polynomial.card_roots' _
    _ ≤ wronskianRootCountBound n := polynomialWronskian_natDegree_le_rootCountBound p hp hdeg hdn

theorem shiftedWronskianRoots_empty (p : Fin 0 → Polynomial ℂ) (x : ℂ) :
    shiftedWronskianRoots p x = ∅ := by
  simp [shiftedWronskianRoots]

theorem shiftedWronskianRoots_eq_empty_of_full_span {m : ℕ}
    (p : Fin m → Polynomial ℂ) (hp : LinearIndependent ℂ p)
    (hfull : Submodule.span ℂ (Set.range p) = Polynomial.degreeLT ℂ m) (x : ℂ) :
    shiftedWronskianRoots p x = ∅ := by
  obtain ⟨c, _, hc⟩ := (polynomialWronskian_eq_nonzero_constant_iff_span p hp).mpr hfull
  simp [shiftedWronskianRoots, hc]

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
  classical
  have hunion : (Finset.univ.biUnion (fun d => shiftedWronskianRoots (p d) x)).card ≤
      n * wronskianRootCountBound n := by
    calc
      _ ≤ ∑ d : Fin n, (shiftedWronskianRoots (p d) x).card := Finset.card_biUnion_le
      _ ≤ ∑ _d : Fin n, wronskianRootCountBound n :=
        Finset.sum_le_sum (fun d _ => shiftedWronskianRoots_card_le (p d) (hp d)
          (hdeg d) (by omega) x)
      _ = n * wronskianRootCountBound n := by simp
  unfold forbiddenWronskianSet forbiddenWronskianCountBound
  cases query with
  | none => simpa using hunion.trans (Nat.le_succ _)
  | some z =>
    have h := Finset.card_union_le
      (Finset.univ.biUnion (fun d => shiftedWronskianRoots (p d) x)) {z}
    simp only [Finset.card_singleton] at h
    exact h.trans (Nat.add_le_add_right hunion 1)

theorem polynomialNestedBasis_linearIndependent {m d : ℕ}
    (V : Submodule ℂ (Polynomial.degreeLT ℂ (d + 1))) (b : Module.Basis (Fin m) ℂ V) :
    LinearIndependent ℂ (fun i => ((b i).val : Polynomial ℂ)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hkernel : ∑ k, c k • b k = 0 := by
    apply Subtype.ext
    apply Subtype.ext
    simpa only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero] using hc
  have hrepr := congrArg (fun u : V => b.repr u i) hkernel
  simpa [Finsupp.single_apply] using hrepr

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
  exact polynomialNestedBasis_linearIndependent (polynomialKernelSpace L j d)
    (polynomialKernelBasis L j d)

theorem polynomialKernelFamily_degree_le (L : ℕ → Polynomial ℂ →ₗ[ℂ] ℂ) (j d : ℕ)
    (i : Fin (polynomialKernelDimension L j d)) :
    (polynomialKernelFamily L j d i).natDegree ≤ d := by
  have hh := Polynomial.mem_degreeLT.mp (polynomialKernelBasis L j d i).val.property
  change (polynomialKernelFamily L j d i).degree < (d + 1 : WithBot ℕ) at hh
  rw [Polynomial.degree_eq_natDegree ((polynomialKernelFamily_linearIndependent L j d).ne_zero i)] at hh
  have hlt : (polynomialKernelFamily L j d i).natDegree < d + 1 := by exact_mod_cast hh
  omega

theorem polynomialKernelFamily_annihilated (L : ℕ → Polynomial ℂ →ₗ[ℂ] ℂ) (j d : ℕ)
    (k : Fin (polynomialKernelDimension L j d)) :
    ∀ i < j, L i (polynomialKernelFamily L j d k) = 0 :=
  (mem_scalarPrefixKernel _ _ _).mp (polynomialKernelBasis L j d k).property

theorem mem_span_polynomialKernelFamily (L : ℕ → Polynomial ℂ →ₗ[ℂ] ℂ) (j d : ℕ)
    (q : Polynomial ℂ) :
    q ∈ Submodule.span ℂ (Set.range (polynomialKernelFamily L j d)) ↔
      q.natDegree ≤ d ∧ ∀ i < j, L i q = 0 := by
  classical
  constructor
  · intro hq
    constructor
    · have hle : Submodule.span ℂ (Set.range (polynomialKernelFamily L j d)) ≤
          Polynomial.degreeLT ℂ (d + 1) := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact (polynomialKernelBasis L j d i).val.property
      have hh := Polynomial.mem_degreeLT.mp (hle hq)
      by_cases hzero : q = 0
      · simp [hzero]
      · rw [Polynomial.degree_eq_natDegree hzero] at hh
        have hlt : q.natDegree < d + 1 := by exact_mod_cast hh
        omega
    · intro i hi
      have hle : Submodule.span ℂ (Set.range (polynomialKernelFamily L j d)) ≤ (L i).ker := by
        rw [Submodule.span_le]
        rintro _ ⟨k, rfl⟩
        exact polynomialKernelFamily_annihilated L j d k i hi
      exact hle hq
  · rintro ⟨hdeg, hLq⟩
    have hqdeg : q ∈ Polynomial.degreeLT ℂ (d + 1) := by
      apply Polynomial.mem_degreeLT.mpr
      apply Polynomial.degree_le_natDegree.trans_lt
      exact_mod_cast Nat.lt_succ_of_le hdeg
    let q' : Polynomial.degreeLT ℂ (d + 1) := ⟨q, hqdeg⟩
    have hq' : q' ∈ polynomialKernelSpace L j d := (mem_scalarPrefixKernel _ _ _).mpr hLq
    let q'' : polynomialKernelSpace L j d := ⟨q', hq'⟩
    let b := polynomialKernelBasis L j d
    have hrepr := congrArg (fun r : polynomialKernelSpace L j d => (r.val : Polynomial ℂ))
      (b.sum_repr q'')
    apply (Submodule.mem_span_range_iff_exists_fun ℂ).mpr
    refine ⟨fun i => b.repr q'' i, ?_⟩
    simpa only [Submodule.coe_sum, Submodule.coe_smul, polynomialKernelFamily, b] using hrepr

/-- The manuscript's actual forbidden set for an arbitrary prefix of scalar polynomial data. -/
def polynomialKernelForbiddenSet (L : ℕ → Polynomial ℂ →ₗ[ℂ] ℂ)
    (j n : ℕ) (x : ℂ) (query : Option ℂ) : Finset ℂ :=
  forbiddenWronskianSet (fun d : Fin n => polynomialKernelFamily L j (d.val + 1)) x query

theorem polynomialKernelForbiddenSet_card_le (L : ℕ → Polynomial ℂ →ₗ[ℂ] ℂ)
    (j n : ℕ) (x : ℂ) (query : Option ℂ) :
    (polynomialKernelForbiddenSet L j n x query).card ≤ forbiddenWronskianCountBound n := by
  exact forbiddenWronskianSet_card_le _
    (fun d => polynomialKernelFamily_linearIndependent L j (d.val + 1))
    (fun d => polynomialKernelFamily_degree_le L j (d.val + 1)) x query

theorem mem_forbiddenWronskianSet {n : ℕ} {dim : Fin n → ℕ}
    (p : (d : Fin n) → Fin (dim d) → Polynomial ℂ)
    (hp : ∀ d, LinearIndependent ℂ (p d)) (x z : ℂ) (query : Option ℂ) :
    z ∈ forbiddenWronskianSet p x query ↔
      (∃ d, (polynomialWronskian (p d)).eval (z - x) = 0) ∨ query = some z := by
  classical
  have hmem (d : Fin n) := mem_shiftedWronskianRoots (p d) (hp d) x z
  simp only [forbiddenWronskianSet, Finset.mem_union, Finset.mem_biUnion,
    Finset.mem_univ, true_and, hmem]
  cases query <;> simp [eq_comm]

theorem polynomialKernelForbiddenSet_contains_wronskian_zero
    (L : ℕ → Polynomial ℂ →ₗ[ℂ] ℂ) (j n d : ℕ) (hd : 0 < d) (hdn : d ≤ n)
    (x z : ℂ) (query : Option ℂ)
    (hz : (polynomialWronskian (polynomialKernelFamily L j d)).eval z = 0) :
    x + z ∈ polynomialKernelForbiddenSet L j n x query := by
  apply (mem_forbiddenWronskianSet _
    (fun k => polynomialKernelFamily_linearIndependent L j (k.val + 1)) x (x + z) query).mpr
  left
  let k : Fin n := ⟨d - 1, by omega⟩
  refine ⟨k, ?_⟩
  have hk : k.val + 1 = d := Nat.sub_add_cancel hd
  change (polynomialWronskian (polynomialKernelFamily L j (k.val + 1))).eval (x + z - x) = 0
  rw [hk, add_sub_cancel_left]
  exact hz

theorem polynomialKernelForbiddenSet_contains_query
    (L : ℕ → Polynomial ℂ →ₗ[ℂ] ℂ) (j n : ℕ) (x z : ℂ) :
    z ∈ polynomialKernelForbiddenSet L j n x (some z) := by
  apply (mem_forbiddenWronskianSet _
    (fun k => polynomialKernelFamily_linearIndependent L j (k.val + 1)) x z (some z)).mpr
  exact Or.inr rfl

theorem shiftedWronskianRoots_basis_independent {m : ℕ}
    (V : Submodule ℂ (Polynomial ℂ)) (b b' : Module.Basis (Fin m) ℂ V) (x : ℂ) :
    shiftedWronskianRoots (fun i => (b' i : Polynomial ℂ)) x =
      shiftedWronskianRoots (fun i => (b i : Polynomial ℂ)) x := by
  ext z
  have hb : LinearIndependent ℂ (fun i => (b i : Polynomial ℂ)) :=
    b.linearIndependent.map' V.subtype (by simp)
  have hb' : LinearIndependent ℂ (fun i => (b' i : Polynomial ℂ)) :=
    b'.linearIndependent.map' V.subtype (by simp)
  rw [mem_shiftedWronskianRoots _ hb', mem_shiftedWronskianRoots _ hb]
  exact polynomialWronskian_basis_eval_eq_zero_iff V b b' (z - x)

theorem shiftedWronskianRoots_eq_of_span_eq {m k : ℕ}
    (p : Fin m → Polynomial ℂ) (q : Fin k → Polynomial ℂ)
    (hp : LinearIndependent ℂ p) (hq : LinearIndependent ℂ q)
    (hspan : Submodule.span ℂ (Set.range p) = Submodule.span ℂ (Set.range q)) (x : ℂ) :
    shiftedWronskianRoots p x = shiftedWronskianRoots q x := by
  have hdim := congrArg (fun U : Submodule ℂ (Polynomial ℂ) => Module.finrank ℂ U) hspan
  rw [Module.finrank_eq_card_basis (Module.Basis.span hp),
    Module.finrank_eq_card_basis (Module.Basis.span hq), Fintype.card_fin, Fintype.card_fin] at hdim
  subst k
  ext z
  rw [mem_shiftedWronskianRoots p hp, mem_shiftedWronskianRoots q hq,
    polynomialWronskian_eval_eq_zero_iff_span p hp,
    polynomialWronskian_eval_eq_zero_iff_span q hq, hspan]

theorem polynomialKernelFamily_span_congr (L L' : ℕ → Polynomial ℂ →ₗ[ℂ] ℂ)
    (j d : ℕ) (hL : ∀ i < j, L i = L' i) :
    Submodule.span ℂ (Set.range (polynomialKernelFamily L j d)) =
      Submodule.span ℂ (Set.range (polynomialKernelFamily L' j d)) := by
  ext q
  rw [mem_span_polynomialKernelFamily, mem_span_polynomialKernelFamily]
  constructor
  · rintro ⟨hdeg, hzero⟩
    exact ⟨hdeg, fun i hi => by rw [← hL i hi]; exact hzero i hi⟩
  · rintro ⟨hdeg, hzero⟩
    exact ⟨hdeg, fun i hi => by rw [hL i hi]; exact hzero i hi⟩

/-- Later rows do not affect the forbidden set of a fixed prefix, regardless of basis choices. -/
theorem polynomialKernelForbiddenSet_congr (L L' : ℕ → Polynomial ℂ →ₗ[ℂ] ℂ)
    (j n : ℕ) (x : ℂ) (query : Option ℂ) (hL : ∀ i < j, L i = L' i) :
    polynomialKernelForbiddenSet L j n x query = polynomialKernelForbiddenSet L' j n x query := by
  classical
  unfold polynomialKernelForbiddenSet forbiddenWronskianSet
  congr 1
  apply Finset.biUnion_congr rfl
  intro d _
  exact shiftedWronskianRoots_eq_of_span_eq _ _
    (polynomialKernelFamily_linearIndependent L j (d.val + 1))
    (polynomialKernelFamily_linearIndependent L' j (d.val + 1))
    (polynomialKernelFamily_span_congr L L' j (d.val + 1) hL) x

end KungTraub
