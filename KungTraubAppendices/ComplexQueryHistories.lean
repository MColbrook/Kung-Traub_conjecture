import KungTraubAppendices.ComplexAffineOracle

/-!
# Finite histories of complex derivative queries

The construction follows `KungTraub.QueryHistories` for the complex oracle.
One complex answer counts as one observation, and locations range over ℂ.

A finite history determines the query-node set and the largest requested
derivative order at each node. Corrections preserve these derivative values.
After `s` executions of at most `n` queries, there are at most `n*s` nodes.
-/

noncomputable section

namespace KungTraubAppendices

local instance instDecidableEqComplexQueryForHistory : DecidableEq ComplexQuery := Classical.decEq _

def complexQueryNodes (Q : Finset ComplexQuery) : Finset ℂ := by
  classical
  exact Q.biUnion (fun q => match q with
    | .derivative z _ => {z}
    | .idle => ∅)

def complexQueryOrderAt (z : ℂ) : ComplexQuery → ℕ
  | .derivative y k => if y = z then k else 0
  | .idle => 0

def complexMaxQueryOrder (Q : Finset ComplexQuery) (z : ℂ) : ℕ := Q.sup (complexQueryOrderAt z)

theorem mem_complexQueryNodes_iff (Q : Finset ComplexQuery) (z : ℂ) :
    z ∈ complexQueryNodes Q ↔ ∃ k : ℕ, ComplexQuery.derivative z k ∈ Q := by
  classical
  simp only [complexQueryNodes, Finset.mem_biUnion]
  constructor
  · rintro ⟨q, hq, hz⟩
    cases q with
    | idle => simp at hz
    | derivative y k =>
      have hy : z = y := Finset.mem_singleton.mp hz
      subst y
      exact ⟨k, hq⟩
  · rintro ⟨k, hk⟩
    exact ⟨.derivative z k, hk, Finset.mem_singleton_self z⟩

theorem complex_query_order_le_maxQueryOrder {Q : Finset ComplexQuery} {z : ℂ} {k : ℕ}
    (hq : ComplexQuery.derivative z k ∈ Q) : k ≤ complexMaxQueryOrder Q z := by
  have h := Finset.le_sup (f := complexQueryOrderAt z) hq
  simpa [complexQueryOrderAt, complexMaxQueryOrder] using h

theorem complexQueryNodes_card_le (Q : Finset ComplexQuery) : (complexQueryNodes Q).card ≤ Q.card := by
  classical
  unfold complexQueryNodes
  calc
    _ ≤ ∑ q ∈ Q, (match q with | .derivative z _ => ({z} : Finset ℂ) | .idle => ∅).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _q ∈ Q, 1 := by
      apply Finset.sum_le_sum
      intro q _
      cases q <;> simp
    _ = Q.card := by simp

theorem complexQueryNodes_mono {Q Q' : Finset ComplexQuery} (hQQ' : Q ⊆ Q') :
    complexQueryNodes Q ⊆ complexQueryNodes Q' := by
  intro z hz
  obtain ⟨k, hk⟩ := (mem_complexQueryNodes_iff Q z).mp hz
  exact (mem_complexQueryNodes_iff Q' z).mpr ⟨k, hQQ' hk⟩

theorem complexMaxQueryOrder_mono {Q Q' : Finset ComplexQuery} (hQQ' : Q ⊆ Q') (z : ℂ) :
    complexMaxQueryOrder Q z ≤ complexMaxQueryOrder Q' z := Finset.sup_mono hQQ'

def ComplexAlgorithm.actualQuerySet {n : ℕ} (A : ComplexAlgorithm n) (f : ℂ → ℂ) (x : ℂ) :
    Finset ComplexQuery := by
  classical
  exact Finset.univ.image (A.actualQuery f x)

theorem ComplexAlgorithm.mem_actualQuerySet {n : ℕ} (A : ComplexAlgorithm n)
    (f : ℂ → ℂ) (x : ℂ) (i : Fin n) : A.actualQuery f x i ∈ A.actualQuerySet f x := by
  classical
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

theorem ComplexAlgorithm.actualQuerySet_card_le {n : ℕ} (A : ComplexAlgorithm n)
    (f : ℂ → ℂ) (x : ℂ) : (A.actualQuerySet f x).card ≤ n := by
  classical
  exact Finset.card_image_le.trans (by simp)

def ComplexAlgorithm.queryHistory {n : ℕ} (A : ComplexAlgorithm n)
    (functions : ℕ → ℂ → ℂ) (starts : ℕ → ℂ) (s : ℕ) : Finset ComplexQuery := by
  classical
  exact (Finset.range s).biUnion (fun i => A.actualQuerySet (functions i) (starts i))

theorem ComplexAlgorithm.queryHistory_zero {n : ℕ} (A : ComplexAlgorithm n)
    (functions : ℕ → ℂ → ℂ) (starts : ℕ → ℂ) : A.queryHistory functions starts 0 = ∅ := by
  classical
  simp [queryHistory]

theorem ComplexAlgorithm.queryHistory_succ {n : ℕ} (A : ComplexAlgorithm n)
    (functions : ℕ → ℂ → ℂ) (starts : ℕ → ℂ) (s : ℕ) :
    A.queryHistory functions starts (s + 1) =
      A.actualQuerySet (functions s) (starts s) ∪ A.queryHistory functions starts s := by
  classical
  simp [queryHistory, Finset.range_add_one, Finset.biUnion_insert]

theorem ComplexAlgorithm.mem_queryHistory {n : ℕ} (A : ComplexAlgorithm n)
    (functions : ℕ → ℂ → ℂ) (starts : ℕ → ℂ) {s i : ℕ} (hi : i < s) (j : Fin n) :
    A.actualQuery (functions i) (starts i) j ∈ A.queryHistory functions starts s := by
  classical
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr hi,
    A.mem_actualQuerySet (functions i) (starts i) j⟩

theorem ComplexAlgorithm.queryHistory_mono {n : ℕ} (A : ComplexAlgorithm n)
    (functions : ℕ → ℂ → ℂ) (starts : ℕ → ℂ) {s t : ℕ} (hst : s ≤ t) :
    A.queryHistory functions starts s ⊆ A.queryHistory functions starts t := by
  classical
  exact Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.range_mono hst)

theorem ComplexAlgorithm.queryHistory_card_le {n : ℕ} (A : ComplexAlgorithm n)
    (functions : ℕ → ℂ → ℂ) (starts : ℕ → ℂ) (s : ℕ) :
    (A.queryHistory functions starts s).card ≤ n * s := by
  classical
  calc
    _ ≤ ∑ i ∈ Finset.range s, (A.actualQuerySet (functions i) (starts i)).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ Finset.range s, n :=
      Finset.sum_le_sum (fun i _ => A.actualQuerySet_card_le (functions i) (starts i))
    _ = n * s := by simp [Nat.mul_comm]

theorem ComplexAlgorithm.queryHistory_nodes_card_le {n : ℕ} (A : ComplexAlgorithm n)
    (functions : ℕ → ℂ → ℂ) (starts : ℕ → ℂ) (s : ℕ) :
    (complexQueryNodes (A.queryHistory functions starts s)).card ≤ n * s :=
  (complexQueryNodes_card_le _).trans (A.queryHistory_card_le functions starts s)

theorem ComplexAlgorithm.queryHistory_covers_derivative {n : ℕ} (A : ComplexAlgorithm n)
    (functions : ℕ → ℂ → ℂ) (starts : ℕ → ℂ) {s i : ℕ} (hi : i < s)
    (j : Fin n) {z : ℂ} {k : ℕ}
    (hquery : A.actualQuery (functions i) (starts i) j = .derivative z k) :
    z ∈ complexQueryNodes (A.queryHistory functions starts s) ∧
      k ≤ complexMaxQueryOrder (A.queryHistory functions starts s) z := by
  have hmem := A.mem_queryHistory functions starts hi j
  rw [hquery] at hmem
  exact ⟨(mem_complexQueryNodes_iff _ z).mpr ⟨k, hmem⟩, complex_query_order_le_maxQueryOrder hmem⟩

end KungTraubAppendices
