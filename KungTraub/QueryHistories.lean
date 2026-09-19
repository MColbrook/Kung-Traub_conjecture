import KungTraub.AffineTranscripts

/-!
# Finite histories of actual derivative queries

The entire construction preserves every earlier requested derivative. A finite
query history determines its node set and the largest requested derivative order
at each node. Repetitions and idle slots do not change that information. The
history of s completed n-query executions has at most n*s distinct nodes.
-/

noncomputable section

namespace KungTraub

local instance : DecidableEq RealQuery := Classical.decEq _

def queryNodes (Q : Finset RealQuery) : Finset ℝ := by
  classical
  exact Q.biUnion (fun q => match q with
    | .derivative z _ => {z}
    | .idle => ∅)

def queryOrderAt (z : ℝ) : RealQuery → ℕ
  | .derivative y k => if y = z then k else 0
  | .idle => 0

def maxQueryOrder (Q : Finset RealQuery) (z : ℝ) : ℕ := Q.sup (queryOrderAt z)

theorem mem_queryNodes_iff (Q : Finset RealQuery) (z : ℝ) :
    z ∈ queryNodes Q ↔ ∃ k : ℕ, RealQuery.derivative z k ∈ Q := by
  classical
  simp only [queryNodes, Finset.mem_biUnion]
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

theorem query_order_le_maxQueryOrder {Q : Finset RealQuery} {z : ℝ} {k : ℕ}
    (hq : RealQuery.derivative z k ∈ Q) : k ≤ maxQueryOrder Q z := by
  have h := Finset.le_sup (f := queryOrderAt z) hq
  simpa [queryOrderAt, maxQueryOrder] using h

theorem queryNodes_card_le (Q : Finset RealQuery) : (queryNodes Q).card ≤ Q.card := by
  classical
  unfold queryNodes
  calc
    _ ≤ ∑ q ∈ Q, (match q with | .derivative z _ => ({z} : Finset ℝ) | .idle => ∅).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _q ∈ Q, 1 := by
      apply Finset.sum_le_sum
      intro q _
      cases q <;> simp
    _ = Q.card := by simp

theorem queryNodes_mono {Q Q' : Finset RealQuery} (hQQ' : Q ⊆ Q') :
    queryNodes Q ⊆ queryNodes Q' := by
  intro z hz
  obtain ⟨k, hk⟩ := (mem_queryNodes_iff Q z).mp hz
  exact (mem_queryNodes_iff Q' z).mpr ⟨k, hQQ' hk⟩

theorem maxQueryOrder_mono {Q Q' : Finset RealQuery} (hQQ' : Q ⊆ Q') (z : ℝ) :
    maxQueryOrder Q z ≤ maxQueryOrder Q' z := Finset.sup_mono hQQ'

def RealAlgorithm.actualQuerySet {n : ℕ} (A : RealAlgorithm n) (f : ℝ → ℝ) (x : ℝ) :
    Finset RealQuery := by
  classical
  exact Finset.univ.image (A.actualQuery f x)

theorem RealAlgorithm.mem_actualQuerySet {n : ℕ} (A : RealAlgorithm n)
    (f : ℝ → ℝ) (x : ℝ) (i : Fin n) : A.actualQuery f x i ∈ A.actualQuerySet f x := by
  classical
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

theorem RealAlgorithm.actualQuerySet_card_le {n : ℕ} (A : RealAlgorithm n)
    (f : ℝ → ℝ) (x : ℝ) : (A.actualQuerySet f x).card ≤ n := by
  classical
  exact Finset.card_image_le.trans (by simp)

def RealAlgorithm.queryHistory {n : ℕ} (A : RealAlgorithm n)
    (functions : ℕ → ℝ → ℝ) (starts : ℕ → ℝ) (s : ℕ) : Finset RealQuery := by
  classical
  exact (Finset.range s).biUnion (fun i => A.actualQuerySet (functions i) (starts i))

theorem RealAlgorithm.queryHistory_zero {n : ℕ} (A : RealAlgorithm n)
    (functions : ℕ → ℝ → ℝ) (starts : ℕ → ℝ) : A.queryHistory functions starts 0 = ∅ := by
  classical
  simp [queryHistory]

theorem RealAlgorithm.queryHistory_succ {n : ℕ} (A : RealAlgorithm n)
    (functions : ℕ → ℝ → ℝ) (starts : ℕ → ℝ) (s : ℕ) :
    A.queryHistory functions starts (s + 1) =
      A.actualQuerySet (functions s) (starts s) ∪ A.queryHistory functions starts s := by
  classical
  simp [queryHistory, Finset.range_add_one, Finset.biUnion_insert]

theorem RealAlgorithm.mem_queryHistory {n : ℕ} (A : RealAlgorithm n)
    (functions : ℕ → ℝ → ℝ) (starts : ℕ → ℝ) {s i : ℕ} (hi : i < s) (j : Fin n) :
    A.actualQuery (functions i) (starts i) j ∈ A.queryHistory functions starts s := by
  classical
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr hi,
    A.mem_actualQuerySet (functions i) (starts i) j⟩

theorem RealAlgorithm.queryHistory_mono {n : ℕ} (A : RealAlgorithm n)
    (functions : ℕ → ℝ → ℝ) (starts : ℕ → ℝ) {s t : ℕ} (hst : s ≤ t) :
    A.queryHistory functions starts s ⊆ A.queryHistory functions starts t := by
  classical
  exact Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.range_mono hst)

theorem RealAlgorithm.queryHistory_card_le {n : ℕ} (A : RealAlgorithm n)
    (functions : ℕ → ℝ → ℝ) (starts : ℕ → ℝ) (s : ℕ) :
    (A.queryHistory functions starts s).card ≤ n * s := by
  classical
  calc
    _ ≤ ∑ i ∈ Finset.range s, (A.actualQuerySet (functions i) (starts i)).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ Finset.range s, n :=
      Finset.sum_le_sum (fun i _ => A.actualQuerySet_card_le (functions i) (starts i))
    _ = n * s := by simp [Nat.mul_comm]

theorem RealAlgorithm.queryHistory_nodes_card_le {n : ℕ} (A : RealAlgorithm n)
    (functions : ℕ → ℝ → ℝ) (starts : ℕ → ℝ) (s : ℕ) :
    (queryNodes (A.queryHistory functions starts s)).card ≤ n * s :=
  (queryNodes_card_le _).trans (A.queryHistory_card_le functions starts s)

theorem RealAlgorithm.queryHistory_covers_derivative {n : ℕ} (A : RealAlgorithm n)
    (functions : ℕ → ℝ → ℝ) (starts : ℕ → ℝ) {s i : ℕ} (hi : i < s)
    (j : Fin n) {z : ℝ} {k : ℕ}
    (hquery : A.actualQuery (functions i) (starts i) j = .derivative z k) :
    z ∈ queryNodes (A.queryHistory functions starts s) ∧
      k ≤ maxQueryOrder (A.queryHistory functions starts s) z := by
  have hmem := A.mem_queryHistory functions starts hi j
  rw [hquery] at hmem
  exact ⟨(mem_queryNodes_iff _ z).mpr ⟨k, hmem⟩, query_order_le_maxQueryOrder hmem⟩

end KungTraub
