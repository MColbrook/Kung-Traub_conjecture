import appendix_b_reference.KungTraub.AffineTranscripts

/-!
# Finite histories of actual derivative queries

The entire construction preserves every earlier requested derivative. A finite
query history determines its node set and the largest requested derivative order
at each node. Repetitions and idle slots do not change that information. The
history of s completed n-query executions has at most n*s distinct nodes.
-/

noncomputable section

namespace KungTraub

local instance instDecidableEqRealQuery : DecidableEq RealQuery := Classical.decEq _

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
  sorry

theorem query_order_le_maxQueryOrder {Q : Finset RealQuery} {z : ℝ} {k : ℕ}
    (hq : RealQuery.derivative z k ∈ Q) : k ≤ maxQueryOrder Q z := by
  sorry

theorem queryNodes_card_le (Q : Finset RealQuery) : (queryNodes Q).card ≤ Q.card := by
  sorry

theorem queryNodes_mono {Q Q' : Finset RealQuery} (hQQ' : Q ⊆ Q') :
    queryNodes Q ⊆ queryNodes Q' := by
  sorry

theorem maxQueryOrder_mono {Q Q' : Finset RealQuery} (hQQ' : Q ⊆ Q') (z : ℝ) :
    maxQueryOrder Q z ≤ maxQueryOrder Q' z := by
  sorry

def RealAlgorithm.actualQuerySet {n : ℕ} (A : RealAlgorithm n) (f : ℝ → ℝ) (x : ℝ) :
    Finset RealQuery := by
  classical
  exact Finset.univ.image (A.actualQuery f x)

theorem RealAlgorithm.mem_actualQuerySet {n : ℕ} (A : RealAlgorithm n)
    (f : ℝ → ℝ) (x : ℝ) (i : Fin n) : A.actualQuery f x i ∈ A.actualQuerySet f x := by
  sorry

theorem RealAlgorithm.actualQuerySet_card_le {n : ℕ} (A : RealAlgorithm n)
    (f : ℝ → ℝ) (x : ℝ) : (A.actualQuerySet f x).card ≤ n := by
  sorry

def RealAlgorithm.queryHistory {n : ℕ} (A : RealAlgorithm n)
    (functions : ℕ → ℝ → ℝ) (starts : ℕ → ℝ) (s : ℕ) : Finset RealQuery := by
  classical
  exact (Finset.range s).biUnion (fun i => A.actualQuerySet (functions i) (starts i))

theorem RealAlgorithm.queryHistory_zero {n : ℕ} (A : RealAlgorithm n)
    (functions : ℕ → ℝ → ℝ) (starts : ℕ → ℝ) : A.queryHistory functions starts 0 = ∅ := by
  sorry

theorem RealAlgorithm.queryHistory_succ {n : ℕ} (A : RealAlgorithm n)
    (functions : ℕ → ℝ → ℝ) (starts : ℕ → ℝ) (s : ℕ) :
    A.queryHistory functions starts (s + 1) =
      A.actualQuerySet (functions s) (starts s) ∪ A.queryHistory functions starts s := by
  sorry

theorem RealAlgorithm.mem_queryHistory {n : ℕ} (A : RealAlgorithm n)
    (functions : ℕ → ℝ → ℝ) (starts : ℕ → ℝ) {s i : ℕ} (hi : i < s) (j : Fin n) :
    A.actualQuery (functions i) (starts i) j ∈ A.queryHistory functions starts s := by
  sorry

theorem RealAlgorithm.queryHistory_mono {n : ℕ} (A : RealAlgorithm n)
    (functions : ℕ → ℝ → ℝ) (starts : ℕ → ℝ) {s t : ℕ} (hst : s ≤ t) :
    A.queryHistory functions starts s ⊆ A.queryHistory functions starts t := by
  sorry

theorem RealAlgorithm.queryHistory_card_le {n : ℕ} (A : RealAlgorithm n)
    (functions : ℕ → ℝ → ℝ) (starts : ℕ → ℝ) (s : ℕ) :
    (A.queryHistory functions starts s).card ≤ n * s := by
  sorry

theorem RealAlgorithm.queryHistory_nodes_card_le {n : ℕ} (A : RealAlgorithm n)
    (functions : ℕ → ℝ → ℝ) (starts : ℕ → ℝ) (s : ℕ) :
    (queryNodes (A.queryHistory functions starts s)).card ≤ n * s := by
  sorry

theorem RealAlgorithm.queryHistory_covers_derivative {n : ℕ} (A : RealAlgorithm n)
    (functions : ℕ → ℝ → ℝ) (starts : ℕ → ℝ) {s i : ℕ} (hi : i < s)
    (j : Fin n) {z : ℝ} {k : ℕ}
    (hquery : A.actualQuery (functions i) (starts i) j = .derivative z k) :
    z ∈ queryNodes (A.queryHistory functions starts s) ∧
      k ≤ maxQueryOrder (A.queryHistory functions starts s) z := by
  sorry

end KungTraub
