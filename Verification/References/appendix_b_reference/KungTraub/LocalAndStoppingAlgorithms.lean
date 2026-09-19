import appendix_b_reference.KungTraub.GroupedFlattening
import Mathlib.Tactic

/-!
# Stopping and partially defined observation rules

A bounded decision tree may return an output before exhausting its observations.
Its exact execution is represented by a fixed-length scalar oracle by adding idle
queries after termination. Partially defined query and output rules also admit a
total extension preserving every defined execution. Consequently a local estimate
on a full punctured neighbourhood transfers to that total extension.

These statements justify the model conventions in Section 1.1 of Matthew J.
Colbrook's manuscript. No decision rule receives the input function or its root;
the function enters only when the selected observations are evaluated. Finite
tuple identities and the previously proved prefix uniqueness lemma supply the
execution comparisons.
-/

noncomputable section

namespace KungTraub

/-- An observation tree of depth at most `n`. A leaf may occur at any depth;
continuation branches receive only the answer to the selected query. -/
inductive BoundedRealTree : ℕ → Type where
  | stop {n : ℕ} (value : ℝ) : BoundedRealTree n
  | observe {n : ℕ} (query : RealQuery) (next : ℝ → BoundedRealTree n) :
      BoundedRealTree (n + 1)

/-- Execution of a bounded tree stops as soon as a leaf is reached. -/
def BoundedRealTree.run : {n : ℕ} → BoundedRealTree n → (ℝ → ℝ) → ℝ
  | _, .stop y, _ => y
  | _, .observe q next, f => (next (q.answer f)).run f

/-- The actual number of derivative observations; idle queries have zero cost. -/
def BoundedRealTree.observationCount : {n : ℕ} → BoundedRealTree n → (ℝ → ℝ) → ℕ
  | _, .stop _, _ => 0
  | _, .observe q next, f =>
      (match q with | .idle => 0 | .derivative _ _ => 1) +
        (next (q.answer f)).observationCount f

/-- The index of the tree bounds every execution's number of observations. -/
theorem BoundedRealTree.observationCount_le {n : ℕ} (tree : BoundedRealTree n)
    (f : ℝ → ℝ) : tree.observationCount f ≤ n := by
  sorry

/-- The padded query at a scalar position. At a leaf every remaining query is idle. -/
def BoundedRealTree.paddedQuery : {n : ℕ} → BoundedRealTree n →
    (j : Fin n) → (Fin j.val → ℝ) → RealQuery
  | _, .stop _, _ => fun _ => .idle
  | _, .observe q next, j =>
      Fin.cases (fun _ => q)
        (fun i history =>
          (next (history ⟨0, Nat.succ_pos i.val⟩)).paddedQuery i (Fin.tail history)) j

/-- The padded output recovers the original leaf from the supplied scalar answers. -/
def BoundedRealTree.paddedOutput : {n : ℕ} → BoundedRealTree n → (Fin n → ℝ) → ℝ
  | _, .stop y, _ => y
  | _, .observe _ next, history => (next (history 0)).paddedOutput (Fin.tail history)

/-- The true answer vector completed by zeros after termination. -/
def BoundedRealTree.paddedAnswers : {n : ℕ} → BoundedRealTree n →
    (ℝ → ℝ) → (Fin n → ℝ)
  | _, .stop _, _ => fun _ => 0
  | _, .observe q next, f => Fin.cons (q.answer f) ((next (q.answer f)).paddedAnswers f)

/-- Every padded query receives exactly the corresponding true or idle answer. -/
theorem BoundedRealTree.paddedQuery_answer {n : ℕ} (tree : BoundedRealTree n)
    (f : ℝ → ℝ) (j : Fin n) :
    (tree.paddedQuery j
      (scalarPrefixRestriction (tree.paddedAnswers f) j.val j.isLt.le)).answer f =
        tree.paddedAnswers f j := by
  sorry

/-- Padding retains the output of the stopping execution. -/
theorem BoundedRealTree.paddedOutput_answers {n : ℕ} (tree : BoundedRealTree n)
    (f : ℝ → ℝ) : tree.paddedOutput (tree.paddedAnswers f) = tree.run f := by
  sorry

/-- A stationary stopping algorithm chooses its bounded decision tree from the starting
point alone. No input function or distinguished root is supplied to it. -/
abbrev StoppingRealAlgorithm (n : ℕ) := ℝ → BoundedRealTree n

/-- The output of the bounded stopping algorithm on an input function. -/
def StoppingRealAlgorithm.run {n : ℕ} (A : StoppingRealAlgorithm n)
    (f : ℝ → ℝ) (x : ℝ) : ℝ := (A x).run f

/-- Fixed-length scalar representation, padding terminated branches by idle queries. -/
def StoppingRealAlgorithm.padded {n : ℕ} (A : StoppingRealAlgorithm n) :
    RealAlgorithm n where
  query j x history := (A x).paddedQuery j history
  output x history := (A x).paddedOutput history

/-- Every prefix of the padded execution is the corresponding true answer prefix. -/
theorem StoppingRealAlgorithm.padded_prefix {n : ℕ} (A : StoppingRealAlgorithm n)
    (f : ℝ → ℝ) (x : ℝ) (j : ℕ) (hj : j ≤ n) :
    A.padded.prefix f x j hj = scalarPrefixRestriction ((A x).paddedAnswers f) j hj := by
  sorry

/-- Exact output equivalence holds for every input and starting point, including
executions that terminate before making any observation. -/
theorem StoppingRealAlgorithm.padded_run_eq {n : ℕ} (A : StoppingRealAlgorithm n)
    (f : ℝ → ℝ) (x : ℝ) : A.padded.run f x = A.run f x := by
  sorry

/-- Local order is unchanged by padding a stopping algorithm. -/
theorem StoppingRealAlgorithm.localOrderAt_padded_iff {n : ℕ}
    (A : StoppingRealAlgorithm n) (f : ℝ → ℝ) (α p : ℝ) :
    LocalOrderAt A.padded.run f α p ↔ LocalOrderAt A.run f α p := by
  sorry

/-- Partial stage and output rules. Undefined transcripts are represented by `none`;
the rules still receive only the starting point and the preceding scalar answers. -/
structure PartialRealAlgorithm (n : ℕ) where
  query : (j : Fin n) → ℝ → (Fin j.val → ℝ) → Option RealQuery
  output : ℝ → (Fin n → ℝ) → Option ℝ

/-- A partial execution fails exactly when one of its selected stage rules is undefined. -/
def PartialRealAlgorithm.prefix {n : ℕ} (A : PartialRealAlgorithm n)
    (f : ℝ → ℝ) (x : ℝ) : (j : ℕ) → j ≤ n → Option (Fin j → ℝ)
  | 0, _ => some Fin.elim0
  | j + 1, hj => do
      let hlt : j < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hj
      let previous ← A.prefix f x j hlt.le
      let q ← A.query ⟨j, hlt⟩ x previous
      pure (Fin.snoc previous (q.answer f))

/-- A defined output requires all selected stage rules and the final output rule to exist. -/
def PartialRealAlgorithm.run {n : ℕ} (A : PartialRealAlgorithm n)
    (f : ℝ → ℝ) (x : ℝ) : Option ℝ := do
  let answers ← A.prefix f x n le_rfl
  A.output x answers

/-- An arbitrary total extension: undefined query rules become idle, and an undefined
output becomes zero. No regularity is required or asserted for this extension. -/
def PartialRealAlgorithm.totalExtension {n : ℕ} (A : PartialRealAlgorithm n) :
    RealAlgorithm n where
  query j x history := (A.query j x history).getD .idle
  output x history := (A.output x history).getD 0

/-- Every defined partial prefix is preserved by the total extension. -/
theorem PartialRealAlgorithm.totalExtension_prefix_eq {n : ℕ}
    (A : PartialRealAlgorithm n) (f : ℝ → ℝ) (x : ℝ)
    (j : ℕ) (hj : j ≤ n) {answers : Fin j → ℝ}
    (h : A.prefix f x j hj = some answers) :
    A.totalExtension.prefix f x j hj = answers := by
  sorry

/-- Every defined partial output agrees exactly with the total extension's output. -/
theorem PartialRealAlgorithm.totalExtension_run_eq {n : ℕ}
    (A : PartialRealAlgorithm n) (f : ℝ → ℝ) (x : ℝ) {y : ℝ}
    (h : A.run f x = some y) : A.totalExtension.run f x = y := by
  sorry

/-- A defined stage retains the exact query, including its location and derivative
order, along the total extension's actual execution. -/
theorem PartialRealAlgorithm.totalExtension_actualQuery_eq {n : ℕ}
    (A : PartialRealAlgorithm n) (f : ℝ → ℝ) (x : ℝ) (j : Fin n)
    {answers : Fin j.val → ℝ} {q : RealQuery}
    (hp : A.prefix f x j.val j.isLt.le = some answers)
    (hq : A.query j x answers = some q) :
    A.totalExtension.actualQuery f x j = q := by
  sorry

/-- Being defined on a full punctured neighbourhood. This domain condition does not
discard any nearby starting point on the basis of the observed answers. -/
def PartialRealAlgorithm.DefinedNear {n : ℕ} (A : PartialRealAlgorithm n)
    (f : ℝ → ℝ) (α : ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, 0 < |x - α| → |x - α| < δ →
    ∃ y : ℝ, A.run f x = some y

/-- The local order estimate for a partial method includes defined execution at every
sufficiently close nonroot start, as required by the manuscript's local model. -/
def PartialRealAlgorithm.LocalOrderAt {n : ℕ} (A : PartialRealAlgorithm n)
    (f : ℝ → ℝ) (α p : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧
    ∀ x : ℝ, 0 < |x - α| → |x - α| < δ →
      ∃ y : ℝ, A.run f x = some y ∧ |y - α| ≤ C * Real.rpow |x - α| p

/-- A local estimate on defined executions transfers to the total extension. -/
theorem PartialRealAlgorithm.localOrderAt_totalExtension {n : ℕ}
    (A : PartialRealAlgorithm n) (f : ℝ → ℝ) (α p : ℝ)
    (h : A.LocalOrderAt f α p) : KungTraub.LocalOrderAt A.totalExtension.run f α p := by
  sorry

/-- On a full punctured neighbourhood of definition, total extension preserves and
reflects the local order estimate; only the neighbourhood may be reduced. -/
theorem PartialRealAlgorithm.localOrderAt_totalExtension_iff {n : ℕ}
    (A : PartialRealAlgorithm n) (f : ℝ → ℝ) (α p : ℝ)
    (hdefined : A.DefinedNear f α) :
    KungTraub.LocalOrderAt A.totalExtension.run f α p ↔ A.LocalOrderAt f α p := by
  sorry

end KungTraub
