import KungTraubAppendices.ComplexConclusion

/-!
# Partial complex algorithms and total extensions

The Option-valued oracle and prefix identities follow
`KungTraub.LocalAndStoppingAlgorithms`. Each slot contains one complex answer;
local orders have real exponents, and input domains are arbitrary open sets.

Undefined query rules are extended by idle queries and undefined outputs by
zero. The extension preserves every defined execution. Local order requires
defined and admissible execution at every sufficiently close nonroot start.
-/

noncomputable section
open Filter
open scoped Topology
namespace KungTraubAppendices

/-- Partial stage and output rules. Undefined transcripts are represented by `none`;
the rules receive the starting point and the preceding scalar answers. -/
structure PartialComplexAlgorithm (n : ℕ) where
  query : (j : Fin n) → ℂ → (Fin j.val → ℂ) → Option ComplexQuery
  output : ℂ → (Fin n → ℂ) → Option ℂ

/-- A partial execution fails exactly when one of its selected stage rules is undefined. -/
def PartialComplexAlgorithm.prefix {n : ℕ} (A : PartialComplexAlgorithm n)
    (f : ℂ → ℂ) (x : ℂ) : (j : ℕ) → j ≤ n → Option (Fin j → ℂ)
  | 0, _ => some Fin.elim0
  | j + 1, hj => do
      let hlt : j < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hj
      let previous ← A.prefix f x j hlt.le
      let q ← A.query ⟨j, hlt⟩ x previous
      pure (Fin.snoc previous (q.answer f))

/-- A defined output requires all selected stage rules and the final output rule to exist. -/
def PartialComplexAlgorithm.run {n : ℕ} (A : PartialComplexAlgorithm n)
    (f : ℂ → ℂ) (x : ℂ) : Option ℂ := do
  let answers ← A.prefix f x n le_rfl
  A.output x answers

/-- An arbitrary total extension: undefined query rules become idle, and an undefined
output becomes zero. -/
def PartialComplexAlgorithm.totalExtension {n : ℕ} (A : PartialComplexAlgorithm n) :
    ComplexAlgorithm n where
  query j x history := (A.query j x history).getD .idle
  output x history := (A.output x history).getD 0

/-- Every defined partial prefix is preserved by the total extension. -/
theorem PartialComplexAlgorithm.totalExtension_prefix_eq {n : ℕ}
    (A : PartialComplexAlgorithm n) (f : ℂ → ℂ) (x : ℂ)
    (j : ℕ) (hj : j ≤ n) {answers : Fin j → ℂ}
    (h : A.prefix f x j hj = some answers) :
    A.totalExtension.prefix f x j hj = answers := by
  induction j with
  | zero => exact Option.some.inj h
  | succ j ih =>
    have hjn : j < n := by omega
    cases hp : A.prefix f x j hjn.le with
    | none => simp [PartialComplexAlgorithm.prefix, hp] at h
    | some previous =>
      cases hq : A.query ⟨j, hjn⟩ x previous with
      | none => simp [PartialComplexAlgorithm.prefix, hp, hq] at h
      | some q =>
        have ha : Fin.snoc previous (q.answer f) = answers := by
          simpa [PartialComplexAlgorithm.prefix, hp, hq] using h
        simp only [ComplexAlgorithm.prefix]
        rw [ih hjn.le hp]
        simpa [totalExtension, hq] using ha

/-- Every defined partial output agrees exactly with the total extension's output. -/
theorem PartialComplexAlgorithm.totalExtension_run_eq {n : ℕ}
    (A : PartialComplexAlgorithm n) (f : ℂ → ℂ) (x : ℂ) {y : ℂ}
    (h : A.run f x = some y) : A.totalExtension.run f x = y := by
  cases hp : A.prefix f x n le_rfl with
  | none => simp [PartialComplexAlgorithm.run, hp] at h
  | some answers =>
    have ho : A.output x answers = some y := by
      simpa [PartialComplexAlgorithm.run, hp] using h
    rw [ComplexAlgorithm.run, A.totalExtension_prefix_eq f x n le_rfl hp]
    simp [totalExtension, ho]

/-- A defined stage retains the exact query, including its location and derivative
order, along the total extension's actual execution. -/
theorem PartialComplexAlgorithm.totalExtension_actualQuery_eq {n : ℕ}
    (A : PartialComplexAlgorithm n) (f : ℂ → ℂ) (x : ℂ) (j : Fin n)
    {answers : Fin j.val → ℂ} {q : ComplexQuery}
    (hp : A.prefix f x j.val j.isLt.le = some answers)
    (hq : A.query j x answers = some q) :
    A.totalExtension.actualQuery f x j = q := by
  rw [ComplexAlgorithm.actualQuery, A.totalExtension_prefix_eq f x j.val j.isLt.le hp]
  simp [totalExtension, hq]

/-- Every actually selected stage is defined and its location lies in the given
input domain. Idle slots impose no location condition. The final output's
existence is separately required by the local-order predicate. -/
def PartialComplexAlgorithm.ExecutionIn {n : ℕ} (A : PartialComplexAlgorithm n)
    (f : ℂ → ℂ) (x : ℂ) (U : Set ℂ) : Prop :=
  ∀ j : Fin n, ∃ answers : Fin j.val → ℂ, ∃ q : ComplexQuery,
    A.prefix f x j.val j.isLt.le = some answers ∧
    A.query j x answers = some q ∧
    match q with
    | .derivative z _ => z ∈ U
    | .idle => True

/-- Exact query preservation transfers all actual location constraints, without
requiring any condition on the arbitrarily completed undefined transcripts. -/
theorem PartialComplexAlgorithm.executionIn_totalExtension {n : ℕ}
    (A : PartialComplexAlgorithm n) (f : ℂ → ℂ) (x : ℂ) (U : Set ℂ)
    (h : A.ExecutionIn f x U) : A.totalExtension.ExecutionIn f x U := by
  intro j
  obtain ⟨answers, q, hp, hq, hdomain⟩ := h j
  change match A.totalExtension.actualQuery f x j with
    | .derivative z _ => z ∈ U
    | .idle => True
  rw [A.totalExtension_actualQuery_eq f x j hp hq]
  exact hdomain

/-- Defined execution on every sufficiently close punctured complex start. -/
def PartialComplexAlgorithm.DefinedNear {n : ℕ} (A : PartialComplexAlgorithm n)
    (f : ℂ → ℂ) (α : ℂ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℂ, 0 < ‖x - α‖ → ‖x - α‖ < δ →
    ∃ y : ℂ, A.run f x = some y

/-- The partial local estimate requires a defined output at every nearby
nonroot start, with one constant and one neighbourhood chosen before the start. -/
def PartialComplexAlgorithm.LocalOrderAt {n : ℕ} (A : PartialComplexAlgorithm n)
    (f : ℂ → ℂ) (α : ℂ) (p : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧
    ∀ x : ℂ, 0 < ‖x - α‖ → ‖x - α‖ < δ →
      ∃ y : ℂ, A.run f x = some y ∧ ‖y - α‖ ≤ C * Real.rpow ‖x - α‖ p

/-- A local estimate for the partial execution gives the identical estimate for
its total extension, at all starts in the same punctured neighbourhood. -/
theorem PartialComplexAlgorithm.localOrderAt_totalExtension {n : ℕ}
    (A : PartialComplexAlgorithm n) (f : ℂ → ℂ) (α : ℂ) (p : ℝ)
    (h : A.LocalOrderAt f α p) : ComplexLocalOrderAt A.totalExtension.run f α p := by
  obtain ⟨C, hC, δ, hδ, h⟩ := h
  refine ⟨C, hC, δ, hδ, ?_⟩
  intro x hx hnear
  obtain ⟨y, hy, hbound⟩ := h x hx hnear
  rw [A.totalExtension_run_eq f x hy]
  exact hbound

/-- On a full neighbourhood of definition, extension preserves and reflects
local order; the common neighbourhood may be reduced by taking a minimum. -/
theorem PartialComplexAlgorithm.localOrderAt_totalExtension_iff {n : ℕ}
    (A : PartialComplexAlgorithm n) (f : ℂ → ℂ) (α : ℂ) (p : ℝ)
    (hdefined : A.DefinedNear f α) :
    ComplexLocalOrderAt A.totalExtension.run f α p ↔ A.LocalOrderAt f α p := by
  constructor
  · rintro ⟨C, hC, δ, hδ, hbound⟩
    obtain ⟨η, hη, hdefined⟩ := hdefined
    refine ⟨C, hC, min δ η, lt_min hδ hη, ?_⟩
    intro x hx hnear
    obtain ⟨y, hy⟩ := hdefined x hx (lt_of_lt_of_le hnear (min_le_right _ _))
    refine ⟨y, hy, ?_⟩
    have hb := hbound x hx (lt_of_lt_of_le hnear (min_le_left _ _))
    rwa [A.totalExtension_run_eq f x hy] at hb
  · exact A.localOrderAt_totalExtension f α p

/-- The full arbitrary-open-domain predicate, with actual admissible and defined
executions and the error estimate throughout one punctured neighbourhood. -/
def PartialComplexAlgorithm.UniversalLocalOrder {n : ℕ} (A : PartialComplexAlgorithm n)
    (p : ℝ) : Prop :=
  ∀ U : Set ℂ, IsOpen U → ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U →
    ∀ α : ℂ, α ∈ U → SimpleComplexRoot f α →
      ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧
        ∀ x : ℂ, 0 < ‖x - α‖ → ‖x - α‖ < δ →
          x ∈ U ∧ A.ExecutionIn f x U ∧
            ∃ y : ℂ, A.run f x = some y ∧ ‖y - α‖ ≤ C * Real.rpow ‖x - α‖ p

/-- Defined and admissible local execution transfers to the total extension. -/
theorem PartialComplexAlgorithm.universalLocalOrder_totalExtension {n : ℕ}
    (A : PartialComplexAlgorithm n) (p : ℝ) (h : A.UniversalLocalOrder p) :
    ComplexUniversalLocalOrder A.totalExtension p := by
  intro U hU f hf α hα hroot
  obtain ⟨C, hC, δ, hδ, hlocal⟩ := h U hU f hf α hα hroot
  refine ⟨C, hC, δ, hδ, ?_⟩
  intro x hx hnear
  obtain ⟨hxU, hexecution, y, hy, hbound⟩ := hlocal x hx hnear
  refine ⟨hxU, A.executionIn_totalExtension f x U hexecution, ?_⟩
  rw [A.totalExtension_run_eq f x hy]
  exact hbound

/-- The counterexample for the total extension also excludes partial local
order: failure to be defined near the root cannot satisfy the partial predicate. -/
theorem PartialComplexAlgorithm.not_localOrderAt_of_divergence {n : ℕ}
    (A : PartialComplexAlgorithm n) {f : ℂ → ℂ} {α : ℂ} {p : ℝ} {starts : ℕ → ℂ}
    (hw : ComplexWitnessData f α starts)
    (hdiv : Tendsto (fun i => complexErrorRatio A.totalExtension.run f α p (starts i)) atTop atTop) :
    ¬ A.LocalOrderAt f α p := by
  intro h
  exact not_complexLocalOrderAt_of_divergence hw hdiv (A.localOrderAt_totalExtension f α p h)

/-- Every partial method has an actual entire witness on which its full
punctured-neighbourhood local-order requirement fails. The same witness retains
the derivative/unique-root/nonroot-start properties of the total theorem. -/
theorem PartialComplexAlgorithm.exists_entire_not_localOrder {n : ℕ}
    (A : PartialComplexAlgorithm n) (hn : 1 ≤ n) (p : ℝ)
    (hp : (KungTraub.orderBound n : ℝ) < p) :
    ∃ f : ℂ → ℂ, ∃ α : ℂ, ∃ starts : ℕ → ℂ,
      ComplexWitnessData f α starts ∧ ¬ A.LocalOrderAt f α p := by
  obtain ⟨f, α, starts, hw, hdiv⟩ := complex_entire_counterexample hn A.totalExtension p hp
  exact ⟨f, α, starts, hw, A.not_localOrderAt_of_divergence hw hdiv⟩

/-- The upper bound also holds for arbitrary partial complex rules,
with defined and admissible execution required at every nearby nonroot start. -/
theorem no_complex_partial_universal_order_above {n : ℕ} (hn : 1 ≤ n)
    (A : PartialComplexAlgorithm n) (p : ℝ) (hp : (KungTraub.orderBound n : ℝ) < p) :
    ¬ A.UniversalLocalOrder p := by
  intro h
  exact no_complex_universal_order_above hn A.totalExtension p hp
    (A.universalLocalOrder_totalExtension p h)

end KungTraubAppendices
