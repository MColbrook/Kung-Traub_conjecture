import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic

/-!
# Independent statements for the Palomar submission

This module states the twelve principal results of Matthew J. Colbrook's
*Adversarial Wronskians: A proof of the Kung–Traub conjecture*. It imports only
Mathlib. The concrete definitions below are copied from the development, so
Comparator can compare their values as well as the principal theorem statements
against the proved declarations available from `All`. Only the twelve theorem
proofs at the end are deliberately left as reference placeholders.

For every positive scalar budget, the real results exclude every real exponent
strictly above `2^(n-1)`. Their entire real-type witnesses have a unique real
zero, global derivative bounds `3/4 ≤ f' ≤ 5/4`, and divergent error ratios along
independent nonroot starts converging to that zero. The simultaneous statement
chooses one function and one sequence before quantifying over all larger
exponents. The grouped results use prescribed positive group sizes and the
threshold `ℓ₁ * ∏ j ≥ 2, (ℓⱼ + 1)`; queries within a group cannot depend on its
answers.

The two complex results count one complex derivative value as one observation.
The entire witness has derivative within `1/4` of one on the closed unit disc
and a zero strictly inside that disc, unique there. The universal-order
consequence includes admissible queries on arbitrary open complex domains.

For budgets at least two, the three attainment and sharpness results concern
the concrete inverse Hermite algorithm defined below. It attains `2^(n-1)`
on analytic inputs on open real intervals, with every query inside the interval.
On `exp(x)-1`, its two-sided leading coefficient is
`sharpnessCoefficient (n-1)`, and every strictly larger real order fails.

All oracle rules here are total, deterministic, stationary, and have no memory
between updates. The starting sequence need not be an iteration orbit. Bounded
stopping is represented by idle padding. For partially defined procedures, the
universal-order obstruction transfers through a total extension on a full
punctured neighbourhood of defined executions; the counterexample assertions
here concern that total extension. No claim of defined execution on arbitrary
inputs is made for the original partial procedure.
-/

set_option autoImplicit false

noncomputable section

open Filter
open scoped BigOperators Topology

namespace KungTraub

/-- The exponent after `n` scalar observations, with the induction's initial value at zero. -/
def orderBound (n : ℕ) : ℕ :=
  if n = 0 then 1 else 2 ^ (n - 1)

/-- The exponent for fixed group sizes. The empty product has value one. -/
def groupedOrderBound {k : ℕ} (sizes : Fin k → ℕ) : ℕ :=
  ∏ j : Fin k, if j.val = 0 then sizes j else sizes j + 1

/-- Total number of scalar query slots in a prescribed group schedule. -/
def groupedObservationCount {k : ℕ} (sizes : Fin k → ℕ) : ℕ :=
  ∑ j : Fin k, sizes j

/-- One real derivative observation, or an information-free padding slot without a location. -/
inductive RealQuery where
  | derivative (location : ℝ) (order : ℕ)
  | idle

/-- The answer to a derivative query or an idle slot. -/
def RealQuery.answer (query : RealQuery) (f : ℝ → ℝ) : ℝ :=
  match query with
  | .derivative z ν => iteratedDeriv ν f z
  | .idle => 0

/-- A deterministic stationary memoryless method with at most `n` real scalar observations.
The history supplied to query `j` has exactly `j` earlier answers. There are no regularity or
computability assumptions on these rules, and neither rule receives the input function or root.
Early termination is represented by padding and an output rule retaining the earlier result. -/
structure RealAlgorithm (n : ℕ) where
  query : (j : Fin n) → ℝ → (Fin j.val → ℝ) → RealQuery
  output : ℝ → (Fin n → ℝ) → ℝ

/-- The first `j` answers of a real execution. The bound only permits stages within its budget. -/
def RealAlgorithm.prefix {n : ℕ} (A : RealAlgorithm n) (f : ℝ → ℝ) (x : ℝ) :
    (j : ℕ) → j ≤ n → (Fin j → ℝ)
  | 0, _ => Fin.elim0
  | j + 1, hj =>
      let hlt : j < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hj
      let previous := A.prefix f x j (Nat.le_of_lt hlt)
      Fin.snoc previous ((A.query ⟨j, hlt⟩ x previous).answer f)

/-- The real output after the algorithm's bounded observation execution. -/
def RealAlgorithm.run {n : ℕ} (A : RealAlgorithm n) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  A.output x (A.prefix f x n le_rfl)

/-- Answers in the first `j` groups, with their fixed numbers of scalar entries. The embedding
of a preceding group into the full schedule carries only its index bound, not any input data. -/
abbrev GroupPrefix {k : ℕ} (sizes : Fin k → ℕ) (j : ℕ) (hj : j ≤ k) :=
  (i : Fin j) → Fin (sizes ⟨i.val, Nat.lt_of_lt_of_le i.isLt hj⟩) → ℝ

/-- A method with fixed groups of scalar observations. Query selection for a group receives
only complete earlier groups, so no answer within the current group can affect another query
in that group. The final theorems require `k > 0` and all sizes positive. -/
structure GroupedRealAlgorithm {k : ℕ} (sizes : Fin k → ℕ) where
  query : (j : Fin k) → ℝ → GroupPrefix sizes j.val (Nat.le_of_lt j.isLt) →
    (Fin (sizes j) → RealQuery)
  output : ℝ → GroupPrefix sizes k le_rfl → ℝ

/-- The answers in the first `j` complete groups. The query vector is selected once, from
the preceding groups, before its scalar answers are evaluated. -/
def GroupedRealAlgorithm.prefix {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedRealAlgorithm sizes) (f : ℝ → ℝ) (x : ℝ) :
    (j : ℕ) → (hj : j ≤ k) → GroupPrefix sizes j hj
  | 0, _ => fun i => Fin.elim0 i
  | j + 1, hj =>
      let hlt : j < k := Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hj
      let previous := A.prefix f x j (Nat.le_of_lt hlt)
      let queries := A.query ⟨j, hlt⟩ x previous
      fun i => Fin.lastCases (fun slot => (queries slot).answer f) (fun h => previous h) i

/-- The output of the grouped execution; only answers from its fixed schedule are available. -/
def GroupedRealAlgorithm.run {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedRealAlgorithm sizes) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  A.output x (A.prefix f x k le_rfl)

/-- A scalar update map, evaluated on a real function and an independent real starting point.
Only the oracle model's `run` maps instantiate this type in the final algorithm statements. -/
abbrev RealUpdate := (ℝ → ℝ) → ℝ → ℝ

/-- An entire complex function whose values on the real axis are real. -/
def EntireRealType (F : ℂ → ℂ) : Prop :=
  Differentiable ℂ F ∧ ∀ t : ℝ, (F (t : ℂ)).im = 0

/-- The real restriction of a complex function. `EntireRealType` ensures that taking the real
part discards no information on the real axis. -/
def realRestriction (F : ℂ → ℂ) (t : ℝ) : ℝ :=
  (F (t : ℂ)).re

/-- A specified simple real zero. The zero is used in the mathematical property and is not
supplied to any query-selection or output rule. -/
def SimpleRealRoot (f : ℝ → ℝ) (α : ℝ) : Prop :=
  f α = 0 ∧ deriv f α ≠ 0

/-- The local error estimate at every sufficiently close nonroot starting point. The constants
may depend on the fixed update, function, selected root, and real exponent. -/
def LocalOrderAt (T : RealUpdate) (f : ℝ → ℝ) (α p : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧
    ∀ x : ℝ, 0 < |x - α| → |x - α| < δ →
      |T f x - α| ≤ C * Real.rpow |x - α| p

/-- Universal local order on the primary class: every entire real-type input, at every simple
real zero. The root is quantified after the input and is absent from the algorithm's data. -/
def EntireUniversalLocalOrder (T : RealUpdate) (p : ℝ) : Prop :=
  ∀ F : ℂ → ℂ, EntireRealType F →
    ∀ α : ℝ, SimpleRealRoot (realRestriction F) α →
      LocalOrderAt T (realRestriction F) α p

/-- Universal local order for functions analytic at every real point. -/
def AnalyticUniversalLocalOrder (T : RealUpdate) (p : ℝ) : Prop :=
  ∀ f : ℝ → ℝ, (∀ t : ℝ, AnalyticAt ℝ f t) →
    ∀ α : ℝ, SimpleRealRoot f α → LocalOrderAt T f α p

/-- The analytic, geometric, and derivative properties of the main counterexample. Its zero
is unique on the real line, not necessarily in the complex plane. The starts are independent
inputs and need not form an output orbit of a method. -/
def EntireWitnessData (F : ℂ → ℂ) (α : ℝ) (starts : ℕ → ℝ) : Prop :=
  EntireRealType F ∧
    (∀ t : ℝ, (3 / 4 : ℝ) ≤ deriv (realRestriction F) t ∧
      deriv (realRestriction F) t ≤ (5 / 4 : ℝ)) ∧
    realRestriction F α = 0 ∧
    (∀ t : ℝ, realRestriction F t = 0 → t = α) ∧
    Tendsto starts atTop (𝓝 α) ∧
    (∀ s : ℕ, starts s ≠ α)

/-- The error ratio for a real exponent. Nonzero starting distances are required separately
by the witness data and by the punctured-neighbourhood local estimate. -/
def errorRatio (T : RealUpdate) (f : ℝ → ℝ) (α p x : ℝ) : ℝ :=
  |T f x - α| / Real.rpow |x - α| p

/-- The error ratios tend to positive infinity along the entire sequence of starting points. -/
def ErrorRatioDiverges (T : RealUpdate) (F : ℂ → ℂ) (α : ℝ)
    (starts : ℕ → ℝ) (p : ℝ) : Prop :=
  Tendsto (fun s => errorRatio T (realRestriction F) α p (starts s)) atTop atTop

/-- An entire counterexample at one prescribed exponent, including all of the source theorem's
global derivative and real-root properties. -/
def EntireCounterexample (T : RealUpdate) (p : ℝ) : Prop :=
  ∃ F : ℂ → ℂ, ∃ α : ℝ, ∃ starts : ℕ → ℝ,
    EntireWitnessData F α starts ∧ ErrorRatioDiverges T F α starts p

/-- One entire input and one sequence that defeat every exponent above a fixed bound. The
existential witnesses precede the universal exponent quantifier. -/
def SimultaneousEntireCounterexample (T : RealUpdate) (bound : ℝ) : Prop :=
  ∃ F : ℂ → ℂ, ∃ α : ℝ, ∃ starts : ℕ → ℝ,
    EntireWitnessData F α starts ∧
      ∀ p : ℝ, bound < p → ErrorRatioDiverges T F α starts p

end KungTraub

/-! ## The bounded tree and padding used by the attaining method -/

namespace KungTraub

/-- An observation tree of depth at most `n`. A leaf may occur at any depth;
continuation branches receive only the answer to the selected query. -/
inductive BoundedRealTree : ℕ → Type where
  | stop {n : ℕ} (value : ℝ) : BoundedRealTree n
  | observe {n : ℕ} (query : RealQuery) (next : ℝ → BoundedRealTree n) :
      BoundedRealTree (n + 1)

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

/-- A stationary stopping algorithm chooses its bounded decision tree from the starting
point alone. No input function or distinguished root is supplied to it. -/
abbrev StoppingRealAlgorithm (n : ℕ) := ℝ → BoundedRealTree n

/-- Fixed-length scalar representation, padding terminated branches by idle queries. -/
def StoppingRealAlgorithm.padded {n : ℕ} (A : StoppingRealAlgorithm n) :
    RealAlgorithm n where
  query j x history := (A x).paddedQuery j history
  output x history := (A x).paddedOutput history

end KungTraub

/-! ## Complex observations and local domains -/

namespace KungTraubAppendices

/-- One complex derivative observation, or a zero-cost slot after stopping. -/
inductive ComplexQuery where
  | derivative (location : ℂ) (order : ℕ)
  | idle

/-- The answer to a query. Final input classes guarantee all required derivatives. -/
def ComplexQuery.answer (q : ComplexQuery) (f : ℂ → ℂ) : ℂ :=
  match q with
  | .derivative z ν => iteratedDeriv ν f z
  | .idle => 0

/-- A deterministic stationary method with at most `n` complex scalar observations.
The dependent history prevents access to the current or any later answer. -/
structure ComplexAlgorithm (n : ℕ) where
  query : (j : Fin n) → ℂ → (Fin j.val → ℂ) → ComplexQuery
  output : ℂ → (Fin n → ℂ) → ℂ

/-- The actual answer prefix, defined recursively in observation order. -/
def ComplexAlgorithm.prefix {n : ℕ} (A : ComplexAlgorithm n) (f : ℂ → ℂ) (x : ℂ) :
    (j : ℕ) → j ≤ n → (Fin j → ℂ)
  | 0, _ => Fin.elim0
  | j + 1, hj =>
      let hlt : j < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hj
      let previous := A.prefix f x j (Nat.le_of_lt hlt)
      Fin.snoc previous ((A.query ⟨j, hlt⟩ x previous).answer f)

/-- Output of the actual adaptive execution. -/
def ComplexAlgorithm.run {n : ℕ} (A : ComplexAlgorithm n) (f : ℂ → ℂ) (x : ℂ) : ℂ :=
  A.output x (A.prefix f x n le_rfl)

/-- All actual query locations lie in the input domain. Idle slots have no location. -/
def ComplexAlgorithm.ExecutionIn {n : ℕ} (A : ComplexAlgorithm n)
    (f : ℂ → ℂ) (x : ℂ) (U : Set ℂ) : Prop :=
  ∀ j : Fin n,
    match A.query j x (A.prefix f x j.val j.isLt.le) with
    | .derivative z _ => z ∈ U
    | .idle => True

/-- The function vanishes at the root and has nonzero derivative there. -/
def SimpleComplexRoot (f : ℂ → ℂ) (α : ℂ) : Prop :=
  f α = 0 ∧ deriv f α ≠ 0

/-- A local estimate on every sufficiently close nonroot complex start. -/
def ComplexLocalOrderAt (T : (ℂ → ℂ) → ℂ → ℂ) (f : ℂ → ℂ)
    (α : ℂ) (p : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧
    ∀ x : ℂ, 0 < ‖x - α‖ → ‖x - α‖ < δ →
      ‖T f x - α‖ ≤ C * Real.rpow ‖x - α‖ p

/-- Universal order on holomorphic inputs on arbitrary open domains. Domain
admissibility and the error estimate hold on one full punctured neighbourhood. -/
def ComplexUniversalLocalOrder {n : ℕ} (A : ComplexAlgorithm n) (p : ℝ) : Prop :=
  ∀ U : Set ℂ, IsOpen U → ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U →
    ∀ α : ℂ, α ∈ U → SimpleComplexRoot f α →
      ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧
        ∀ x : ℂ, 0 < ‖x - α‖ → ‖x - α‖ < δ →
          x ∈ U ∧ A.ExecutionIn f x U ∧
            ‖A.run f x - α‖ ≤ C * Real.rpow ‖x - α‖ p

/-- The geometric and analytic properties of the entire witness, with a unique
root on the closed unit disc.
Index `i : ℕ` corresponds to stage `s = i + 1`. -/
def ComplexWitnessData (f : ℂ → ℂ) (α : ℂ) (starts : ℕ → ℂ) : Prop :=
  Differentiable ℂ f ∧
    (∀ z : ℂ, ‖z‖ ≤ 1 → ‖deriv f z - 1‖ ≤ (1 / 4 : ℝ)) ∧
    f α = 0 ∧ ‖α‖ < 1 ∧
    (∀ z : ℂ, ‖z‖ ≤ 1 → f z = 0 → z = α) ∧
    Tendsto starts atTop (𝓝 α) ∧ (∀ i : ℕ, starts i ≠ α)

/-- The error ratio uses a real exponent even for complex inputs. -/
def complexErrorRatio (T : (ℂ → ℂ) → ℂ → ℂ) (f : ℂ → ℂ)
    (α : ℂ) (p : ℝ) (x : ℂ) : ℝ :=
  ‖T f x - α‖ / Real.rpow ‖x - α‖ p

/-- One fixed entire input and one sequence whose ratios tend to positive infinity.
 -/
def ComplexEntireCounterexample (T : (ℂ → ℂ) → ℂ → ℂ) (p : ℝ) : Prop :=
  ∃ f : ℂ → ℂ, ∃ α : ℂ, ∃ starts : ℕ → ℂ,
    ComplexWitnessData f α starts ∧
      Tendsto (fun i => complexErrorRatio T f α p (starts i)) atTop atTop

end KungTraubAppendices

/-! ## The concrete inverse Hermite update -/

namespace KungTraubAppendices

open Polynomial

variable {𝕜 ι : Type*} [Field 𝕜] [DecidableEq ι]

/-- Interpolate the values at distinct nodes and one prescribed derivative at `i`.
The formula is total on arbitrary data; its characteristic properties require
the stated membership and injectivity hypotheses. -/
def hermiteWithDerivative (s : Finset ι) (nodes values : ι → 𝕜)
    (i : ι) (d : 𝕜) : 𝕜[X] :=
  Lagrange.interpolate s nodes values +
    C ((d - (Lagrange.interpolate s nodes values).derivative.eval (nodes i)) /
      (Lagrange.nodal s nodes).derivative.eval (nodes i)) * Lagrange.nodal s nodes

end KungTraubAppendices

namespace KungTraubAppendices

local instance instDecidableEqReal : DecidableEq ℝ := Classical.decEq ℝ

/-- The remaining value observations after the initial value and derivative.
`functionValues` are inverse-interpolation nodes; `points` are their ordinates.
The distinguished node `0` always denotes the initial observation. -/
def inverseHermiteTail : (remaining j : ℕ) →
    (Fin (j + 1) → ℝ) → (Fin (j + 1) → ℝ) → ℝ → ℝ →
      KungTraub.BoundedRealTree remaining
  | 0, _, _, _, _, next => .stop next
  | remaining + 1, j, functionValues, points, reciprocalDerivative, next =>
      .observe (.derivative next 0) fun value =>
        if value = 0 then .stop next else
          let extendedValues := Fin.snoc functionValues value
          let extendedPoints := Fin.snoc points next
          let H := hermiteWithDerivative Finset.univ extendedValues extendedPoints
            (0 : Fin (j + 2)) reciprocalDerivative
          inverseHermiteTail remaining (j + 1) extendedValues extendedPoints
            reciprocalDerivative (H.eval 0)

/-- The full bounded observation tree. Budgets below two are arbitrary total
extensions; all Appendix A results require `n ≥ 2`. -/
def inverseHermiteTree : (n : ℕ) → ℝ → KungTraub.BoundedRealTree n
  | 0, x => .stop x
  | 1, x => .stop x
  | remaining + 2, x =>
      .observe (.derivative x 0) fun value =>
        if value = 0 then .stop x else
          .observe (.derivative x 1) fun derivative =>
            if derivative = 0 then .stop x else
              inverseHermiteTail remaining 0 (fun _ => value) (fun _ => x)
                derivative⁻¹ (x - value / derivative)

/-- The stationary method chooses its bounded tree from the starting point alone. -/
def inverseHermiteMethod (n : ℕ) : KungTraub.StoppingRealAlgorithm n :=
  inverseHermiteTree n

/-- The same actual method in the fixed-slot oracle model, with idle padding. -/
def inverseHermiteAlgorithm (n : ℕ) : KungTraub.RealAlgorithm n :=
  (inverseHermiteMethod n).padded

/-- Every actual derivative-query location belongs to the real input domain. -/
def realExecutionIn {n : ℕ} (A : KungTraub.RealAlgorithm n)
    (f : ℝ → ℝ) (x : ℝ) (U : Set ℝ) : Prop :=
  ∀ j : Fin n,
    match A.query j x (A.prefix f x j.val j.isLt.le) with
    | .derivative z _ => z ∈ U
    | .idle => True

/-- The full interval-local attainment property, including query admissibility.
The input domain and its analytic function precede the local constants. -/
def RealIntervalUniversalLocalOrder {n : ℕ} (A : KungTraub.RealAlgorithm n)
    (p : ℝ) : Prop :=
  ∀ U : Set ℝ, IsOpen U → Set.OrdConnected U →
    ∀ f : ℝ → ℝ, (∀ t ∈ U, AnalyticAt ℝ f t) →
      ∀ α : ℝ, α ∈ U → KungTraub.SimpleRealRoot f α →
        ∃ C : ℝ, 0 < C ∧ ∃ δ : ℝ, 0 < δ ∧
          ∀ x : ℝ, 0 < |x - α| → |x - α| < δ →
            x ∈ U ∧ realExecutionIn A f x U ∧
              |A.run f x - α| ≤ C * Real.rpow |x - α| p

/-- The leading coefficients on `exp(x)-1`. Index zero is a harmless initial
convention; the empty product gives exactly `κ₁=1/2`. -/
def sharpnessCoefficient : ℕ → ℝ
  | 0 => 1
  | j + 1 => (∏ i : Fin j, sharpnessCoefficient (i.val + 1)) / ((j : ℝ) + 2)
termination_by j => j
decreasing_by omega

end KungTraubAppendices

/-! ## Principal reference statements -/

namespace KungTraub

theorem entire_counterexample {n : ℕ} (hn : 1 ≤ n) (A : RealAlgorithm n)
    (p : ℝ) (hp : (orderBound n : ℝ) < p) :
    EntireCounterexample A.run p := by
  sorry

theorem no_entire_universal_order_above {n : ℕ} (hn : 1 ≤ n) (A : RealAlgorithm n)
    (p : ℝ) (hp : (orderBound n : ℝ) < p) :
    ¬ EntireUniversalLocalOrder A.run p := by
  sorry

theorem no_universal_order_above {n : ℕ} (hn : 1 ≤ n) (A : RealAlgorithm n)
    (p : ℝ) (hp : (orderBound n : ℝ) < p) :
    ¬ AnalyticUniversalLocalOrder A.run p := by
  sorry

theorem grouped_entire_counterexample {k : ℕ} (hk : 1 ≤ k) (sizes : Fin k → ℕ)
    (hsize : ∀ j, 1 ≤ sizes j) (A : GroupedRealAlgorithm sizes)
    (p : ℝ) (hp : (groupedOrderBound sizes : ℝ) < p) :
    EntireCounterexample A.run p := by
  sorry

theorem no_grouped_entire_universal_order_above {k : ℕ} (hk : 1 ≤ k)
    (sizes : Fin k → ℕ) (hsize : ∀ j, 1 ≤ sizes j) (A : GroupedRealAlgorithm sizes)
    (p : ℝ) (hp : (groupedOrderBound sizes : ℝ) < p) :
    ¬ EntireUniversalLocalOrder A.run p := by
  sorry

theorem no_grouped_universal_order_above {k : ℕ} (hk : 1 ≤ k)
    (sizes : Fin k → ℕ) (hsize : ∀ j, 1 ≤ sizes j) (A : GroupedRealAlgorithm sizes)
    (p : ℝ) (hp : (groupedOrderBound sizes : ℝ) < p) :
    ¬ AnalyticUniversalLocalOrder A.run p := by
  sorry

theorem simultaneous_entire_counterexample {n : ℕ} (hn : 1 ≤ n)
    (A : RealAlgorithm n) :
    SimultaneousEntireCounterexample A.run (orderBound n : ℝ) := by
  sorry

end KungTraub

open Filter
open scoped Topology

namespace KungTraubAppendices

theorem complex_entire_counterexample {n : ℕ} (hn : 1 ≤ n)
    (A : ComplexAlgorithm n) (p : ℝ) (hp : (KungTraub.orderBound n : ℝ) < p) :
    ComplexEntireCounterexample A.run p := by
  sorry

theorem no_complex_universal_order_above {n : ℕ} (hn : 1 ≤ n)
    (A : ComplexAlgorithm n) (p : ℝ) (hp : (KungTraub.orderBound n : ℝ) < p) :
    ¬ ComplexUniversalLocalOrder A p := by
  sorry

theorem inverseHermite_universal_local_order (n : ℕ) (hn : 2 ≤ n) :
    RealIntervalUniversalLocalOrder (inverseHermiteAlgorithm n)
      (KungTraub.orderBound n : ℝ) := by
  sorry

theorem inverseHermite_exp_asymptotic (n : ℕ) (hn : 2 ≤ n) :
    Tendsto (fun x : ℝ =>
      (inverseHermiteAlgorithm n).run (fun t => Real.exp t - 1) x /
        x ^ KungTraub.orderBound n)
      (𝓝[≠] (0 : ℝ)) (𝓝 (sharpnessCoefficient (n - 1))) := by
  sorry

theorem inverseHermite_not_local_order_exp (n : ℕ) (hn : 2 ≤ n)
    (p : ℝ) (hp : (KungTraub.orderBound n : ℝ) < p) :
    ¬ KungTraub.LocalOrderAt (inverseHermiteAlgorithm n).run
      (fun t => Real.exp t - 1) 0 p := by
  sorry

end KungTraubAppendices
