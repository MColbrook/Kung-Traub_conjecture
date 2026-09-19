import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Scalar observation models and local-order statements

The real oracle returns one derivative value at each query. Its decision rules are arbitrary
functions of the initial point and earlier scalar answers; they have no access to the input
function itself. A second model chooses all queries in each prescribed group before receiving
any answer from that group.

The input class used for the primary local-order statements consists of entire functions that
are real on the real axis. The corresponding whole-line real-analytic property is also defined
to state the consequence for the broader class. Counterexample predicates retain global real
derivative bounds, uniqueness of the real zero, and divergence along independent starting points.

Source: Matthew J. Colbrook, *Adversarial Wronskians: A proof of the Kung–Traub conjecture*,
Sections 1 and 4.
-/

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
