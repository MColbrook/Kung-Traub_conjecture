import appendix_b_reference.KungTraubAppendices.ComplexPolynomialStage
import appendix_b_reference.KungTraubAppendices.ComplexWitnessAssembly
import appendix_b_reference.KungTraub.BudgetExtension

/-!
# The complex polynomial stage sequence

The recursion follows `KungTraub.EntireStageSequence`. A finite history contains
the completed polynomial inputs, starts, roots and outputs. The budget has a
positive geometric continuation, with the next allowance included before
choosing the next stage. Corrections preserve all saved complex derivative
jets, including those at exterior nodes.

The finite adversary extends each history, giving the stage sequence and its
entire counterexample.
-/

noncomputable section
open KungTraub
open scoped BigOperators

namespace KungTraubAppendices

structure ComplexStageEntry where
  polynomial : Polynomial ℂ
  epsilon : ℝ
  start : ℂ
  root : ℂ
  coefficient : ℝ
  deriving Inhabited

def complexHistoryFunction (e : ℕ → ComplexStageEntry) (s : ℕ) : ℂ → ℂ :=
  complexPolynomialStage (fun i => (e i).polynomial) s

def complexHistoryOutput {n : ℕ} (A : ComplexAlgorithm n) (e : ℕ → ComplexStageEntry)
    (s : ℕ) : ℂ := A.run (complexHistoryFunction e (s + 1)) (e s).start

theorem complexHistoryFunction_congr {e e' : ℕ → ComplexStageEntry} {s : ℕ}
    (h : ∀ i < s, (e i).polynomial = (e' i).polynomial) :
    complexHistoryFunction e s = complexHistoryFunction e' s := by
  sorry

theorem complexHistoryFunction_update_prefix (e : ℕ → ComplexStageEntry)
    (s : ℕ) (entry : ComplexStageEntry) (N : ℕ) (hN : N ≤ s) :
    complexHistoryFunction (Function.update e s entry) N = complexHistoryFunction e N := by
  sorry

theorem complexHistoryFunction_update_succ (e : ℕ → ComplexStageEntry)
    (s : ℕ) (entry : ComplexStageEntry) :
    complexHistoryFunction (Function.update e s entry) (s + 1) =
      fun z => complexHistoryFunction e s z + entry.polynomial.eval z := by
  sorry

theorem complexHistoryFunction_eq_eval (e : ℕ → ComplexStageEntry) (s : ℕ) :
    complexHistoryFunction e s =
      fun z => (Polynomial.X + ∑ i ∈ Finset.range s, (e i).polynomial).eval z := by
  sorry

/-- The extension property used in the discrete recursion. -/
def ComplexStageExtensionAvailable {n : ℕ} (A : ComplexAlgorithm n) (B p : ℝ) : Prop :=
  ∀ (s : ℕ) (f : Polynomial ℂ) (Q : Finset ComplexQuery) (a : ℂ) (b L : ℝ),
    (∀ z : ℂ, ‖z‖ ≤ 1 → ‖f.eval z - z‖ ≤ L ∧ ‖f.derivative.eval z - 1‖ ≤ L) →
    ‖a‖ ≤ 1 / 16 → f.eval a = 0 →
    (∀ z ∈ complexQueryNodes Q, ‖z‖ ≤ 1 → f.eval z ≠ 0) →
    0 < b → b ≤ 1 / 32 → L + b ≤ 1 / 16 →
    Nonempty (ComplexPolynomialStageChoice A f Q a b ((s : ℝ) + 3) B p s)

theorem complex_scalarStageExtensionAvailable {n : ℕ} (A : ComplexAlgorithm n)
    (hn : 0 < n) (p : ℝ) (hp : (orderBound n : ℝ) < p) :
    ComplexStageExtensionAvailable A (orderBound n : ℝ) p := by
  sorry

/-- Only finite data and their proved invariants are stored. The correction at
index i is the paper's positive stage i+1. -/
structure ComplexHistory {n : ℕ} (A : ComplexAlgorithm n) (B p : ℝ) (s : ℕ) where
  entry : ℕ → ComplexStageEntry
  budget : ℕ → ℝ
  bounds : ComplexPolynomialStageBounds (fun i => (entry i).polynomial) budget
  tail_zero : ∀ i, s ≤ i → (entry i).polynomial = 0
  epsilon_pos : ∀ i < s, 0 < (entry i).epsilon
  epsilon_cap : ∀ i : ℕ, i < s → (entry i).epsilon < 1 / ((i : ℝ) + 1)
  coefficient_pos : ∀ i < s, 0 < (entry i).coefficient
  root_norm : ∀ i < s, ‖(entry i).root‖ ≤ 1 / 16
  is_root : ∀ i < s, complexHistoryFunction entry (i + 1) (entry i).root = 0
  start_lower : ∀ i < s, (3 / 4 : ℝ) * (entry i).epsilon ≤ ‖(entry i).start - (entry i).root‖
  start_upper : ∀ i < s, ‖(entry i).start - (entry i).root‖ ≤ (5 / 4 : ℝ) * (entry i).epsilon
  error_bound : ∀ i < s, (entry i).coefficient * (entry i).epsilon ^ B ≤
    ‖complexHistoryOutput A entry i - (entry i).root‖
  amplification : ∀ i : ℕ, i < s → ((i : ℝ) + 1) * (2 * (entry i).epsilon) ^ p ≤
    ((entry i).coefficient / 2) * (entry i).epsilon ^ B
  next_budget_error : ∀ i < s, budget (i + 1) ≤
    ‖complexHistoryOutput A entry i - (entry i).root‖ / 32
  next_budget_scale : ∀ i < s, budget (i + 1) ≤ (entry i).epsilon / 32
  old_jets : ∀ i < s, ∀ (j : Fin n) z k,
    A.actualQuery (complexHistoryFunction entry (i + 1)) (entry i).start j = .derivative z k →
    iteratedDeriv k (complexHistoryFunction entry s) z =
      iteratedDeriv k (complexHistoryFunction entry (i + 1)) z
  old_values : ∀ i < s, ∀ (j : Fin n) z k,
    A.actualQuery (complexHistoryFunction entry (i + 1)) (entry i).start j = .derivative z k →
    ‖z‖ ≤ 1 → complexHistoryFunction entry s z ≠ 0

def ComplexHistory.Extends {n : ℕ} {A : ComplexAlgorithm n} {B p : ℝ} {s : ℕ}
    (H : ComplexHistory A B p s) (H' : ComplexHistory A B p (s + 1)) : Prop :=
  (∀ i < s, H'.entry i = H.entry i) ∧ ∀ i ≤ s, H'.budget i = H.budget i

/-- The empty history satisfies the initial stage conditions. -/
theorem initialComplexHistory_bounds :
    ComplexPolynomialStageBounds (fun _ : ℕ => (0 : Polynomial ℂ))
      (fun i => (1 / 32 : ℝ) * (1 / 2) ^ i) := by
  sorry

theorem initialComplexHistory_vacuous {P : ℕ → Prop} : ∀ i < 0, P i := by
  sorry

def initialComplexHistory {n : ℕ} (A : ComplexAlgorithm n) (B p : ℝ) : ComplexHistory A B p 0 :=
  {
    entry := fun _ => ⟨0, 0, 0, 0, 0⟩
    budget := fun i => (1 / 32 : ℝ) * (1 / 2) ^ i
    bounds := initialComplexHistory_bounds
    tail_zero := fun _ _ => rfl
    epsilon_pos := initialComplexHistory_vacuous
    epsilon_cap := initialComplexHistory_vacuous
    coefficient_pos := initialComplexHistory_vacuous
    root_norm := initialComplexHistory_vacuous
    is_root := initialComplexHistory_vacuous
    start_lower := initialComplexHistory_vacuous
    start_upper := initialComplexHistory_vacuous
    error_bound := initialComplexHistory_vacuous
    amplification := initialComplexHistory_vacuous
    next_budget_error := initialComplexHistory_vacuous
    next_budget_scale := initialComplexHistory_vacuous
    old_jets := initialComplexHistory_vacuous
    old_values := initialComplexHistory_vacuous
  }

theorem ComplexHistory.current_budget_small {n : ℕ} {A : ComplexAlgorithm n} {B p : ℝ}
    {s : ℕ} (H : ComplexHistory A B p s) : H.budget s ≤ 1 / 32 := by
  sorry

/-- The next allowance is included in the finite budget before invoking the
concrete root-family theorem. This supplies actual additive headroom. -/
theorem ComplexHistory.budget_headroom {n : ℕ} {A : ComplexAlgorithm n} {B p : ℝ}
    {s : ℕ} (H : ComplexHistory A B p s) :
    (∑ i ∈ Finset.range s, H.budget i) + H.budget s ≤ (1 / 16 : ℝ) := by
  sorry

theorem ComplexHistory.partial_bounds {n : ℕ} {A : ComplexAlgorithm n} {B p : ℝ}
    {s : ℕ} (H : ComplexHistory A B p s) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖complexHistoryFunction H.entry s z - z‖ ≤ ∑ i ∈ Finset.range s, H.budget i ∧
      ‖deriv (complexHistoryFunction H.entry s) z - 1‖ ≤ ∑ i ∈ Finset.range s, H.budget i := by
  sorry

theorem ComplexHistory.current_root {n : ℕ} {A : ComplexAlgorithm n} {B p : ℝ}
    {s : ℕ} (H : ComplexHistory A B p s) :
    ∃ a : ℂ, complexHistoryFunction H.entry s a = 0 ∧ ‖a‖ ≤ (1 / 16 : ℝ) := by
  sorry

theorem ComplexHistory.history_nodes_nonzero {n : ℕ} {A : ComplexAlgorithm n} {B p : ℝ}
    {s : ℕ} (H : ComplexHistory A B p s) :
    ∀ z ∈ complexQueryNodes (A.queryHistory (fun i => complexHistoryFunction H.entry (i + 1))
      (fun i => (H.entry i).start) s), ‖z‖ ≤ 1 → complexHistoryFunction H.entry s z ≠ 0 := by
  sorry

theorem ComplexHistory.update_bounds {n : ℕ} {A : ComplexAlgorithm n} {B p : ℝ}
    {s : ℕ} (H : ComplexHistory A B p s) (entry : ComplexStageEntry)
    {next : ℝ} (hnext : 0 < next) (hhalf : next ≤ H.budget s / 2)
    (hdisc : ∀ z : ℂ, ‖z‖ ≤ (s : ℝ) + 3 → ‖entry.polynomial.eval z‖ ≤ H.budget s)
    (hderiv : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖entry.polynomial.derivative.eval z‖ ≤ H.budget s) :
    ComplexPolynomialStageBounds (fun i => ((Function.update H.entry s entry) i).polynomial)
      (extendBudget H.budget s next) := by
  sorry

/-- A finite history extends by one stage. Every old completed input,
start and output stays identical and the whole old budget prefix stays fixed. -/
theorem ComplexHistory.exists_extension {n : ℕ} {A : ComplexAlgorithm n} {B p : ℝ}
    (available : ComplexStageExtensionAvailable A B p) {s : ℕ} (H : ComplexHistory A B p s) :
    ∃ H' : ComplexHistory A B p (s + 1), H.Extends H' := by
  sorry

def complexHistoryChain {n : ℕ} {A : ComplexAlgorithm n} {B p : ℝ}
    (available : ComplexStageExtensionAvailable A B p) : (s : ℕ) → ComplexHistory A B p s
  | 0 => initialComplexHistory A B p
  | s + 1 => Classical.choose (ComplexHistory.exists_extension available (complexHistoryChain available s))

theorem complexHistoryChain_extends {n : ℕ} {A : ComplexAlgorithm n} {B p : ℝ}
    (available : ComplexStageExtensionAvailable A B p) (s : ℕ) :
    (complexHistoryChain available s).Extends (complexHistoryChain available (s + 1)) := by
  sorry

theorem complexHistoryChain_entry_stable {n : ℕ} {A : ComplexAlgorithm n} {B p : ℝ}
    (available : ComplexStageExtensionAvailable A B p) {i N M : ℕ} (hi : i < N) (hNM : N ≤ M) :
    (complexHistoryChain available M).entry i = (complexHistoryChain available N).entry i := by
  sorry

theorem complexHistoryChain_budget_stable {n : ℕ} {A : ComplexAlgorithm n} {B p : ℝ}
    (available : ComplexStageExtensionAvailable A B p) {i N M : ℕ} (hi : i ≤ N) (hNM : N ≤ M) :
    (complexHistoryChain available M).budget i = (complexHistoryChain available N).budget i := by
  sorry

def chosenComplexEntry {n : ℕ} {A : ComplexAlgorithm n} {B p : ℝ}
    (available : ComplexStageExtensionAvailable A B p) (i : ℕ) : ComplexStageEntry :=
  (complexHistoryChain available (i + 1)).entry i

def chosenComplexBudget {n : ℕ} {A : ComplexAlgorithm n} {B p : ℝ}
    (available : ComplexStageExtensionAvailable A B p) (i : ℕ) : ℝ :=
  (complexHistoryChain available i).budget i

theorem chosenComplexEntry_prefix {n : ℕ} {A : ComplexAlgorithm n} {B p : ℝ}
    (available : ComplexStageExtensionAvailable A B p) {i N : ℕ} (hi : i < N) :
    chosenComplexEntry available i = (complexHistoryChain available N).entry i := by
  sorry

theorem chosenComplexBudget_prefix {n : ℕ} {A : ComplexAlgorithm n} {B p : ℝ}
    (available : ComplexStageExtensionAvailable A B p) {i N : ℕ} (hi : i ≤ N) :
    chosenComplexBudget available i = (complexHistoryChain available N).budget i := by
  sorry

theorem chosenComplexFunction_prefix {n : ℕ} {A : ComplexAlgorithm n} {B p : ℝ}
    (available : ComplexStageExtensionAvailable A B p) {N M : ℕ} (hNM : N ≤ M) :
    complexHistoryFunction (chosenComplexEntry available) N =
      complexHistoryFunction (complexHistoryChain available M).entry N := by
  sorry

theorem chosenComplexOutput_prefix {n : ℕ} {A : ComplexAlgorithm n} {B p : ℝ}
    (available : ComplexStageExtensionAvailable A B p) {i M : ℕ} (hi : i < M) :
    complexHistoryOutput A (chosenComplexEntry available) i =
      complexHistoryOutput A (complexHistoryChain available M).entry i := by
  sorry

/-- Compatible finite histories construct all infinite stage data, including
exact persistence of every saved derivative at every later finite stage. -/
theorem exists_complexAdversarialStages_of_extension {n : ℕ} {A : ComplexAlgorithm n} {B p : ℝ}
    (available : ComplexStageExtensionAvailable A B p) : Nonempty (ComplexAdversarialStages A B p) := by
  sorry

/-- The exact scalar complex finite adversary constructs the stage sequence. -/
theorem exists_complexAdversarialStages {n : ℕ} (A : ComplexAlgorithm n) (hn : 0 < n)
    (p : ℝ) (hp : (orderBound n : ℝ) < p) :
    Nonempty (ComplexAdversarialStages A (orderBound n : ℝ) p) := by
  sorry

/-- The stage sequence gives the entire counterexample of Appendix B. -/
theorem complex_entireCounterexample_constructed {n : ℕ} (A : ComplexAlgorithm n)
    (hn : 0 < n) (p : ℝ) (hp : (orderBound n : ℝ) < p) :
    ComplexEntireCounterexample A.run p := by
  sorry

end KungTraubAppendices
