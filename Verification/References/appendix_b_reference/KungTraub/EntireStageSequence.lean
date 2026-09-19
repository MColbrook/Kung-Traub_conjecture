import appendix_b_reference.KungTraub.EntireStageConstruction
import appendix_b_reference.KungTraub.QueryHistories
import appendix_b_reference.KungTraub.BudgetExtension

/-!
# Recursive construction of the Gaussian stages

The discrete induction in Section 4 of Matthew J. Colbrook's manuscript. Finite histories retain actual executions and exact old
derivatives. The correction multiplier is absorbed into its real polynomial,
so the final Gaussian scale sequence is identically one.
-/

noncomputable section
open scoped BigOperators

namespace KungTraub

structure GaussianStageEntry where
  polynomial : Polynomial ℝ
  epsilon : ℝ
  start : ℝ
  root : ℝ
  coefficient : ℝ
  deriving Inhabited

def gaussianHistoryFunction (e : ℕ → GaussianStageEntry) (s : ℕ) : ℝ → ℝ :=
  gaussianRealStage (fun i => (e i).polynomial) (fun _ => 1) s

def gaussianHistoryOutput {n : ℕ} (A : RealAlgorithm n) (e : ℕ → GaussianStageEntry)
    (s : ℕ) : ℝ := A.run (gaussianHistoryFunction e (s + 1)) (e s).start

theorem gaussianHistoryFunction_congr {e e' : ℕ → GaussianStageEntry} {s : ℕ}
    (h : ∀ i < s, (e i).polynomial = (e' i).polynomial) :
    gaussianHistoryFunction e s = gaussianHistoryFunction e' s := by
  sorry

theorem gaussianHistoryFunction_update_prefix (e : ℕ → GaussianStageEntry)
    (s : ℕ) (entry : GaussianStageEntry) (N : ℕ) (hN : N ≤ s) :
    gaussianHistoryFunction (Function.update e s entry) N = gaussianHistoryFunction e N := by
  sorry

theorem gaussianHistoryFunction_update_succ (e : ℕ → GaussianStageEntry)
    (s : ℕ) (entry : GaussianStageEntry) :
    gaussianHistoryFunction (Function.update e s entry) (s + 1) =
      fun t => gaussianHistoryFunction e s t + gaussianPolynomial entry.polynomial t := by
  sorry

theorem gaussianHistoryFunction_eq_base (e : ℕ → GaussianStageEntry) (s : ℕ) :
    gaussianHistoryFunction e s =
      fun t => t + gaussianPolynomial (∑ i ∈ Finset.range s, (e i).polynomial) t := by
  sorry

/-- A one-step extension property with exponent B, for the scalar and grouped constructions. -/
def GaussianStageExtensionAvailable {n : ℕ} (A : RealAlgorithm n) (B : ℝ)
    (exponent : ℕ → ℝ) : Prop :=
  ∀ (s : ℕ) (P : Polynomial ℝ) (Z : Finset ℝ) (orders : ℝ → ℕ) (a b : ℝ),
    (∀ t : ℝ, |(t + gaussianPolynomial P t) - t| ≤ 1 / 16 ∧
      (15 : ℝ) / 16 ≤ deriv (fun y => y + gaussianPolynomial P y) t ∧
      deriv (fun y => y + gaussianPolynomial P y) t ≤ 17 / 16) →
    |a| ≤ 1 / 4 → a + gaussianPolynomial P a = 0 →
    (∀ z ∈ Z, z + gaussianPolynomial P z ≠ 0) → 0 < b → b ≤ 1 / 16 →
    Nonempty (GaussianStageChoice A P Z orders a b ((s : ℝ) + 3) B (exponent s) s)

theorem scalar_gaussianStageExtensionAvailable {n : ℕ} (A : RealAlgorithm n)
    (hn : 0 < n) (exponent : ℕ → ℝ) (hp : ∀ s, (orderBound n : ℝ) < exponent s) :
    GaussianStageExtensionAvailable A (orderBound n : ℝ) exponent := by
  sorry

/-- Every invariant concerns a completed finite history. The budget has a positive
geometric continuation, while the unchosen polynomial corrections are zero. -/
structure GaussianHistory {n : ℕ} (A : RealAlgorithm n) (B : ℝ)
    (exponent : ℕ → ℝ) (s : ℕ) where
  entry : ℕ → GaussianStageEntry
  budget : ℕ → ℝ
  bounds : GaussianStageBounds (fun i => (entry i).polynomial) (fun _ => 1) budget
  tail_zero : ∀ i, s ≤ i → (entry i).polynomial = 0
  epsilon_pos : ∀ i < s, 0 < (entry i).epsilon
  epsilon_cap : ∀ i : ℕ, i < s → (entry i).epsilon < 1 / ((i : ℝ) + 1)
  epsilon_quarter : ∀ i < s, (entry i).epsilon < 1 / 4
  coefficient_pos : ∀ i < s, 0 < (entry i).coefficient
  is_root : ∀ i < s, gaussianHistoryFunction entry (i + 1) (entry i).root = 0
  start_lower : ∀ i < s, (3 / 4 : ℝ) * (entry i).epsilon ≤ (entry i).start - (entry i).root
  start_upper : ∀ i < s, (entry i).start - (entry i).root ≤ (5 / 4 : ℝ) * (entry i).epsilon
  error_bound : ∀ i < s, (entry i).coefficient * (entry i).epsilon ^ B ≤
    |gaussianHistoryOutput A entry i - (entry i).root|
  amplification : ∀ i : ℕ, i < s → ((i : ℝ) + 1) * (2 * (entry i).epsilon) ^ exponent i ≤
    ((entry i).coefficient / 2) * (entry i).epsilon ^ B
  next_budget_error : ∀ i < s, budget (i + 1) ≤
    |gaussianHistoryOutput A entry i - (entry i).root| / 32
  next_budget_scale : ∀ i < s, budget (i + 1) ≤ (entry i).epsilon / 32
  old_jets : ∀ i < s, ∀ (j : Fin n) z k,
    A.actualQuery (gaussianHistoryFunction entry (i + 1)) (entry i).start j = .derivative z k →
    iteratedDeriv k (gaussianHistoryFunction entry s) z =
      iteratedDeriv k (gaussianHistoryFunction entry (i + 1)) z
  old_values : ∀ i < s, ∀ (j : Fin n) z k,
    A.actualQuery (gaussianHistoryFunction entry (i + 1)) (entry i).start j = .derivative z k →
    gaussianHistoryFunction entry s z ≠ 0

def GaussianHistory.Extends {n : ℕ} {A : RealAlgorithm n} {B : ℝ}
    {exponent : ℕ → ℝ} {s : ℕ} (H : GaussianHistory A B exponent s)
    (H' : GaussianHistory A B exponent (s + 1)) : Prop :=
  (∀ i < s, H'.entry i = H.entry i) ∧ ∀ i ≤ s, H'.budget i = H.budget i

theorem initialGaussianHistory_bounds :
    GaussianStageBounds (fun _ : ℕ => (0 : Polynomial ℝ)) (fun _ => 1)
      (fun i => (1 / 32 : ℝ) * (1 / 2) ^ i) := by
  sorry

theorem initialGaussianHistory_vacuous {P : ℕ → Prop} : ∀ i < 0, P i := by
  sorry

def initialGaussianHistory {n : ℕ} (A : RealAlgorithm n) (B : ℝ) (exponent : ℕ → ℝ) :
    GaussianHistory A B exponent 0 :=
  {
    entry := fun _ => ⟨0, 0, 0, 0, 0⟩
    budget := fun i => (1 / 32 : ℝ) * (1 / 2) ^ i
    bounds := initialGaussianHistory_bounds
    tail_zero := fun _ _ => rfl
    epsilon_pos := initialGaussianHistory_vacuous
    epsilon_cap := initialGaussianHistory_vacuous
    epsilon_quarter := initialGaussianHistory_vacuous
    coefficient_pos := initialGaussianHistory_vacuous
    is_root := initialGaussianHistory_vacuous
    start_lower := initialGaussianHistory_vacuous
    start_upper := initialGaussianHistory_vacuous
    error_bound := initialGaussianHistory_vacuous
    amplification := initialGaussianHistory_vacuous
    next_budget_error := initialGaussianHistory_vacuous
    next_budget_scale := initialGaussianHistory_vacuous
    old_jets := initialGaussianHistory_vacuous
    old_values := initialGaussianHistory_vacuous
  }

theorem GaussianHistory.current_budget_small {n : ℕ} {A : RealAlgorithm n} {B : ℝ}
    {exponent : ℕ → ℝ} {s : ℕ} (H : GaussianHistory A B exponent s) : H.budget s ≤ 1 / 16 := by
  sorry

theorem GaussianHistory.current_root {n : ℕ} {A : RealAlgorithm n} {B : ℝ}
    {exponent : ℕ → ℝ} {s : ℕ} (H : GaussianHistory A B exponent s) :
    ∃ a : ℝ, gaussianHistoryFunction H.entry s a = 0 ∧ |a| ≤ 1 / 4 := by
  sorry

theorem GaussianHistory.history_nodes_nonzero {n : ℕ} {A : RealAlgorithm n} {B : ℝ}
    {exponent : ℕ → ℝ} {s : ℕ} (H : GaussianHistory A B exponent s) :
    ∀ z ∈ queryNodes (A.queryHistory (fun i => gaussianHistoryFunction H.entry (i + 1))
      (fun i => (H.entry i).start) s), gaussianHistoryFunction H.entry s z ≠ 0 := by
  sorry

theorem GaussianHistory.update_bounds {n : ℕ} {A : RealAlgorithm n} {B : ℝ}
    {exponent : ℕ → ℝ} {s : ℕ} (H : GaussianHistory A B exponent s)
    (entry : GaussianStageEntry) {next : ℝ} (hnext : 0 < next) (hhalf : next ≤ H.budget s / 2)
    (hvalue : ∀ t, |gaussianPolynomial entry.polynomial t| ≤ H.budget s)
    (hderiv : ∀ t, |deriv (gaussianPolynomial entry.polynomial) t| ≤ H.budget s)
    (hdisc : ∀ z : ℂ, ‖z‖ ≤ (s : ℝ) + 3 →
      ‖complexGaussianPolynomial entry.polynomial z‖ ≤ H.budget s) :
    GaussianStageBounds (fun i => ((Function.update H.entry s entry) i).polynomial)
      (fun _ => 1) (extendBudget H.budget s next) := by
  sorry

/-- Every valid finite history has an extension preserving all previous stages.
The finite adversary supplies the one-step extension property. -/
theorem GaussianHistory.exists_extension {n : ℕ} {A : RealAlgorithm n} {B : ℝ}
    {exponent : ℕ → ℝ} (available : GaussianStageExtensionAvailable A B exponent)
    {s : ℕ} (H : GaussianHistory A B exponent s) :
    ∃ H' : GaussianHistory A B exponent (s + 1), H.Extends H' := by
  sorry

def gaussianHistoryChain {n : ℕ} {A : RealAlgorithm n} {B : ℝ} {exponent : ℕ → ℝ}
    (available : GaussianStageExtensionAvailable A B exponent) :
    (s : ℕ) → GaussianHistory A B exponent s
  | 0 => initialGaussianHistory A B exponent
  | s + 1 => Classical.choose (GaussianHistory.exists_extension available (gaussianHistoryChain available s))

theorem gaussianHistoryChain_extends {n : ℕ} {A : RealAlgorithm n} {B : ℝ} {exponent : ℕ → ℝ}
    (available : GaussianStageExtensionAvailable A B exponent) (s : ℕ) :
    (gaussianHistoryChain available s).Extends (gaussianHistoryChain available (s + 1)) := by
  sorry

theorem gaussianHistoryChain_entry_stable {n : ℕ} {A : RealAlgorithm n} {B : ℝ}
    {exponent : ℕ → ℝ} (available : GaussianStageExtensionAvailable A B exponent)
    {i N M : ℕ} (hi : i < N) (hNM : N ≤ M) :
    (gaussianHistoryChain available M).entry i = (gaussianHistoryChain available N).entry i := by
  sorry

theorem gaussianHistoryChain_budget_stable {n : ℕ} {A : RealAlgorithm n} {B : ℝ}
    {exponent : ℕ → ℝ} (available : GaussianStageExtensionAvailable A B exponent)
    {i N M : ℕ} (hi : i ≤ N) (hNM : N ≤ M) :
    (gaussianHistoryChain available M).budget i = (gaussianHistoryChain available N).budget i := by
  sorry

def chosenGaussianEntry {n : ℕ} {A : RealAlgorithm n} {B : ℝ} {exponent : ℕ → ℝ}
    (available : GaussianStageExtensionAvailable A B exponent) (i : ℕ) : GaussianStageEntry :=
  (gaussianHistoryChain available (i + 1)).entry i

def chosenGaussianBudget {n : ℕ} {A : RealAlgorithm n} {B : ℝ} {exponent : ℕ → ℝ}
    (available : GaussianStageExtensionAvailable A B exponent) (i : ℕ) : ℝ :=
  (gaussianHistoryChain available i).budget i

theorem chosenGaussianEntry_prefix {n : ℕ} {A : RealAlgorithm n} {B : ℝ}
    {exponent : ℕ → ℝ} (available : GaussianStageExtensionAvailable A B exponent)
    {i N : ℕ} (hi : i < N) :
    chosenGaussianEntry available i = (gaussianHistoryChain available N).entry i := by
  sorry

theorem chosenGaussianBudget_prefix {n : ℕ} {A : RealAlgorithm n} {B : ℝ}
    {exponent : ℕ → ℝ} (available : GaussianStageExtensionAvailable A B exponent)
    {i N : ℕ} (hi : i ≤ N) :
    chosenGaussianBudget available i = (gaussianHistoryChain available N).budget i := by
  sorry

theorem chosenGaussianFunction_prefix {n : ℕ} {A : RealAlgorithm n} {B : ℝ}
    {exponent : ℕ → ℝ} (available : GaussianStageExtensionAvailable A B exponent)
    {N M : ℕ} (hNM : N ≤ M) :
    gaussianHistoryFunction (chosenGaussianEntry available) N =
      gaussianHistoryFunction (gaussianHistoryChain available M).entry N := by
  sorry

theorem chosenGaussianOutput_prefix {n : ℕ} {A : RealAlgorithm n} {B : ℝ}
    {exponent : ℕ → ℝ} (available : GaussianStageExtensionAvailable A B exponent)
    {i M : ℕ} (hi : i < M) :
    gaussianHistoryOutput A (chosenGaussianEntry available) i =
      gaussianHistoryOutput A (gaussianHistoryChain available M).entry i := by
  sorry

/-- Compatible finite histories determine an infinite sequence of stages. -/
theorem exists_gaussianAdversarialStages_of_extension {n : ℕ} {A : RealAlgorithm n} {B : ℝ}
    {exponent : ℕ → ℝ} (available : GaussianStageExtensionAvailable A B exponent) :
    Nonempty (GaussianAdversarialStages A B exponent) := by
  sorry

/-- Actual scalar stages are constructed for any sequence of exponents above B_n. -/
theorem exists_scalar_gaussianAdversarialStages {n : ℕ} (A : RealAlgorithm n) (hn : 0 < n)
    (exponent : ℕ → ℝ) (hp : ∀ s, (orderBound n : ℝ) < exponent s) :
    Nonempty (GaussianAdversarialStages A (orderBound n : ℝ) exponent) := by
  sorry

/-- The scalar entire counterexample. -/
theorem scalar_entireCounterexample_constructed {n : ℕ} (A : RealAlgorithm n) (hn : 0 < n)
    (p : ℝ) (hp : (orderBound n : ℝ) < p) : EntireCounterexample A.run p := by
  sorry

/-- One constructed entire function and one sequence defeat every larger scalar order. -/
theorem scalar_simultaneousEntireCounterexample_constructed {n : ℕ} (A : RealAlgorithm n)
    (hn : 0 < n) : SimultaneousEntireCounterexample A.run (orderBound n : ℝ) := by
  sorry

end KungTraub
