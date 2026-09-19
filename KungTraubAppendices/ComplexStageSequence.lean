import KungTraubAppendices.ComplexPolynomialStage
import KungTraubAppendices.ComplexWitnessAssembly
import KungTraub.BudgetExtension

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
  funext z
  simp only [complexHistoryFunction, complexPolynomialStage]
  congr 1
  exact Finset.sum_congr rfl (fun i hi => congrArg (fun P : Polynomial ℂ => P.eval z)
    (h i (Finset.mem_range.mp hi)))

theorem complexHistoryFunction_update_prefix (e : ℕ → ComplexStageEntry)
    (s : ℕ) (entry : ComplexStageEntry) (N : ℕ) (hN : N ≤ s) :
    complexHistoryFunction (Function.update e s entry) N = complexHistoryFunction e N := by
  apply complexHistoryFunction_congr
  intro i hi
  rw [Function.update_of_ne (by omega : i ≠ s)]

theorem complexHistoryFunction_update_succ (e : ℕ → ComplexStageEntry)
    (s : ℕ) (entry : ComplexStageEntry) :
    complexHistoryFunction (Function.update e s entry) (s + 1) =
      fun z => complexHistoryFunction e s z + entry.polynomial.eval z := by
  funext z
  have hp := congrFun (complexHistoryFunction_update_prefix e s entry s le_rfl) z
  simp only [complexHistoryFunction, complexPolynomialStage] at hp ⊢
  rw [Finset.sum_range_succ, ← add_assoc, hp, Function.update_self]

theorem complexHistoryFunction_eq_eval (e : ℕ → ComplexStageEntry) (s : ℕ) :
    complexHistoryFunction e s =
      fun z => (Polynomial.X + ∑ i ∈ Finset.range s, (e i).polynomial).eval z :=
  complexPolynomialStage_eq_eval _ s

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
  intro s f Q a b L hf ha hroot hold hb hbsmall hbudget
  exact exists_complexPolynomialStageChoice A hn f Q hf ha hroot hold hb hbsmall hbudget
    (by have := Nat.cast_nonneg (α := ℝ) s; linarith) hp s

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
  refine {
    budget_pos := fun i => by positivity
    budget_half := ?_
    budget_first := by norm_num
    disc_bound := ?_
    deriv_bound := ?_
  }
  · intro i
    rw [pow_succ]
    exact le_of_eq (by ring)
  · intro i z _
    simp
  · intro i z _
    simp

theorem initialComplexHistory_vacuous {P : ℕ → Prop} : ∀ i < 0, P i :=
  fun i hi => False.elim (Nat.not_lt_zero i hi)

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
  have hp : (1 / 2 : ℝ) ^ s ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  calc
    H.budget s ≤ H.budget 0 * (1 / 2 : ℝ) ^ s := budget_le_geometric H.bounds.budget_half s
    _ ≤ H.budget 0 * 1 := mul_le_mul_of_nonneg_left hp (H.bounds.budget_pos 0).le
    _ ≤ 1 / 32 := by simpa using H.bounds.budget_first

/-- The next allowance is included in the finite budget before invoking the
concrete root-family theorem. This supplies actual additive headroom. -/
theorem ComplexHistory.budget_headroom {n : ℕ} {A : ComplexAlgorithm n} {B p : ℝ}
    {s : ℕ} (H : ComplexHistory A B p s) :
    (∑ i ∈ Finset.range s, H.budget i) + H.budget s ≤ (1 / 16 : ℝ) := by
  simpa only [Finset.sum_range_succ] using H.bounds.partial_budget (s + 1)

theorem ComplexHistory.partial_bounds {n : ℕ} {A : ComplexAlgorithm n} {B p : ℝ}
    {s : ℕ} (H : ComplexHistory A B p s) (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖complexHistoryFunction H.entry s z - z‖ ≤ ∑ i ∈ Finset.range s, H.budget i ∧
      ‖deriv (complexHistoryFunction H.entry s) z - 1‖ ≤ ∑ i ∈ Finset.range s, H.budget i := by
  constructor
  · simp only [complexHistoryFunction, complexPolynomialStage, add_sub_cancel_left]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => H.bounds.value_bound i z hz))
  · rw [complexHistoryFunction, complexPolynomialStage_deriv, add_sub_cancel_left]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => H.bounds.deriv_bound i z hz))

theorem ComplexHistory.current_root {n : ℕ} {A : ComplexAlgorithm n} {B p : ℝ}
    {s : ℕ} (H : ComplexHistory A B p s) :
    ∃ a : ℂ, complexHistoryFunction H.entry s a = 0 ∧ ‖a‖ ≤ (1 / 16 : ℝ) := by
  obtain ⟨a, ha, hroot, _⟩ := exists_unique_simple_root_on_unit_disc
    (complexPolynomialStage_differentiable (fun i => (H.entry i).polynomial) s)
    (fun z hz => (H.bounds.finite_bounds s z hz).1)
    (fun z hz => (H.bounds.finite_bounds s z hz).2)
  exact ⟨a, hroot.1, ha⟩

theorem ComplexHistory.history_nodes_nonzero {n : ℕ} {A : ComplexAlgorithm n} {B p : ℝ}
    {s : ℕ} (H : ComplexHistory A B p s) :
    ∀ z ∈ complexQueryNodes (A.queryHistory (fun i => complexHistoryFunction H.entry (i + 1))
      (fun i => (H.entry i).start) s), ‖z‖ ≤ 1 → complexHistoryFunction H.entry s z ≠ 0 := by
  classical
  intro z hz hzone
  obtain ⟨k, hk⟩ := (mem_complexQueryNodes_iff _ z).mp hz
  obtain ⟨i, hi, hki⟩ := Finset.mem_biUnion.mp hk
  obtain ⟨j, _, hquery⟩ := Finset.mem_image.mp hki
  exact H.old_values i (Finset.mem_range.mp hi) j z k hquery hzone

theorem ComplexHistory.update_bounds {n : ℕ} {A : ComplexAlgorithm n} {B p : ℝ}
    {s : ℕ} (H : ComplexHistory A B p s) (entry : ComplexStageEntry)
    {next : ℝ} (hnext : 0 < next) (hhalf : next ≤ H.budget s / 2)
    (hdisc : ∀ z : ℂ, ‖z‖ ≤ (s : ℝ) + 3 → ‖entry.polynomial.eval z‖ ≤ H.budget s)
    (hderiv : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖entry.polynomial.derivative.eval z‖ ≤ H.budget s) :
    ComplexPolynomialStageBounds (fun i => ((Function.update H.entry s entry) i).polynomial)
      (extendBudget H.budget s next) := by
  have hfuture (i : ℕ) (hi : s < i) : ((Function.update H.entry s entry) i).polynomial = 0 := by
    rw [Function.update_of_ne (ne_of_gt hi), H.tail_zero i hi.le]
  refine {
    budget_pos := extendBudget_pos H.bounds.budget_pos hnext
    budget_half := extendBudget_half H.bounds.budget_half hhalf
    budget_first := extendBudget_initial_bound H.bounds.budget_first
    disc_bound := ?_
    deriv_bound := ?_
  }
  · intro i z hz
    rcases lt_trichotomy i s with hi | rfl | hi
    · rw [Function.update_of_ne (ne_of_lt hi), extendBudget_agrees next hi.le]
      exact H.bounds.disc_bound i z hz
    · simpa only [Function.update_self, extendBudget_agrees next le_rfl] using hdisc z hz
    · simpa [hfuture i hi] using (extendBudget_pos H.bounds.budget_pos hnext i).le
  · intro i z hz
    rcases lt_trichotomy i s with hi | rfl | hi
    · rw [Function.update_of_ne (ne_of_lt hi), extendBudget_agrees next hi.le]
      exact H.bounds.deriv_bound i z hz
    · simpa only [Function.update_self, extendBudget_agrees next le_rfl] using hderiv z hz
    · simpa [hfuture i hi] using (extendBudget_pos H.bounds.budget_pos hnext i).le

/-- A finite history extends by one stage. Every old completed input,
start and output stays identical and the whole old budget prefix stays fixed. -/
theorem ComplexHistory.exists_extension {n : ℕ} {A : ComplexAlgorithm n} {B p : ℝ}
    (available : ComplexStageExtensionAvailable A B p) {s : ℕ} (H : ComplexHistory A B p s) :
    ∃ H' : ComplexHistory A B p (s + 1), H.Extends H' := by
  classical
  let f := Polynomial.X + ∑ i ∈ Finset.range s, (H.entry i).polynomial
  let L := ∑ i ∈ Finset.range s, H.budget i
  have hbaseeq : complexHistoryFunction H.entry s = fun z => f.eval z :=
    complexHistoryFunction_eq_eval H.entry s
  have hbase : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖f.eval z - z‖ ≤ L ∧ ‖f.derivative.eval z - 1‖ ≤ L := by
    intro z hz
    have h := H.partial_bounds z hz
    rw [hbaseeq, f.deriv] at h
    exact h
  obtain ⟨a, hroot, ha⟩ := H.current_root
  let queries := A.queryHistory (fun i => complexHistoryFunction H.entry (i + 1))
    (fun i => (H.entry i).start) s
  have hold : ∀ z ∈ complexQueryNodes queries, ‖z‖ ≤ 1 → f.eval z ≠ 0 := by
    intro z hz hzone
    rw [← congrFun hbaseeq z]
    exact H.history_nodes_nonzero z hz hzone
  let G := Classical.choice (available s f queries a (H.budget s) L hbase ha
    (by simpa only [hbaseeq] using hroot) hold (H.bounds.budget_pos s)
    H.current_budget_small H.budget_headroom)
  obtain ⟨next, hnext, hnextHalf, hnextError, hnextScale⟩ :=
    G.exists_next_budget (H.bounds.budget_pos s)
  let entry : ComplexStageEntry := ⟨G.correction, G.epsilon, a + (G.epsilon : ℂ), G.root, G.coefficient⟩
  let e := Function.update H.entry s entry
  have heold (i : ℕ) (hi : i < s) : e i = H.entry i := Function.update_of_ne (ne_of_lt hi) _ _
  have hes : e s = entry := Function.update_self _ _ _
  have hfold (i : ℕ) (hi : i < s) :
      complexHistoryFunction e (i + 1) = complexHistoryFunction H.entry (i + 1) :=
    complexHistoryFunction_update_prefix H.entry s entry (i + 1) (by omega)
  have hyold (i : ℕ) (hi : i < s) : complexHistoryOutput A e i = complexHistoryOutput A H.entry i := by
    unfold complexHistoryOutput
    rw [hfold i hi, heold i hi]
  have hnew : complexHistoryFunction e (s + 1) = fun z => (f + G.correction).eval z := by
    rw [complexHistoryFunction_update_succ, hbaseeq]
    funext z
    simp only [Polynomial.eval_add, entry]
  have hynew : complexHistoryOutput A e s =
      A.run (fun z => (f + G.correction).eval z) (a + (G.epsilon : ℂ)) := by
    unfold complexHistoryOutput
    rw [hnew, hes]
  have hbounds : ComplexPolynomialStageBounds (fun i => (e i).polynomial)
      (extendBudget H.budget s next) := H.update_bounds entry hnext hnextHalf
    (fun z hz => (G.disc_bound.1 z hz).trans (by linarith [H.bounds.budget_pos s]))
    (fun z hz => (G.disc_bound.2 z hz).trans (by linarith [H.bounds.budget_pos s]))
  refine ⟨{
    entry := e
    budget := extendBudget H.budget s next
    bounds := hbounds
    tail_zero := ?_
    epsilon_pos := ?_
    epsilon_cap := ?_
    coefficient_pos := ?_
    root_norm := ?_
    is_root := ?_
    start_lower := ?_
    start_upper := ?_
    error_bound := ?_
    amplification := ?_
    next_budget_error := ?_
    next_budget_scale := ?_
    old_jets := ?_
    old_values := ?_
  }, ?_⟩
  · intro i hi
    change ((Function.update H.entry s entry) i).polynomial = 0
    rw [Function.update_of_ne (by omega : i ≠ s)]
    exact H.tail_zero i (by omega)
  · intro i hi
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | rfl
    · simpa only [heold i hi] using H.epsilon_pos i hi
    · simpa only [hes] using G.epsilon_pos
  · intro i hi
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | rfl
    · simpa only [heold i hi] using H.epsilon_cap i hi
    · simpa only [hes] using G.epsilon_cap
  · intro i hi
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | rfl
    · simpa only [heold i hi] using H.coefficient_pos i hi
    · simpa only [hes] using G.coefficient_pos
  · intro i hi
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | rfl
    · simpa only [heold i hi] using H.root_norm i hi
    · simpa only [hes] using G.root_bound
  · intro i hi
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | rfl
    · simpa only [heold i hi, hfold i hi] using H.is_root i hi
    · simpa only [hes, hnew] using G.simple_root.1
  · intro i hi
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | rfl
    · simpa only [heold i hi] using H.start_lower i hi
    · simpa only [hes] using G.start_lower
  · intro i hi
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | rfl
    · simpa only [heold i hi] using H.start_upper i hi
    · simpa only [hes] using G.start_upper
  · intro i hi
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | rfl
    · simpa only [heold i hi, hyold i hi] using H.error_bound i hi
    · simpa only [hes, hynew] using G.error_bound
  · intro i hi
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | rfl
    · simpa only [heold i hi] using H.amplification i hi
    · simpa only [hes] using G.amplification
  · intro i hi
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | rfl
    · rw [extendBudget_agrees next (by omega : i + 1 ≤ s)]
      simpa only [heold i hi, hyold i hi] using H.next_budget_error i hi
    · simpa only [extendBudget_next, hes, hynew] using hnextError
  · intro i hi
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | rfl
    · rw [extendBudget_agrees next (by omega : i + 1 ≤ s)]
      simpa only [heold i hi] using H.next_budget_scale i hi
    · simpa only [extendBudget_next, hes] using hnextScale
  · intro i hi j z k hquery
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | rfl
    · have hqueryold : A.actualQuery (complexHistoryFunction H.entry (i + 1))
          (H.entry i).start j = .derivative z k := by simpa only [heold i hi, hfold i hi] using hquery
      have hmem : ComplexQuery.derivative z k ∈ queries := by
        have h := A.mem_queryHistory (fun i => complexHistoryFunction H.entry (i + 1))
          (fun i => (H.entry i).start) hi j
        simpa only [hqueryold] using h
      calc
        iteratedDeriv k (complexHistoryFunction e (s + 1)) z =
            iteratedDeriv k (complexHistoryFunction H.entry s) z := by
          rw [hnew, G.old_jets z k hmem, ← hbaseeq]
        _ = iteratedDeriv k (complexHistoryFunction H.entry (i + 1)) z :=
          H.old_jets i hi j z k hqueryold
        _ = iteratedDeriv k (complexHistoryFunction e (i + 1)) z := by rw [hfold i hi]
    · rfl
  · intro i hi j z k hquery hzone
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | rfl
    · have hqueryold : A.actualQuery (complexHistoryFunction H.entry (i + 1))
          (H.entry i).start j = .derivative z k := by simpa only [heold i hi, hfold i hi] using hquery
      have hz := (A.queryHistory_covers_derivative
        (fun i => complexHistoryFunction H.entry (i + 1)) (fun i => (H.entry i).start) hi j hqueryold).1
      rw [hnew]
      exact G.old_values z hz hzone
    · rw [hnew]
      apply G.new_values j z k
      · simpa only [hnew, hes] using hquery
      · exact hzone
  · exact ⟨heold, fun i hi => extendBudget_agrees next hi⟩

def complexHistoryChain {n : ℕ} {A : ComplexAlgorithm n} {B p : ℝ}
    (available : ComplexStageExtensionAvailable A B p) : (s : ℕ) → ComplexHistory A B p s
  | 0 => initialComplexHistory A B p
  | s + 1 => Classical.choose (ComplexHistory.exists_extension available (complexHistoryChain available s))

theorem complexHistoryChain_extends {n : ℕ} {A : ComplexAlgorithm n} {B p : ℝ}
    (available : ComplexStageExtensionAvailable A B p) (s : ℕ) :
    (complexHistoryChain available s).Extends (complexHistoryChain available (s + 1)) :=
  Classical.choose_spec (ComplexHistory.exists_extension available (complexHistoryChain available s))

theorem complexHistoryChain_entry_stable {n : ℕ} {A : ComplexAlgorithm n} {B p : ℝ}
    (available : ComplexStageExtensionAvailable A B p) {i N M : ℕ} (hi : i < N) (hNM : N ≤ M) :
    (complexHistoryChain available M).entry i = (complexHistoryChain available N).entry i := by
  induction M, hNM using Nat.le_induction with
  | base => rfl
  | succ M hNM ih =>
    exact ((complexHistoryChain_extends available M).1 i (hi.trans_le hNM)).trans ih

theorem complexHistoryChain_budget_stable {n : ℕ} {A : ComplexAlgorithm n} {B p : ℝ}
    (available : ComplexStageExtensionAvailable A B p) {i N M : ℕ} (hi : i ≤ N) (hNM : N ≤ M) :
    (complexHistoryChain available M).budget i = (complexHistoryChain available N).budget i := by
  induction M, hNM using Nat.le_induction with
  | base => rfl
  | succ M hNM ih =>
    exact ((complexHistoryChain_extends available M).2 i (hi.trans hNM)).trans ih

def chosenComplexEntry {n : ℕ} {A : ComplexAlgorithm n} {B p : ℝ}
    (available : ComplexStageExtensionAvailable A B p) (i : ℕ) : ComplexStageEntry :=
  (complexHistoryChain available (i + 1)).entry i

def chosenComplexBudget {n : ℕ} {A : ComplexAlgorithm n} {B p : ℝ}
    (available : ComplexStageExtensionAvailable A B p) (i : ℕ) : ℝ :=
  (complexHistoryChain available i).budget i

theorem chosenComplexEntry_prefix {n : ℕ} {A : ComplexAlgorithm n} {B p : ℝ}
    (available : ComplexStageExtensionAvailable A B p) {i N : ℕ} (hi : i < N) :
    chosenComplexEntry available i = (complexHistoryChain available N).entry i :=
  (complexHistoryChain_entry_stable available (Nat.lt_succ_self i) (by omega : i + 1 ≤ N)).symm

theorem chosenComplexBudget_prefix {n : ℕ} {A : ComplexAlgorithm n} {B p : ℝ}
    (available : ComplexStageExtensionAvailable A B p) {i N : ℕ} (hi : i ≤ N) :
    chosenComplexBudget available i = (complexHistoryChain available N).budget i :=
  (complexHistoryChain_budget_stable available le_rfl hi).symm

theorem chosenComplexFunction_prefix {n : ℕ} {A : ComplexAlgorithm n} {B p : ℝ}
    (available : ComplexStageExtensionAvailable A B p) {N M : ℕ} (hNM : N ≤ M) :
    complexHistoryFunction (chosenComplexEntry available) N =
      complexHistoryFunction (complexHistoryChain available M).entry N := by
  apply complexHistoryFunction_congr
  intro i hi
  exact congrArg ComplexStageEntry.polynomial (chosenComplexEntry_prefix available (hi.trans_le hNM))

theorem chosenComplexOutput_prefix {n : ℕ} {A : ComplexAlgorithm n} {B p : ℝ}
    (available : ComplexStageExtensionAvailable A B p) {i M : ℕ} (hi : i < M) :
    complexHistoryOutput A (chosenComplexEntry available) i =
      complexHistoryOutput A (complexHistoryChain available M).entry i := by
  unfold complexHistoryOutput
  rw [chosenComplexFunction_prefix available (by omega : i + 1 ≤ M),
    chosenComplexEntry_prefix available hi]

/-- Compatible finite histories construct all infinite stage data, including
exact persistence of every saved derivative at every later finite stage. -/
theorem exists_complexAdversarialStages_of_extension {n : ℕ} {A : ComplexAlgorithm n} {B p : ℝ}
    (available : ComplexStageExtensionAvailable A B p) : Nonempty (ComplexAdversarialStages A B p) := by
  let e := chosenComplexEntry available
  let b := chosenComplexBudget available
  have he (i N : ℕ) (hi : i < N) : e i = (complexHistoryChain available N).entry i :=
    chosenComplexEntry_prefix available hi
  have hb (i N : ℕ) (hi : i ≤ N) : b i = (complexHistoryChain available N).budget i :=
    chosenComplexBudget_prefix available hi
  have hf (N M : ℕ) (hNM : N ≤ M) : complexHistoryFunction e N =
      complexHistoryFunction (complexHistoryChain available M).entry N :=
    chosenComplexFunction_prefix available hNM
  have hy (i M : ℕ) (hi : i < M) : complexHistoryOutput A e i =
      complexHistoryOutput A (complexHistoryChain available M).entry i :=
    chosenComplexOutput_prefix available hi
  have hbounds : ComplexPolynomialStageBounds (fun i => (e i).polynomial) b := by
    refine {
      budget_pos := fun i => (complexHistoryChain available i).bounds.budget_pos i
      budget_half := ?_
      budget_first := (complexHistoryChain available 0).bounds.budget_first
      disc_bound := ?_
      deriv_bound := ?_
    }
    · intro i
      rw [hb (i + 1) (i + 1) le_rfl, hb i (i + 1) (Nat.le_succ i)]
      exact (complexHistoryChain available (i + 1)).bounds.budget_half i
    · intro i z hz
      rw [he i (i + 1) (Nat.lt_succ_self i), hb i (i + 1) (Nat.le_succ i)]
      exact (complexHistoryChain available (i + 1)).bounds.disc_bound i z hz
    · intro i z hz
      rw [he i (i + 1) (Nat.lt_succ_self i), hb i (i + 1) (Nat.le_succ i)]
      exact (complexHistoryChain available (i + 1)).bounds.deriv_bound i z hz
  refine ⟨{
    polynomial := fun i => (e i).polynomial
    budget := b
    epsilon := fun i => (e i).epsilon
    starts := fun i => (e i).start
    roots := fun i => (e i).root
    coefficient := fun i => (e i).coefficient
    bounds := hbounds
    epsilon_pos := ?_
    epsilon_cap := ?_
    coefficient_pos := ?_
    root_norm := ?_
    stage_root := ?_
    start_lower := ?_
    start_upper := ?_
    error_bound := ?_
    amplification := ?_
    next_budget_error := ?_
    next_budget_scale := ?_
    jets_preserved := ?_
  }⟩
  · intro i
    rw [he i (i + 1) (Nat.lt_succ_self i)]
    exact (complexHistoryChain available (i + 1)).epsilon_pos i (Nat.lt_succ_self i)
  · intro i
    rw [he i (i + 1) (Nat.lt_succ_self i)]
    exact (complexHistoryChain available (i + 1)).epsilon_cap i (Nat.lt_succ_self i)
  · intro i
    rw [he i (i + 1) (Nat.lt_succ_self i)]
    exact (complexHistoryChain available (i + 1)).coefficient_pos i (Nat.lt_succ_self i)
  · intro i
    rw [he i (i + 1) (Nat.lt_succ_self i)]
    exact ((complexHistoryChain available (i + 1)).root_norm i (Nat.lt_succ_self i)).trans (by norm_num)
  · intro i
    change complexHistoryFunction e (i + 1) (e i).root = 0
    rw [hf (i + 1) (i + 1) le_rfl, he i (i + 1) (Nat.lt_succ_self i)]
    exact (complexHistoryChain available (i + 1)).is_root i (Nat.lt_succ_self i)
  · intro i
    rw [he i (i + 1) (Nat.lt_succ_self i)]
    exact (complexHistoryChain available (i + 1)).start_lower i (Nat.lt_succ_self i)
  · intro i
    rw [he i (i + 1) (Nat.lt_succ_self i)]
    exact (complexHistoryChain available (i + 1)).start_upper i (Nat.lt_succ_self i)
  · intro i
    change (e i).coefficient * (e i).epsilon ^ B ≤ ‖complexHistoryOutput A e i - (e i).root‖
    rw [hy i (i + 1) (Nat.lt_succ_self i), he i (i + 1) (Nat.lt_succ_self i)]
    exact (complexHistoryChain available (i + 1)).error_bound i (Nat.lt_succ_self i)
  · intro i
    rw [he i (i + 1) (Nat.lt_succ_self i)]
    exact (complexHistoryChain available (i + 1)).amplification i (Nat.lt_succ_self i)
  · intro i
    change b (i + 1) ≤ ‖complexHistoryOutput A e i - (e i).root‖ / 32
    rw [hb (i + 1) (i + 1) le_rfl, hy i (i + 1) (Nat.lt_succ_self i),
      he i (i + 1) (Nat.lt_succ_self i)]
    exact (complexHistoryChain available (i + 1)).next_budget_error i (Nat.lt_succ_self i)
  · intro i
    rw [hb (i + 1) (i + 1) le_rfl, he i (i + 1) (Nat.lt_succ_self i)]
    exact (complexHistoryChain available (i + 1)).next_budget_scale i (Nat.lt_succ_self i)
  · intro i j z k hquery N hN
    have hi : i < N := by omega
    change A.actualQuery (complexHistoryFunction e (i + 1)) (e i).start j = .derivative z k at hquery
    rw [hf (i + 1) N hN, he i N hi] at hquery
    change iteratedDeriv k (complexHistoryFunction e N) z =
      iteratedDeriv k (complexHistoryFunction e (i + 1)) z
    rw [hf N N le_rfl, hf (i + 1) N hN]
    exact (complexHistoryChain available N).old_jets i hi j z k hquery

/-- The exact scalar complex finite adversary constructs the stage sequence. -/
theorem exists_complexAdversarialStages {n : ℕ} (A : ComplexAlgorithm n) (hn : 0 < n)
    (p : ℝ) (hp : (orderBound n : ℝ) < p) :
    Nonempty (ComplexAdversarialStages A (orderBound n : ℝ) p) :=
  exists_complexAdversarialStages_of_extension (complex_scalarStageExtensionAvailable A hn p hp)

/-- The stage sequence gives the entire counterexample of Appendix B. -/
theorem complex_entireCounterexample_constructed {n : ℕ} (A : ComplexAlgorithm n)
    (hn : 0 < n) (p : ℝ) (hp : (orderBound n : ℝ) < p) :
    ComplexEntireCounterexample A.run p := by
  let D := Classical.choice (exists_complexAdversarialStages A hn p hp)
  exact D.counterexample ((Nat.cast_nonneg (orderBound n)).trans hp.le)

end KungTraubAppendices
