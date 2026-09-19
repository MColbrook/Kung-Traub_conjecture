import KungTraub.EntireStageConstruction
import KungTraub.QueryHistories
import KungTraub.BudgetExtension

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
  funext t
  simp only [gaussianHistoryFunction, gaussianRealStage, finiteEntireStage, one_mul]
  congr 1
  exact Finset.sum_congr rfl (fun i hi => congrArg (fun P => gaussianPolynomial P t)
    (h i (Finset.mem_range.mp hi)))

theorem gaussianHistoryFunction_update_prefix (e : ℕ → GaussianStageEntry)
    (s : ℕ) (entry : GaussianStageEntry) (N : ℕ) (hN : N ≤ s) :
    gaussianHistoryFunction (Function.update e s entry) N = gaussianHistoryFunction e N := by
  apply gaussianHistoryFunction_congr
  intro i hi
  rw [Function.update_of_ne (by omega : i ≠ s)]

theorem gaussianHistoryFunction_update_succ (e : ℕ → GaussianStageEntry)
    (s : ℕ) (entry : GaussianStageEntry) :
    gaussianHistoryFunction (Function.update e s entry) (s + 1) =
      fun t => gaussianHistoryFunction e s t + gaussianPolynomial entry.polynomial t := by
  funext t
  unfold gaussianHistoryFunction gaussianRealStage
  rw [finiteEntireStage_succ]
  have hp := congrFun (gaussianHistoryFunction_update_prefix e s entry s le_rfl) t
  unfold gaussianHistoryFunction gaussianRealStage at hp
  rw [hp]
  simp only [Function.update_self, one_mul]

theorem gaussianHistoryFunction_eq_base (e : ℕ → GaussianStageEntry) (s : ℕ) :
    gaussianHistoryFunction e s =
      fun t => t + gaussianPolynomial (∑ i ∈ Finset.range s, (e i).polynomial) t := by
  unfold gaussianHistoryFunction gaussianRealStage
  simpa only [Polynomial.C_1, one_mul] using
    finiteEntireStage_gaussian_form (fun i => (e i).polynomial) (fun _ => 1) s

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
  intro s P Z orders a b hbase ha hroot hold hb hbsmall
  exact exists_gaussianStageChoice A hn P Z orders hbase ha hroot hold hb hbsmall
    (by positivity) (hp s) s

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
  refine {
    budget_pos := fun i => by positivity
    budget_half := ?_
    budget_first := by norm_num
    value_bound := ?_
    deriv_bound := ?_
    disc_bound := ?_
  }
  · intro i
    rw [pow_succ]
    exact le_of_eq (by ring)
  · intro i t
    simp [gaussianPolynomial]
  · intro i t
    simp [gaussianPolynomial]
  · intro i z _
    simp [complexGaussianPolynomial]

theorem initialGaussianHistory_vacuous {P : ℕ → Prop} : ∀ i < 0, P i :=
  fun i hi => False.elim (Nat.not_lt_zero i hi)

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
  have hp : (1 / 2 : ℝ) ^ s ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  calc
    H.budget s ≤ H.budget 0 * (1 / 2 : ℝ) ^ s := budget_le_geometric H.bounds.budget_half s
    _ ≤ H.budget 0 * 1 := mul_le_mul_of_nonneg_left hp (H.bounds.budget_pos 0).le
    _ ≤ 1 / 16 := by linarith [H.bounds.budget_first]

theorem GaussianHistory.current_root {n : ℕ} {A : RealAlgorithm n} {B : ℝ}
    {exponent : ℕ → ℝ} {s : ℕ} (H : GaussianHistory A B exponent s) :
    ∃ a : ℝ, gaussianHistoryFunction H.entry s a = 0 ∧ |a| ≤ 1 / 4 := by
  have hf : Differentiable ℝ (gaussianHistoryFunction H.entry s) :=
    fun t => (finiteEntireStage_hasDerivAt
      (fun i y => ((gaussianPolynomial_hasDerivAt (H.entry i).polynomial y).const_mul 1).differentiableAt)
      s t).differentiableAt
  obtain ⟨a, ha, _⟩ := existsUnique_zero_of_bounded_identity_perturbation hf
    (by norm_num : (0 : ℝ) < 15 / 16)
    (fun t => (H.bounds.finite_bounds s t).2.1) (fun t => (H.bounds.finite_bounds s t).1)
  have habs := abs_zero_le_perturbation_bound (fun t => (H.bounds.finite_bounds s t).1) ha
  exact ⟨a, ha, by linarith⟩

theorem GaussianHistory.history_nodes_nonzero {n : ℕ} {A : RealAlgorithm n} {B : ℝ}
    {exponent : ℕ → ℝ} {s : ℕ} (H : GaussianHistory A B exponent s) :
    ∀ z ∈ queryNodes (A.queryHistory (fun i => gaussianHistoryFunction H.entry (i + 1))
      (fun i => (H.entry i).start) s), gaussianHistoryFunction H.entry s z ≠ 0 := by
  classical
  intro z hz
  obtain ⟨k, hk⟩ := (mem_queryNodes_iff _ z).mp hz
  obtain ⟨i, hi, hki⟩ := Finset.mem_biUnion.mp hk
  obtain ⟨j, _, hquery⟩ := Finset.mem_image.mp hki
  exact H.old_values i (Finset.mem_range.mp hi) j z k hquery

theorem GaussianHistory.update_bounds {n : ℕ} {A : RealAlgorithm n} {B : ℝ}
    {exponent : ℕ → ℝ} {s : ℕ} (H : GaussianHistory A B exponent s)
    (entry : GaussianStageEntry) {next : ℝ} (hnext : 0 < next) (hhalf : next ≤ H.budget s / 2)
    (hvalue : ∀ t, |gaussianPolynomial entry.polynomial t| ≤ H.budget s)
    (hderiv : ∀ t, |deriv (gaussianPolynomial entry.polynomial) t| ≤ H.budget s)
    (hdisc : ∀ z : ℂ, ‖z‖ ≤ (s : ℝ) + 3 →
      ‖complexGaussianPolynomial entry.polynomial z‖ ≤ H.budget s) :
    GaussianStageBounds (fun i => ((Function.update H.entry s entry) i).polynomial)
      (fun _ => 1) (extendBudget H.budget s next) := by
  have hfuture (i : ℕ) (hi : s < i) : ((Function.update H.entry s entry) i).polynomial = 0 := by
    rw [Function.update_of_ne (ne_of_gt hi), H.tail_zero i hi.le]
  refine {
    budget_pos := extendBudget_pos H.bounds.budget_pos hnext
    budget_half := extendBudget_half H.bounds.budget_half hhalf
    budget_first := extendBudget_initial_bound H.bounds.budget_first
    value_bound := ?_
    deriv_bound := ?_
    disc_bound := ?_
  }
  · intro i t
    rcases lt_trichotomy i s with hi | rfl | hi
    · rw [Function.update_of_ne (ne_of_lt hi), extendBudget_agrees next hi.le]
      exact H.bounds.value_bound i t
    · simpa only [Function.update_self, one_mul, extendBudget_agrees next le_rfl] using hvalue t
    · simpa [hfuture i hi, gaussianPolynomial] using
        (extendBudget_pos H.bounds.budget_pos hnext i).le
  · intro i t
    rcases lt_trichotomy i s with hi | rfl | hi
    · rw [Function.update_of_ne (ne_of_lt hi), extendBudget_agrees next hi.le]
      exact H.bounds.deriv_bound i t
    · simpa only [Function.update_self, one_mul, extendBudget_agrees next le_rfl] using hderiv t
    · simpa [hfuture i hi, gaussianPolynomial] using
        (extendBudget_pos H.bounds.budget_pos hnext i).le
  · intro i z hz
    rcases lt_trichotomy i s with hi | rfl | hi
    · rw [Function.update_of_ne (ne_of_lt hi), extendBudget_agrees next hi.le]
      exact H.bounds.disc_bound i z hz
    · simpa only [Function.update_self, Complex.ofReal_one, one_mul,
        extendBudget_agrees next le_rfl] using hdisc z hz
    · simpa [hfuture i hi, complexGaussianPolynomial] using
        (extendBudget_pos H.bounds.budget_pos hnext i).le

/-- Every valid finite history has an extension preserving all previous stages.
The finite adversary supplies the one-step extension property. -/
theorem GaussianHistory.exists_extension {n : ℕ} {A : RealAlgorithm n} {B : ℝ}
    {exponent : ℕ → ℝ} (available : GaussianStageExtensionAvailable A B exponent)
    {s : ℕ} (H : GaussianHistory A B exponent s) :
    ∃ H' : GaussianHistory A B exponent (s + 1), H.Extends H' := by
  classical
  let P := ∑ i ∈ Finset.range s, (H.entry i).polynomial
  have hbaseeq : gaussianHistoryFunction H.entry s = fun t => t + gaussianPolynomial P t :=
    gaussianHistoryFunction_eq_base H.entry s
  have hbase : ∀ t : ℝ, |(t + gaussianPolynomial P t) - t| ≤ 1 / 16 ∧
      (15 : ℝ) / 16 ≤ deriv (fun y => y + gaussianPolynomial P y) t ∧
      deriv (fun y => y + gaussianPolynomial P y) t ≤ 17 / 16 := by
    intro t
    have h : |gaussianHistoryFunction H.entry s t - t| ≤ 1 / 16 ∧
        (15 : ℝ) / 16 ≤ deriv (gaussianHistoryFunction H.entry s) t ∧
        deriv (gaussianHistoryFunction H.entry s) t ≤ 17 / 16 := H.bounds.finite_bounds s t
    simpa only [hbaseeq] using h
  obtain ⟨a, hroot, ha⟩ := H.current_root
  let queries := A.queryHistory (fun i => gaussianHistoryFunction H.entry (i + 1))
    (fun i => (H.entry i).start) s
  have hold : ∀ z ∈ queryNodes queries, z + gaussianPolynomial P z ≠ 0 := by
    intro z hz
    rw [← congrFun hbaseeq z]
    exact H.history_nodes_nonzero z hz
  let G := Classical.choice (available s P (queryNodes queries) (maxQueryOrder queries) a (H.budget s)
    hbase ha (by simpa only [hbaseeq] using hroot) hold (H.bounds.budget_pos s) H.current_budget_small)
  obtain ⟨next, hnext, hnextHalf, hnextError, hnextScale⟩ :=
    G.exists_next_budget (H.bounds.budget_pos s)
  let entry : GaussianStageEntry := ⟨Polynomial.C G.multiplier * G.polynomial,
    G.epsilon, a + G.epsilon, G.root, G.coefficient⟩
  let e := Function.update H.entry s entry
  have heold (i : ℕ) (hi : i < s) : e i = H.entry i := Function.update_of_ne (ne_of_lt hi) _ _
  have hes : e s = entry := Function.update_self _ _ _
  have hfold (i : ℕ) (hi : i < s) :
      gaussianHistoryFunction e (i + 1) = gaussianHistoryFunction H.entry (i + 1) :=
    gaussianHistoryFunction_update_prefix H.entry s entry (i + 1) (by omega)
  have hyold (i : ℕ) (hi : i < s) :
      gaussianHistoryOutput A e i = gaussianHistoryOutput A H.entry i := by
    unfold gaussianHistoryOutput
    rw [hfold i hi, heold i hi]
  have hnew : gaussianHistoryFunction e (s + 1) =
      gaussianUpdatedFunction P G.multiplier G.polynomial := by
    rw [gaussianHistoryFunction_update_succ, hbaseeq]
    funext t
    change (t + gaussianPolynomial P t) +
      gaussianPolynomial (Polynomial.C G.multiplier * G.polynomial) t = _
    rw [gaussianPolynomial_C_mul]
    rfl
  have hynew : gaussianHistoryOutput A e s =
      A.run (gaussianUpdatedFunction P G.multiplier G.polynomial) (a + G.epsilon) := by
    unfold gaussianHistoryOutput
    rw [hnew, hes]
  have hg : gaussianPolynomial entry.polynomial =
      fun t => G.multiplier * gaussianPolynomial G.polynomial t := by
    funext t
    exact gaussianPolynomial_C_mul G.multiplier G.polynomial t
  have hbounds : GaussianStageBounds (fun i => (e i).polynomial) (fun _ => 1)
      (extendBudget H.budget s next) := H.update_bounds entry hnext hnextHalf
    (fun t => by rw [hg]; exact G.value_bound t)
    (fun t => by rw [hg]; exact G.deriv_bound t)
    (fun z hz => by rw [complexGaussianPolynomial_C_mul]; exact G.disc_bound z hz)
  refine ⟨{
    entry := e
    budget := extendBudget H.budget s next
    bounds := hbounds
    tail_zero := ?_
    epsilon_pos := ?_
    epsilon_cap := ?_
    epsilon_quarter := ?_
    coefficient_pos := ?_
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
    · simpa only [heold i hi] using H.epsilon_quarter i hi
    · simpa only [hes] using G.epsilon_quarter
  · intro i hi
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | rfl
    · simpa only [heold i hi] using H.coefficient_pos i hi
    · simpa only [hes] using G.coefficient_pos
  · intro i hi
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | rfl
    · simpa only [heold i hi, hfold i hi] using H.is_root i hi
    · simpa only [hes, hnew] using G.is_root
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
    · have hqueryold : A.actualQuery (gaussianHistoryFunction H.entry (i + 1))
          (H.entry i).start j = .derivative z k := by simpa only [heold i hi, hfold i hi] using hquery
      obtain ⟨hz, hk⟩ := A.queryHistory_covers_derivative
        (fun i => gaussianHistoryFunction H.entry (i + 1)) (fun i => (H.entry i).start) hi j hqueryold
      calc
        iteratedDeriv k (gaussianHistoryFunction e (s + 1)) z =
            iteratedDeriv k (gaussianHistoryFunction H.entry s) z := by
          rw [hnew, G.old_jets z hz k hk, ← hbaseeq]
        _ = iteratedDeriv k (gaussianHistoryFunction H.entry (i + 1)) z :=
          H.old_jets i hi j z k hqueryold
        _ = iteratedDeriv k (gaussianHistoryFunction e (i + 1)) z := by rw [hfold i hi]
    · rfl
  · intro i hi j z k hquery
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hi | rfl
    · have hqueryold : A.actualQuery (gaussianHistoryFunction H.entry (i + 1))
          (H.entry i).start j = .derivative z k := by simpa only [heold i hi, hfold i hi] using hquery
      have hz := (A.queryHistory_covers_derivative
        (fun i => gaussianHistoryFunction H.entry (i + 1)) (fun i => (H.entry i).start) hi j hqueryold).1
      rw [hnew]
      exact G.old_values z hz
    · rw [hnew]
      apply G.new_values j z k
      simpa only [hnew, hes] using hquery
  · exact ⟨heold, fun i hi => extendBudget_agrees next hi⟩

def gaussianHistoryChain {n : ℕ} {A : RealAlgorithm n} {B : ℝ} {exponent : ℕ → ℝ}
    (available : GaussianStageExtensionAvailable A B exponent) :
    (s : ℕ) → GaussianHistory A B exponent s
  | 0 => initialGaussianHistory A B exponent
  | s + 1 => Classical.choose (GaussianHistory.exists_extension available (gaussianHistoryChain available s))

theorem gaussianHistoryChain_extends {n : ℕ} {A : RealAlgorithm n} {B : ℝ} {exponent : ℕ → ℝ}
    (available : GaussianStageExtensionAvailable A B exponent) (s : ℕ) :
    (gaussianHistoryChain available s).Extends (gaussianHistoryChain available (s + 1)) :=
  Classical.choose_spec (GaussianHistory.exists_extension available (gaussianHistoryChain available s))

theorem gaussianHistoryChain_entry_stable {n : ℕ} {A : RealAlgorithm n} {B : ℝ}
    {exponent : ℕ → ℝ} (available : GaussianStageExtensionAvailable A B exponent)
    {i N M : ℕ} (hi : i < N) (hNM : N ≤ M) :
    (gaussianHistoryChain available M).entry i = (gaussianHistoryChain available N).entry i := by
  induction M, hNM using Nat.le_induction with
  | base => rfl
  | succ M hNM ih =>
    exact ((gaussianHistoryChain_extends available M).1 i (hi.trans_le hNM)).trans ih

theorem gaussianHistoryChain_budget_stable {n : ℕ} {A : RealAlgorithm n} {B : ℝ}
    {exponent : ℕ → ℝ} (available : GaussianStageExtensionAvailable A B exponent)
    {i N M : ℕ} (hi : i ≤ N) (hNM : N ≤ M) :
    (gaussianHistoryChain available M).budget i = (gaussianHistoryChain available N).budget i := by
  induction M, hNM using Nat.le_induction with
  | base => rfl
  | succ M hNM ih =>
    exact ((gaussianHistoryChain_extends available M).2 i (hi.trans hNM)).trans ih

def chosenGaussianEntry {n : ℕ} {A : RealAlgorithm n} {B : ℝ} {exponent : ℕ → ℝ}
    (available : GaussianStageExtensionAvailable A B exponent) (i : ℕ) : GaussianStageEntry :=
  (gaussianHistoryChain available (i + 1)).entry i

def chosenGaussianBudget {n : ℕ} {A : RealAlgorithm n} {B : ℝ} {exponent : ℕ → ℝ}
    (available : GaussianStageExtensionAvailable A B exponent) (i : ℕ) : ℝ :=
  (gaussianHistoryChain available i).budget i

theorem chosenGaussianEntry_prefix {n : ℕ} {A : RealAlgorithm n} {B : ℝ}
    {exponent : ℕ → ℝ} (available : GaussianStageExtensionAvailable A B exponent)
    {i N : ℕ} (hi : i < N) :
    chosenGaussianEntry available i = (gaussianHistoryChain available N).entry i :=
  (gaussianHistoryChain_entry_stable available (Nat.lt_succ_self i) (by omega : i + 1 ≤ N)).symm

theorem chosenGaussianBudget_prefix {n : ℕ} {A : RealAlgorithm n} {B : ℝ}
    {exponent : ℕ → ℝ} (available : GaussianStageExtensionAvailable A B exponent)
    {i N : ℕ} (hi : i ≤ N) :
    chosenGaussianBudget available i = (gaussianHistoryChain available N).budget i :=
  (gaussianHistoryChain_budget_stable available le_rfl hi).symm

theorem chosenGaussianFunction_prefix {n : ℕ} {A : RealAlgorithm n} {B : ℝ}
    {exponent : ℕ → ℝ} (available : GaussianStageExtensionAvailable A B exponent)
    {N M : ℕ} (hNM : N ≤ M) :
    gaussianHistoryFunction (chosenGaussianEntry available) N =
      gaussianHistoryFunction (gaussianHistoryChain available M).entry N := by
  apply gaussianHistoryFunction_congr
  intro i hi
  exact congrArg GaussianStageEntry.polynomial (chosenGaussianEntry_prefix available (hi.trans_le hNM))

theorem chosenGaussianOutput_prefix {n : ℕ} {A : RealAlgorithm n} {B : ℝ}
    {exponent : ℕ → ℝ} (available : GaussianStageExtensionAvailable A B exponent)
    {i M : ℕ} (hi : i < M) :
    gaussianHistoryOutput A (chosenGaussianEntry available) i =
      gaussianHistoryOutput A (gaussianHistoryChain available M).entry i := by
  unfold gaussianHistoryOutput
  rw [chosenGaussianFunction_prefix available (by omega : i + 1 ≤ M),
    chosenGaussianEntry_prefix available hi]

/-- Compatible finite histories determine an infinite sequence of stages. -/
theorem exists_gaussianAdversarialStages_of_extension {n : ℕ} {A : RealAlgorithm n} {B : ℝ}
    {exponent : ℕ → ℝ} (available : GaussianStageExtensionAvailable A B exponent) :
    Nonempty (GaussianAdversarialStages A B exponent) := by
  let e := chosenGaussianEntry available
  let b := chosenGaussianBudget available
  have he (i N : ℕ) (hi : i < N) : e i = (gaussianHistoryChain available N).entry i :=
    chosenGaussianEntry_prefix available hi
  have hb (i N : ℕ) (hi : i ≤ N) : b i = (gaussianHistoryChain available N).budget i :=
    chosenGaussianBudget_prefix available hi
  have hf (N M : ℕ) (hNM : N ≤ M) : gaussianHistoryFunction e N =
      gaussianHistoryFunction (gaussianHistoryChain available M).entry N :=
    chosenGaussianFunction_prefix available hNM
  have hy (i M : ℕ) (hi : i < M) : gaussianHistoryOutput A e i =
      gaussianHistoryOutput A (gaussianHistoryChain available M).entry i :=
    chosenGaussianOutput_prefix available hi
  have hbounds : GaussianStageBounds (fun i => (e i).polynomial) (fun _ => 1) b := by
    refine {
      budget_pos := fun i => (gaussianHistoryChain available i).bounds.budget_pos i
      budget_half := ?_
      budget_first := (gaussianHistoryChain available 0).bounds.budget_first
      value_bound := ?_
      deriv_bound := ?_
      disc_bound := ?_
    }
    · intro i
      rw [hb (i + 1) (i + 1) le_rfl, hb i (i + 1) (Nat.le_succ i)]
      exact (gaussianHistoryChain available (i + 1)).bounds.budget_half i
    · intro i t
      rw [he i (i + 1) (Nat.lt_succ_self i), hb i (i + 1) (Nat.le_succ i)]
      exact (gaussianHistoryChain available (i + 1)).bounds.value_bound i t
    · intro i t
      rw [he i (i + 1) (Nat.lt_succ_self i), hb i (i + 1) (Nat.le_succ i)]
      exact (gaussianHistoryChain available (i + 1)).bounds.deriv_bound i t
    · intro i z hz
      rw [he i (i + 1) (Nat.lt_succ_self i), hb i (i + 1) (Nat.le_succ i)]
      exact (gaussianHistoryChain available (i + 1)).bounds.disc_bound i z hz
  refine ⟨{
    polynomial := fun i => (e i).polynomial
    scale := fun _ => 1
    budget := b
    epsilon := fun i => (e i).epsilon
    starts := fun i => (e i).start
    roots := fun i => (e i).root
    coefficient := fun i => (e i).coefficient
    bounds := hbounds
    epsilon_pos := ?_
    epsilon_cap := ?_
    epsilon_quarter := ?_
    coefficient_pos := ?_
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
    exact (gaussianHistoryChain available (i + 1)).epsilon_pos i (Nat.lt_succ_self i)
  · intro i
    rw [he i (i + 1) (Nat.lt_succ_self i)]
    exact (gaussianHistoryChain available (i + 1)).epsilon_cap i (Nat.lt_succ_self i)
  · intro i
    rw [he i (i + 1) (Nat.lt_succ_self i)]
    exact (gaussianHistoryChain available (i + 1)).epsilon_quarter i (Nat.lt_succ_self i)
  · intro i
    rw [he i (i + 1) (Nat.lt_succ_self i)]
    exact (gaussianHistoryChain available (i + 1)).coefficient_pos i (Nat.lt_succ_self i)
  · intro i
    change gaussianHistoryFunction e (i + 1) (e i).root = 0
    rw [hf (i + 1) (i + 1) le_rfl, he i (i + 1) (Nat.lt_succ_self i)]
    exact (gaussianHistoryChain available (i + 1)).is_root i (Nat.lt_succ_self i)
  · intro i
    rw [he i (i + 1) (Nat.lt_succ_self i)]
    exact (gaussianHistoryChain available (i + 1)).start_lower i (Nat.lt_succ_self i)
  · intro i
    rw [he i (i + 1) (Nat.lt_succ_self i)]
    exact (gaussianHistoryChain available (i + 1)).start_upper i (Nat.lt_succ_self i)
  · intro i
    change (e i).coefficient * (e i).epsilon ^ B ≤ |gaussianHistoryOutput A e i - (e i).root|
    rw [hy i (i + 1) (Nat.lt_succ_self i), he i (i + 1) (Nat.lt_succ_self i)]
    exact (gaussianHistoryChain available (i + 1)).error_bound i (Nat.lt_succ_self i)
  · intro i
    rw [he i (i + 1) (Nat.lt_succ_self i)]
    exact (gaussianHistoryChain available (i + 1)).amplification i (Nat.lt_succ_self i)
  · intro i
    change b (i + 1) ≤ |gaussianHistoryOutput A e i - (e i).root| / 32
    rw [hb (i + 1) (i + 1) le_rfl, hy i (i + 1) (Nat.lt_succ_self i),
      he i (i + 1) (Nat.lt_succ_self i)]
    exact (gaussianHistoryChain available (i + 1)).next_budget_error i (Nat.lt_succ_self i)
  · intro i
    rw [hb (i + 1) (i + 1) le_rfl, he i (i + 1) (Nat.lt_succ_self i)]
    exact (gaussianHistoryChain available (i + 1)).next_budget_scale i (Nat.lt_succ_self i)
  · intro i j z k hquery N hN
    have hi : i < N := by omega
    change A.actualQuery (gaussianHistoryFunction e (i + 1)) (e i).start j = .derivative z k at hquery
    rw [hf (i + 1) N hN, he i N hi] at hquery
    change iteratedDeriv k (gaussianHistoryFunction e N) z =
      iteratedDeriv k (gaussianHistoryFunction e (i + 1)) z
    rw [hf N N le_rfl, hf (i + 1) N hN]
    exact (gaussianHistoryChain available N).old_jets i hi j z k hquery

/-- Actual scalar stages are constructed for any sequence of exponents above B_n. -/
theorem exists_scalar_gaussianAdversarialStages {n : ℕ} (A : RealAlgorithm n) (hn : 0 < n)
    (exponent : ℕ → ℝ) (hp : ∀ s, (orderBound n : ℝ) < exponent s) :
    Nonempty (GaussianAdversarialStages A (orderBound n : ℝ) exponent) :=
  exists_gaussianAdversarialStages_of_extension (scalar_gaussianStageExtensionAvailable A hn exponent hp)

/-- The scalar entire counterexample. -/
theorem scalar_entireCounterexample_constructed {n : ℕ} (A : RealAlgorithm n) (hn : 0 < n)
    (p : ℝ) (hp : (orderBound n : ℝ) < p) : EntireCounterexample A.run p := by
  let D := Classical.choice (exists_scalar_gaussianAdversarialStages A hn (fun _ => p) (fun _ => hp))
  exact entireCounterexample_of_gaussian_stages D ((Nat.cast_nonneg (orderBound n)).trans hp.le)

/-- One constructed entire function and one sequence defeat every larger scalar order. -/
theorem scalar_simultaneousEntireCounterexample_constructed {n : ℕ} (A : RealAlgorithm n)
    (hn : 0 < n) : SimultaneousEntireCounterexample A.run (orderBound n : ℝ) := by
  have hp : ∀ s : ℕ, (orderBound n : ℝ) < (orderBound n : ℝ) + 1 / ((s : ℝ) + 1) := by
    intro s
    have h : (0 : ℝ) < 1 / ((s : ℝ) + 1) := by positivity
    linarith
  let D := Classical.choice (exists_scalar_gaussianAdversarialStages A hn
    (fun s => (orderBound n : ℝ) + 1 / ((s : ℝ) + 1)) hp)
  exact simultaneousEntireCounterexample_of_gaussian_stages D (Nat.cast_nonneg _)

end KungTraub
