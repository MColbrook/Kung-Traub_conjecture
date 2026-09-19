import KungTraub.Definitions

/-!
# Complex derivative observations and the counterexample

The complex oracle of Appendix B follows the real oracle in
`KungTraub.Definitions`. One complex value counts as one observation.
Query and output rules depend on the starting point and preceding answers.
-/

noncomputable section

open Filter
open scoped Topology

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
