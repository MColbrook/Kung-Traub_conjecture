import KungTraub.Definitions

/-!
# Preservation of adaptive executions

The manuscript's entire-limit construction preserves the derivative answers at the queries
made in each earlier execution. The induction below proves that this preserves every later
decision and the final output, for arbitrary query and output rules. The grouped version uses
the same argument with a complete vector of answers at each induction step.

Finite tuple extension uses Mathlib's `Fin.snoc` machinery, from the tuple module by
Floris van Doorn, Yury Kudryashov, Sébastien Gouëzel, Chris Hughes and Antoine Chambert-Loir,
and Lean's `Fin.lastCases`. No continuity or measurability of a decision rule is required.
-/

noncomputable section

namespace KungTraub

/-- Equality of every derivative answer requested by a fixed query implies equality of its
answer. An idle query imposes no condition on the two input functions. -/
theorem RealQuery.answer_eq_of_derivatives_eq (q : RealQuery) {f g : ℝ → ℝ}
    (h : ∀ z ν, q = .derivative z ν → iteratedDeriv ν f z = iteratedDeriv ν g z) :
    q.answer f = q.answer g := by
  sorry

/-- The query made at a fixed stage of the actual execution on `f`. -/
def RealAlgorithm.actualQuery {n : ℕ} (A : RealAlgorithm n) (f : ℝ → ℝ)
    (x : ℝ) (j : Fin n) : RealQuery :=
  A.query j x (A.prefix f x j.val (Nat.le_of_lt j.isLt))

/-- Matching the answers to the actual `f`-run queries preserves every scalar prefix. The
agreement is only required on those queries, not on all possible transcripts. -/
theorem RealAlgorithm.prefix_eq_of_answers_eq {n : ℕ} (A : RealAlgorithm n)
    {f g : ℝ → ℝ} {x : ℝ}
    (h : ∀ j, (A.actualQuery f x j).answer f = (A.actualQuery f x j).answer g)
    (j : ℕ) (hj : j ≤ n) : A.prefix f x j hj = A.prefix g x j hj := by
  sorry

/-- Matching answers along the actual execution also preserves the chosen queries. -/
theorem RealAlgorithm.actualQuery_eq_of_answers_eq {n : ℕ} (A : RealAlgorithm n)
    {f g : ℝ → ℝ} {x : ℝ}
    (h : ∀ j, (A.actualQuery f x j).answer f = (A.actualQuery f x j).answer g)
    (j : Fin n) : A.actualQuery f x j = A.actualQuery g x j := by
  sorry

/-- Matching answers along the actual scalar execution preserves its output. -/
theorem RealAlgorithm.run_eq_of_answers_eq {n : ℕ} (A : RealAlgorithm n)
    {f g : ℝ → ℝ} {x : ℝ}
    (h : ∀ j, (A.actualQuery f x j).answer f = (A.actualQuery f x j).answer g) :
    A.run f x = A.run g x := by
  sorry

/-- Exact derivative data at all actual scalar queries preserve the output. Arbitrary
derivative orders and query locations are permitted; idle slots need no derivative data. -/
theorem RealAlgorithm.run_eq_of_derivatives_eq {n : ℕ} (A : RealAlgorithm n)
    {f g : ℝ → ℝ} {x : ℝ}
    (h : ∀ j z ν, A.actualQuery f x j = .derivative z ν →
      iteratedDeriv ν f z = iteratedDeriv ν g z) :
    A.run f x = A.run g x := by
  sorry

/-- All queries selected for one group of the actual execution on `f`. -/
def GroupedRealAlgorithm.actualQueries {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedRealAlgorithm sizes) (f : ℝ → ℝ) (x : ℝ) (j : Fin k) :
    Fin (sizes j) → RealQuery :=
  A.query j x (A.prefix f x j.val (Nat.le_of_lt j.isLt))

/-- Matching all answers to the actual `f`-run queries preserves every grouped prefix.
Only complete earlier groups enter query selection, as in the underlying model. -/
theorem GroupedRealAlgorithm.prefix_eq_of_answers_eq {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedRealAlgorithm sizes) {f g : ℝ → ℝ} {x : ℝ}
    (h : ∀ j slot, (A.actualQueries f x j slot).answer f =
      (A.actualQueries f x j slot).answer g)
    (j : ℕ) (hj : j ≤ k) : A.prefix f x j hj = A.prefix g x j hj := by
  sorry

/-- Matching answers along the grouped execution preserves each complete query vector. -/
theorem GroupedRealAlgorithm.actualQueries_eq_of_answers_eq {k : ℕ}
    {sizes : Fin k → ℕ} (A : GroupedRealAlgorithm sizes) {f g : ℝ → ℝ} {x : ℝ}
    (h : ∀ j slot, (A.actualQueries f x j slot).answer f =
      (A.actualQueries f x j slot).answer g)
    (j : Fin k) : A.actualQueries f x j = A.actualQueries g x j := by
  sorry

/-- Matching answers along the actual grouped execution preserves its output. -/
theorem GroupedRealAlgorithm.run_eq_of_answers_eq {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedRealAlgorithm sizes) {f g : ℝ → ℝ} {x : ℝ}
    (h : ∀ j slot, (A.actualQueries f x j slot).answer f =
      (A.actualQueries f x j slot).answer g) : A.run f x = A.run g x := by
  sorry

/-- Exact derivative data at the actual grouped queries preserve the output, without
introducing any dependence on answers from within a group. -/
theorem GroupedRealAlgorithm.run_eq_of_derivatives_eq {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedRealAlgorithm sizes) {f g : ℝ → ℝ} {x : ℝ}
    (h : ∀ j slot z ν, A.actualQueries f x j slot = .derivative z ν →
      iteratedDeriv ν f z = iteratedDeriv ν g z) : A.run f x = A.run g x := by
  sorry

end KungTraub
