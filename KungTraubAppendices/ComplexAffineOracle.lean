import KungTraubAppendices.ComplexDefinitions
import KungTraub.PolynomialInformation

/-!
# Complex affine fibres of adaptive observations

The fixed-scale argument restricts linear observations of functions to an affine
family indexed by complex parameters. Decision rules remain arbitrary. Along an
actual execution, the parameters with the same prefix form exactly the translate
of the common kernel of the rows selected during that execution.

This module adapts the real transcript proofs in `KungTraub.AffineTranscripts`.
The field-polymorphic scalar-prefix kernel and rank results in
`KungTraub.PolynomialInformation` are reused directly over ℂ. One complex
linear functional counts as one scalar observation.

The optional location allows the finite-scale construction to avoid the query
point when an affine observation comes from derivative evaluation. It plays no
role in the affine equations. Mathlib supplies linear-map kernels and finite
tuple extension for arbitrary decision and output rules.
-/

noncomputable section

namespace KungTraubAppendices

open KungTraub

variable (E : Type*) [AddCommGroup E] [Module ℂ E]

/-- One affine complex scalar observation, with an optional derivative-query location. -/
structure ComplexAffineObservation where
  linear : E →ₗ[ℂ] ℂ
  offset : ℂ
  location : Option ℂ

variable {E}

/-- The actual affine answer at a parameter. -/
def ComplexAffineObservation.answer (q : ComplexAffineObservation E) (u : E) : ℂ :=
  q.offset + q.linear u

/-- Two answers agree exactly when the parameter difference annihilates the row. -/
theorem ComplexAffineObservation.answer_eq_iff (q : ComplexAffineObservation E) (u v : E) :
    q.answer v = q.answer u ↔ q.linear (v - u) = 0 := by
  simp only [answer, map_sub, sub_eq_zero, add_right_inj]

variable (E)

/-- Arbitrary adaptive complex rules using only the start and previous scalar answers. -/
structure ComplexAffineAlgorithm (n : ℕ) where
  query : (j : Fin n) → ℂ → (Fin j.val → ℂ) → ComplexAffineObservation E
  output : ℂ → (Fin n → ℂ) → ℂ

variable {E}

/-- The exact complex answer prefix selected recursively by the rules. -/
def ComplexAffineAlgorithm.prefix {n : ℕ} (A : ComplexAffineAlgorithm E n) (u : E) (x : ℂ) :
    (j : ℕ) → j ≤ n → (Fin j → ℂ)
  | 0, _ => Fin.elim0
  | j + 1, hj =>
      let hlt : j < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hj
      let previous := A.prefix u x j (Nat.le_of_lt hlt)
      Fin.snoc previous ((A.query ⟨j, hlt⟩ x previous).answer u)

/-- Output after the full complex answer prefix. -/
def ComplexAffineAlgorithm.run {n : ℕ} (A : ComplexAffineAlgorithm E n) (u : E) (x : ℂ) : ℂ :=
  A.output x (A.prefix u x n le_rfl)

/-- The observation chosen on this actual parameter execution. -/
def ComplexAffineAlgorithm.actualObservation {n : ℕ} (A : ComplexAffineAlgorithm E n)
    (u : E) (x : ℂ) (j : Fin n) : ComplexAffineObservation E :=
  A.query j x (A.prefix u x j.val (Nat.le_of_lt j.isLt))

/-- Zero extension beyond the query budget is only for the common prefix-map API. -/
def ComplexAffineAlgorithm.actualLinearMap {n : ℕ} (A : ComplexAffineAlgorithm E n)
    (u : E) (x : ℂ) (j : ℕ) : E →ₗ[ℂ] ℂ :=
  if hj : j < n then (A.actualObservation u x ⟨j, hj⟩).linear else 0

/-- Common complex kernel of the rows selected along the actual prefix. -/
def ComplexAffineAlgorithm.direction {n : ℕ} (A : ComplexAffineAlgorithm E n)
    (u : E) (x : ℂ) (j : ℕ) : Submodule ℂ E :=
  scalarPrefixKernel (A.actualLinearMap u x) j

/-- Exact adaptive prefix equality is equivalent to the selected linear equations. -/
theorem ComplexAffineAlgorithm.prefix_eq_iff_linear_equations {n : ℕ}
    (A : ComplexAffineAlgorithm E n) (u v : E) (x : ℂ) (j : ℕ) (hj : j ≤ n) :
    A.prefix v x j hj = A.prefix u x j hj ↔
      ∀ i < j, A.actualLinearMap u x i (v - u) = 0 := by
  induction j with
  | zero => simp [ComplexAffineAlgorithm.prefix]
  | succ j ih =>
    have hlt : j < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hj
    have hjn : j ≤ n := Nat.le_of_lt hlt
    constructor
    · intro h
      simp only [ComplexAffineAlgorithm.prefix] at h
      have hp := Fin.snoc_inj.mp h
      have hprev := (ih hjn).mp hp.1
      have hlast := hp.2
      rw [hp.1] at hlast
      have hrow : A.actualLinearMap u x j (v - u) = 0 := by
        simpa only [actualLinearMap, dif_pos hlt, actualObservation] using
          ((A.actualObservation u x ⟨j, hlt⟩).answer_eq_iff u v).mp hlast
      intro i hi
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hij | rfl
      · exact hprev i hij
      · exact hrow
    · intro h
      have hp := (ih hjn).mpr (fun i hi => h i (Nat.lt_succ_of_lt hi))
      simp only [ComplexAffineAlgorithm.prefix]
      rw [hp]
      apply Fin.snoc_inj.mpr
      refine ⟨rfl, ?_⟩
      apply ((A.actualObservation u x ⟨j, hlt⟩).answer_eq_iff u v).mpr
      simpa only [actualLinearMap, dif_pos hlt] using h j (Nat.lt_succ_self j)

/-- Parameters giving one exact prefix form a translate of its common kernel. -/
theorem ComplexAffineAlgorithm.prefix_eq_iff_sub_mem_direction {n : ℕ}
    (A : ComplexAffineAlgorithm E n) (u v : E) (x : ℂ) (j : ℕ) (hj : j ≤ n) :
    A.prefix v x j hj = A.prefix u x j hj ↔ v - u ∈ A.direction u x j := by
  rw [prefix_eq_iff_linear_equations, direction, mem_scalarPrefixKernel]

/-- Moving inside the actual affine fibre preserves every answer in the prefix. -/
theorem ComplexAffineAlgorithm.prefix_add_eq_of_mem_direction {n : ℕ}
    (A : ComplexAffineAlgorithm E n) (u h : E) (x : ℂ) (j : ℕ) (hj : j ≤ n)
    (hh : h ∈ A.direction u x j) :
    A.prefix (u + h) x j hj = A.prefix u x j hj := by
  apply (A.prefix_eq_iff_sub_mem_direction u (u + h) x j hj).mpr
  simpa only [add_sub_cancel_left] using hh

/-- A displacement in the final common kernel preserves the exact output. -/
theorem ComplexAffineAlgorithm.run_add_eq_of_mem_direction {n : ℕ}
    (A : ComplexAffineAlgorithm E n) (u h : E) (x : ℂ) (hh : h ∈ A.direction u x n) :
    A.run (u + h) x = A.run u x :=
  congrArg (A.output x) (A.prefix_add_eq_of_mem_direction u h x n le_rfl hh)

/-- Equality of a longer prefix preserves every earlier prefix. -/
theorem ComplexAffineAlgorithm.prefix_eq_of_later_prefix_eq {n : ℕ}
    (A : ComplexAffineAlgorithm E n) {u v : E} {x : ℂ} {j k : ℕ} (hjk : j ≤ k) (hkn : k ≤ n)
    (heq : A.prefix v x k hkn = A.prefix u x k hkn) :
    A.prefix v x j (hjk.trans hkn) = A.prefix u x j (hjk.trans hkn) := by
  rw [prefix_eq_iff_linear_equations] at heq ⊢
  exact fun i hi => heq i (lt_of_lt_of_le hi hjk)

/-- Equal previous answers force exactly the same next observation. -/
theorem ComplexAffineAlgorithm.actualObservation_eq_of_prefix_eq {n : ℕ}
    (A : ComplexAffineAlgorithm E n) {u v : E} {x : ℂ} (j : Fin n)
    (heq : A.prefix v x j.val (Nat.le_of_lt j.isLt) =
      A.prefix u x j.val (Nat.le_of_lt j.isLt)) :
    A.actualObservation v x j = A.actualObservation u x j :=
  congrArg (A.query j x) heq

/-- Equal previous answers also preserve the actual next linear row. -/
theorem ComplexAffineAlgorithm.actualLinearMap_eq_of_prefix_eq {n : ℕ}
    (A : ComplexAffineAlgorithm E n) {u v : E} {x : ℂ} {j : ℕ} (hj : j < n)
    (heq : A.prefix v x j (Nat.le_of_lt hj) = A.prefix u x j (Nat.le_of_lt hj)) :
    A.actualLinearMap v x j = A.actualLinearMap u x j := by
  simp only [actualLinearMap, dif_pos hj]
  exact congrArg ComplexAffineObservation.linear (A.actualObservation_eq_of_prefix_eq ⟨j, hj⟩ heq)

/-- The remaining complex direction space is constant along a prefix fibre. -/
theorem ComplexAffineAlgorithm.direction_eq_of_prefix_eq {n : ℕ}
    (A : ComplexAffineAlgorithm E n) {u v : E} {x : ℂ} {j : ℕ} (hj : j ≤ n)
    (heq : A.prefix v x j hj = A.prefix u x j hj) :
    A.direction v x j = A.direction u x j := by
  ext h
  simp only [direction, mem_scalarPrefixKernel]
  have hrows (i : ℕ) (hi : i < j) : A.actualLinearMap v x i = A.actualLinearMap u x i :=
    A.actualLinearMap_eq_of_prefix_eq (lt_of_lt_of_le hi hj)
      (A.prefix_eq_of_later_prefix_eq (Nat.le_of_lt hi) hj heq)
  constructor
  · intro hv i hi
    rw [← hrows i hi]
    exact hv i hi
  · intro hu i hi
    rw [hrows i hi]
    exact hu i hi

/-- One additional complex scalar answer intersects with one complex linear kernel. -/
theorem ComplexAffineAlgorithm.direction_succ {n : ℕ} (A : ComplexAffineAlgorithm E n)
    (u : E) (x : ℂ) (j : ℕ) :
    A.direction u x (j + 1) = A.direction u x j ⊓ (A.actualLinearMap u x j).ker :=
  scalarPrefixKernel_succ _ _

/-- The same one-row intersection holds after changing centre within the old fibre. -/
theorem ComplexAffineAlgorithm.direction_succ_of_prefix_eq {n : ℕ}
    (A : ComplexAffineAlgorithm E n) {u v : E} {x : ℂ} {j : ℕ} (hj : j < n)
    (heq : A.prefix v x j (Nat.le_of_lt hj) = A.prefix u x j (Nat.le_of_lt hj)) :
    A.direction v x (j + 1) = A.direction u x j ⊓ (A.actualLinearMap u x j).ker := by
  rw [A.direction_succ, A.direction_eq_of_prefix_eq (Nat.le_of_lt hj) heq,
    A.actualLinearMap_eq_of_prefix_eq hj heq]

/-- Before any observation every parameter direction remains possible. -/
theorem ComplexAffineAlgorithm.direction_zero {n : ℕ} (A : ComplexAffineAlgorithm E n)
    (u : E) (x : ℂ) : A.direction u x 0 = ⊤ :=
  scalarPrefixKernel_zero _

/-- Along an actual execution the remaining complex direction spaces are nested. -/
theorem ComplexAffineAlgorithm.direction_antitone {n : ℕ} (A : ComplexAffineAlgorithm E n)
    (u : E) (x : ℂ) : Antitone (A.direction u x) :=
  scalarPrefixKernel_antitone _

/-- Rank of the actual complex observation map for a fixed prefix. -/
def ComplexAffineAlgorithm.informationRank {n : ℕ} (A : ComplexAffineAlgorithm E n)
    (u : E) (x : ℂ) (j : ℕ) : ℕ :=
  scalarPrefixRank (A.actualLinearMap u x) j

section FiniteDimension

variable [FiniteDimensional ℂ E]

/-- Exact complex rank-nullity for the rows that the rules actually selected. -/
theorem ComplexAffineAlgorithm.rank_add_finrank_direction {n : ℕ}
    (A : ComplexAffineAlgorithm E n) (u : E) (x : ℂ) (j : ℕ) :
    A.informationRank u x j + Module.finrank ℂ (A.direction u x j) =
      Module.finrank ℂ E :=
  scalarPrefixRank_add_finrank_kernel _ _

/-- One complex scalar observation increases complex rank by at most one. -/
theorem ComplexAffineAlgorithm.informationRank_succ_le {n : ℕ}
    (A : ComplexAffineAlgorithm E n) (u : E) (x : ℂ) (j : ℕ) :
    A.informationRank u x (j + 1) ≤ A.informationRank u x j + 1 :=
  scalarPrefixRank_succ_le _ _

/-- At most `j` complex scalar constraints have complex rank at most `j`. -/
theorem ComplexAffineAlgorithm.informationRank_le_length {n : ℕ}
    (A : ComplexAffineAlgorithm E n) (u : E) (x : ℂ) (j : ℕ) :
    A.informationRank u x j ≤ j :=
  scalarPrefixRank_le_length _ _

/-- The remaining direction space loses at most one complex dimension per answer. -/
theorem ComplexAffineAlgorithm.finrank_sub_direction_le {n : ℕ}
    (A : ComplexAffineAlgorithm E n) (u : E) (x : ℂ) (j : ℕ) :
    Module.finrank ℂ E - Module.finrank ℂ (A.direction u x j) ≤ j := by
  have hdim := A.rank_add_finrank_direction u x j
  have hrank := A.informationRank_le_length u x j
  omega

/-- Equivalent lower bound on the dimension of the actual remaining directions. -/
theorem ComplexAffineAlgorithm.finrank_direction_ge {n : ℕ}
    (A : ComplexAffineAlgorithm E n) (u : E) (x : ℂ) (j : ℕ) :
    Module.finrank ℂ E - j ≤ Module.finrank ℂ (A.direction u x j) := by
  have hdim := A.rank_add_finrank_direction u x j
  have hrank := A.informationRank_le_length u x j
  omega

end FiniteDimension

/-- The derivative query selected along the actual complex execution. -/
def ComplexAlgorithm.actualQuery {n : ℕ} (A : ComplexAlgorithm n) (f : ℂ → ℂ)
    (x : ℂ) (j : Fin n) : ComplexQuery :=
  A.query j x (A.prefix f x j.val (Nat.le_of_lt j.isLt))

/-- A derivative query has its specified complex location; an idle slot has none. -/
def ComplexQuery.location : ComplexQuery → Option ℂ
  | .derivative z _ => some z
  | .idle => none

/-- Restrict a complex-oracle algorithm to affine observations of a parameter family. -/
def ComplexAlgorithm.toAffine {n : ℕ} (A : ComplexAlgorithm n)
    (observe : ComplexQuery → ComplexAffineObservation E) : ComplexAffineAlgorithm E n where
  query j x previous := observe (A.query j x previous)
  output := A.output

/-- An affine representation of query answers preserves every prefix. -/
theorem ComplexAlgorithm.toAffine_prefix_eq {n : ℕ} (A : ComplexAlgorithm n)
    (observe : ComplexQuery → ComplexAffineObservation E) {u : E} {f : ℂ → ℂ}
    (hanswer : ∀ q, (observe q).answer u = q.answer f)
    (x : ℂ) (j : ℕ) (hj : j ≤ n) :
    (A.toAffine observe).prefix u x j hj = A.prefix f x j hj := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hlt : j < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hj
    have hprev := ih (Nat.le_of_lt hlt)
    simp only [toAffine] at hprev
    simp only [ComplexAffineAlgorithm.prefix, ComplexAlgorithm.prefix, toAffine]
    rw [hprev]
    exact Fin.snoc_inj.mpr ⟨rfl, hanswer _⟩

/-- The faithful representation preserves the complex algorithm's exact output. -/
theorem ComplexAlgorithm.toAffine_run_eq {n : ℕ} (A : ComplexAlgorithm n)
    (observe : ComplexQuery → ComplexAffineObservation E) {u : E} {f : ℂ → ℂ}
    (hanswer : ∀ q, (observe q).answer u = q.answer f) (x : ℂ) :
    (A.toAffine observe).run u x = A.run f x :=
  congrArg (A.output x) (A.toAffine_prefix_eq observe hanswer x n le_rfl)

/-- Faithful observation locations remain the actual complex derivative-query locations. -/
theorem ComplexAlgorithm.toAffine_actual_location_eq {n : ℕ} (A : ComplexAlgorithm n)
    (observe : ComplexQuery → ComplexAffineObservation E) {u : E} {f : ℂ → ℂ}
    (hanswer : ∀ q, (observe q).answer u = q.answer f)
    (hlocation : ∀ q, (observe q).location = q.location) (x : ℂ) (j : Fin n) :
    ((A.toAffine observe).actualObservation u x j).location =
      (A.actualQuery f x j).location := by
  have hprev := A.toAffine_prefix_eq observe hanswer x j.val (Nat.le_of_lt j.isLt)
  simp only [toAffine] at hprev
  simp only [ComplexAffineAlgorithm.actualObservation, toAffine]
  rw [hprev]
  exact hlocation _

end KungTraubAppendices
