import KungTraub.Transcripts
import KungTraub.PolynomialInformation

/-!
# Affine fibres of adaptive observations

The fixed-scale argument restricts linear observations of functions to an affine
family indexed by real parameters. Decision rules remain arbitrary. Along an
actual execution, the parameters with the same prefix form exactly the translate
of the common kernel of the rows selected during that execution.

The optional location allows the finite-scale construction to avoid the query
point when an affine observation comes from derivative evaluation. It plays no
role in the affine equations. Mathlib supplies linear-map kernels and finite
tuple extension; no continuity of decision or output rules is assumed.
-/

noncomputable section

namespace KungTraub

variable (E : Type*) [AddCommGroup E] [Module ℝ E]

structure AffineObservation where
  linear : E →ₗ[ℝ] ℝ
  offset : ℝ
  location : Option ℝ

variable {E}

def AffineObservation.answer (q : AffineObservation E) (u : E) : ℝ :=
  q.offset + q.linear u

theorem AffineObservation.answer_eq_iff (q : AffineObservation E) (u v : E) :
    q.answer v = q.answer u ↔ q.linear (v - u) = 0 := by
  simp only [answer, map_sub, sub_eq_zero, add_right_inj]

variable (E)

structure AffineAlgorithm (n : ℕ) where
  query : (j : Fin n) → ℝ → (Fin j.val → ℝ) → AffineObservation E
  output : ℝ → (Fin n → ℝ) → ℝ

variable {E}

def AffineAlgorithm.prefix {n : ℕ} (A : AffineAlgorithm E n) (u : E) (x : ℝ) :
    (j : ℕ) → j ≤ n → (Fin j → ℝ)
  | 0, _ => Fin.elim0
  | j + 1, hj =>
      let hlt : j < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hj
      let previous := A.prefix u x j (Nat.le_of_lt hlt)
      Fin.snoc previous ((A.query ⟨j, hlt⟩ x previous).answer u)

def AffineAlgorithm.run {n : ℕ} (A : AffineAlgorithm E n) (u : E) (x : ℝ) : ℝ :=
  A.output x (A.prefix u x n le_rfl)

def AffineAlgorithm.actualObservation {n : ℕ} (A : AffineAlgorithm E n)
    (u : E) (x : ℝ) (j : Fin n) : AffineObservation E :=
  A.query j x (A.prefix u x j.val (Nat.le_of_lt j.isLt))

/-- The prefix map is extended by zero beyond the query budget. -/
def AffineAlgorithm.actualLinearMap {n : ℕ} (A : AffineAlgorithm E n)
    (u : E) (x : ℝ) (j : ℕ) : E →ₗ[ℝ] ℝ :=
  if hj : j < n then (A.actualObservation u x ⟨j, hj⟩).linear else 0

def AffineAlgorithm.direction {n : ℕ} (A : AffineAlgorithm E n)
    (u : E) (x : ℝ) (j : ℕ) : Submodule ℝ E :=
  scalarPrefixKernel (A.actualLinearMap u x) j

theorem AffineAlgorithm.prefix_eq_iff_linear_equations {n : ℕ}
    (A : AffineAlgorithm E n) (u v : E) (x : ℝ) (j : ℕ) (hj : j ≤ n) :
    A.prefix v x j hj = A.prefix u x j hj ↔
      ∀ i < j, A.actualLinearMap u x i (v - u) = 0 := by
  induction j with
  | zero => simp [AffineAlgorithm.prefix]
  | succ j ih =>
    have hlt : j < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hj
    have hjn : j ≤ n := Nat.le_of_lt hlt
    constructor
    · intro h
      simp only [AffineAlgorithm.prefix] at h
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
      simp only [AffineAlgorithm.prefix]
      rw [hp]
      apply Fin.snoc_inj.mpr
      refine ⟨rfl, ?_⟩
      apply ((A.actualObservation u x ⟨j, hlt⟩).answer_eq_iff u v).mpr
      simpa only [actualLinearMap, dif_pos hlt] using h j (Nat.lt_succ_self j)

theorem AffineAlgorithm.prefix_eq_iff_sub_mem_direction {n : ℕ}
    (A : AffineAlgorithm E n) (u v : E) (x : ℝ) (j : ℕ) (hj : j ≤ n) :
    A.prefix v x j hj = A.prefix u x j hj ↔ v - u ∈ A.direction u x j := by
  rw [prefix_eq_iff_linear_equations, direction, mem_scalarPrefixKernel]

theorem AffineAlgorithm.prefix_add_eq_of_mem_direction {n : ℕ}
    (A : AffineAlgorithm E n) (u h : E) (x : ℝ) (j : ℕ) (hj : j ≤ n)
    (hh : h ∈ A.direction u x j) :
    A.prefix (u + h) x j hj = A.prefix u x j hj := by
  apply (A.prefix_eq_iff_sub_mem_direction u (u + h) x j hj).mpr
  simpa only [add_sub_cancel_left] using hh

theorem AffineAlgorithm.run_add_eq_of_mem_direction {n : ℕ}
    (A : AffineAlgorithm E n) (u h : E) (x : ℝ) (hh : h ∈ A.direction u x n) :
    A.run (u + h) x = A.run u x :=
  congrArg (A.output x) (A.prefix_add_eq_of_mem_direction u h x n le_rfl hh)

theorem AffineAlgorithm.prefix_eq_of_later_prefix_eq {n : ℕ}
    (A : AffineAlgorithm E n) {u v : E} {x : ℝ} {j k : ℕ} (hjk : j ≤ k) (hkn : k ≤ n)
    (heq : A.prefix v x k hkn = A.prefix u x k hkn) :
    A.prefix v x j (hjk.trans hkn) = A.prefix u x j (hjk.trans hkn) := by
  rw [prefix_eq_iff_linear_equations] at heq ⊢
  exact fun i hi => heq i (lt_of_lt_of_le hi hjk)

theorem AffineAlgorithm.actualObservation_eq_of_prefix_eq {n : ℕ}
    (A : AffineAlgorithm E n) {u v : E} {x : ℝ} (j : Fin n)
    (heq : A.prefix v x j.val (Nat.le_of_lt j.isLt) =
      A.prefix u x j.val (Nat.le_of_lt j.isLt)) :
    A.actualObservation v x j = A.actualObservation u x j :=
  congrArg (A.query j x) heq

theorem AffineAlgorithm.actualLinearMap_eq_of_prefix_eq {n : ℕ}
    (A : AffineAlgorithm E n) {u v : E} {x : ℝ} {j : ℕ} (hj : j < n)
    (heq : A.prefix v x j (Nat.le_of_lt hj) = A.prefix u x j (Nat.le_of_lt hj)) :
    A.actualLinearMap v x j = A.actualLinearMap u x j := by
  simp only [actualLinearMap, dif_pos hj]
  exact congrArg AffineObservation.linear (A.actualObservation_eq_of_prefix_eq ⟨j, hj⟩ heq)

theorem AffineAlgorithm.direction_eq_of_prefix_eq {n : ℕ}
    (A : AffineAlgorithm E n) {u v : E} {x : ℝ} {j : ℕ} (hj : j ≤ n)
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

theorem AffineAlgorithm.direction_succ {n : ℕ} (A : AffineAlgorithm E n)
    (u : E) (x : ℝ) (j : ℕ) :
    A.direction u x (j + 1) = A.direction u x j ⊓ (A.actualLinearMap u x j).ker :=
  scalarPrefixKernel_succ _ _

theorem AffineAlgorithm.direction_succ_of_prefix_eq {n : ℕ}
    (A : AffineAlgorithm E n) {u v : E} {x : ℝ} {j : ℕ} (hj : j < n)
    (heq : A.prefix v x j (Nat.le_of_lt hj) = A.prefix u x j (Nat.le_of_lt hj)) :
    A.direction v x (j + 1) = A.direction u x j ⊓ (A.actualLinearMap u x j).ker := by
  rw [A.direction_succ, A.direction_eq_of_prefix_eq (Nat.le_of_lt hj) heq,
    A.actualLinearMap_eq_of_prefix_eq hj heq]

def RealQuery.location : RealQuery → Option ℝ
  | .derivative z _ => some z
  | .idle => none

/-- Restrict a real-oracle algorithm to affine observations of a parameter family. -/
def RealAlgorithm.toAffine {n : ℕ} (A : RealAlgorithm n)
    (observe : RealQuery → AffineObservation E) : AffineAlgorithm E n where
  query j x previous := observe (A.query j x previous)
  output := A.output

theorem RealAlgorithm.toAffine_prefix_eq {n : ℕ} (A : RealAlgorithm n)
    (observe : RealQuery → AffineObservation E) {u : E} {f : ℝ → ℝ}
    (hanswer : ∀ q, (observe q).answer u = q.answer f)
    (x : ℝ) (j : ℕ) (hj : j ≤ n) :
    (A.toAffine observe).prefix u x j hj = A.prefix f x j hj := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hlt : j < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hj
    have hprev := ih (Nat.le_of_lt hlt)
    simp only [toAffine] at hprev
    simp only [AffineAlgorithm.prefix, RealAlgorithm.prefix, toAffine]
    rw [hprev]
    exact Fin.snoc_inj.mpr ⟨rfl, hanswer _⟩

theorem RealAlgorithm.toAffine_run_eq {n : ℕ} (A : RealAlgorithm n)
    (observe : RealQuery → AffineObservation E) {u : E} {f : ℝ → ℝ}
    (hanswer : ∀ q, (observe q).answer u = q.answer f) (x : ℝ) :
    (A.toAffine observe).run u x = A.run f x :=
  congrArg (A.output x) (A.toAffine_prefix_eq observe hanswer x n le_rfl)

theorem RealAlgorithm.toAffine_actual_location_eq {n : ℕ} (A : RealAlgorithm n)
    (observe : RealQuery → AffineObservation E) {u : E} {f : ℝ → ℝ}
    (hanswer : ∀ q, (observe q).answer u = q.answer f)
    (hlocation : ∀ q, (observe q).location = q.location) (x : ℝ) (j : Fin n) :
    ((A.toAffine observe).actualObservation u x j).location =
      (A.actualQuery f x j).location := by
  have hprev := A.toAffine_prefix_eq observe hanswer x j.val (Nat.le_of_lt j.isLt)
  simp only [toAffine] at hprev
  simp only [AffineAlgorithm.actualObservation, toAffine]
  rw [hprev]
  exact hlocation _

end KungTraub
