import KungTraub.AffineTranscripts

/-!
# Restriction of linear observations to an affine family

The finite adversary allows arbitrary scalar linear functionals on a common real
vector space. Restricting such an observation to base + P(u) gives precisely an
affine observation of the parameter u. The following identities preserve the
entire adaptive execution. They also cover affine functionals, so the linear
case requires no additional assumption.
-/

noncomputable section

namespace KungTraub

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

def AffineObservation.restrict (q : AffineObservation F) (base : F) (P : E →ₗ[ℝ] F) :
    AffineObservation E where
  linear := q.linear.comp P
  offset := q.offset + q.linear base
  location := q.location

theorem AffineObservation.restrict_answer (q : AffineObservation F)
    (base : F) (P : E →ₗ[ℝ] F) (u : E) :
    (q.restrict base P).answer u = q.answer (base + P u) := by
  simp [restrict, answer, map_add, add_assoc]

def AffineAlgorithm.restrict {n : ℕ} (A : AffineAlgorithm F n)
    (base : F) (P : E →ₗ[ℝ] F) : AffineAlgorithm E n where
  query j x previous := (A.query j x previous).restrict base P
  output := A.output

theorem AffineAlgorithm.restrict_prefix_eq {n : ℕ} (A : AffineAlgorithm F n)
    (base : F) (P : E →ₗ[ℝ] F) (u : E) (x : ℝ) (j : ℕ) (hj : j ≤ n) :
    (A.restrict base P).prefix u x j hj = A.prefix (base + P u) x j hj := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hlt : j < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hj
    have hprev := ih (Nat.le_of_lt hlt)
    simp only [restrict] at hprev
    simp only [AffineAlgorithm.prefix, restrict]
    rw [hprev]
    exact Fin.snoc_inj.mpr ⟨rfl, AffineObservation.restrict_answer _ base P u⟩

theorem AffineAlgorithm.restrict_run_eq {n : ℕ} (A : AffineAlgorithm F n)
    (base : F) (P : E →ₗ[ℝ] F) (u : E) (x : ℝ) :
    (A.restrict base P).run u x = A.run (base + P u) x :=
  congrArg (A.output x) (A.restrict_prefix_eq base P u x n le_rfl)

theorem AffineAlgorithm.restrict_actual_location_eq {n : ℕ} (A : AffineAlgorithm F n)
    (base : F) (P : E →ₗ[ℝ] F) (u : E) (x : ℝ) (j : Fin n) :
    ((A.restrict base P).actualObservation u x j).location =
      (A.actualObservation (base + P u) x j).location := by
  have hprev := A.restrict_prefix_eq base P u x j.val (Nat.le_of_lt j.isLt)
  simp only [restrict] at hprev
  simp only [actualObservation, restrict]
  rw [hprev]
  rfl

end KungTraub
