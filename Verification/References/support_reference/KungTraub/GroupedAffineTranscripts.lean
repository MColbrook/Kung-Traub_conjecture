import support_reference.KungTraub.AffineTranscripts
import support_reference.KungTraub.GroupedIndexing

/-!
# Affine observations in prescribed groups

All observations in a group are selected from the complete earlier groups,
before any answer in that group. The direction after j groups is the common
kernel of the scalar rows through N_j and equals the direction of the
group-prefix fibre.
-/

noncomputable section
namespace KungTraub
variable (E : Type*) [AddCommGroup E] [Module ℝ E]

structure GroupedAffineAlgorithm {k : ℕ} (sizes : Fin k → ℕ) where
  query : (j : Fin k) → ℝ → GroupPrefix sizes j.val (Nat.le_of_lt j.isLt) →
    (Fin (sizes j) → AffineObservation E)
  output : ℝ → GroupPrefix sizes k le_rfl → ℝ

variable {E}

def GroupedAffineAlgorithm.prefix {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm E sizes) (u : E) (x : ℝ) :
    (j : ℕ) → (hj : j ≤ k) → GroupPrefix sizes j hj
  | 0, _ => fun i => Fin.elim0 i
  | j + 1, hj =>
      let hlt : j < k := Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hj
      let previous := A.prefix u x j (Nat.le_of_lt hlt)
      let queries := A.query ⟨j, hlt⟩ x previous
      fun i => Fin.lastCases (fun slot => (queries slot).answer u) (fun h => previous h) i

def GroupedAffineAlgorithm.run {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm E sizes) (u : E) (x : ℝ) : ℝ :=
  A.output x (A.prefix u x k le_rfl)

def GroupedAffineAlgorithm.actualObservations {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm E sizes) (u : E) (x : ℝ) (g : Fin k) :
    Fin (sizes g) → AffineObservation E :=
  A.query g x (A.prefix u x g.val (Nat.le_of_lt g.isLt))

/-- Scalar rows ordered by group, with every row in a group selected before its answers. -/
def GroupedAffineAlgorithm.actualLinearMap {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm E sizes) (u : E) (x : ℝ) (t : ℕ) : E →ₗ[ℝ] ℝ :=
  if ht : t < groupedObservationCount sizes then
    let pair := (groupSlotEquiv sizes).symm ⟨t, ht⟩
    (A.actualObservations u x pair.1 pair.2).linear
  else 0

def GroupedAffineAlgorithm.direction {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm E sizes) (u : E) (x : ℝ) (j : ℕ) : Submodule ℝ E :=
  scalarPrefixKernel (A.actualLinearMap u x) (groupedPrefixCount sizes j)

theorem GroupedAffineAlgorithm.actualLinearMap_groupSlotEquiv {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm E sizes) (u : E) (x : ℝ)
    (g : Fin k) (slot : Fin (sizes g)) :
    A.actualLinearMap u x (groupSlotEquiv sizes ⟨g, slot⟩).val =
      (A.actualObservations u x g slot).linear := by
  sorry

theorem GroupedAffineAlgorithm.prefix_eq_iff_group_equations {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm E sizes) (u v : E) (x : ℝ) (j : ℕ) (hj : j ≤ k) :
    A.prefix v x j hj = A.prefix u x j hj ↔
      ∀ g : Fin k, g.val < j → ∀ slot, (A.actualObservations u x g slot).linear (v - u) = 0 := by
  sorry

theorem GroupedAffineAlgorithm.prefix_eq_iff_scalar_equations {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm E sizes) (u v : E) (x : ℝ) (j : ℕ) (hj : j ≤ k) :
    A.prefix v x j hj = A.prefix u x j hj ↔
      ∀ t < groupedPrefixCount sizes j, A.actualLinearMap u x t (v - u) = 0 := by
  sorry

theorem GroupedAffineAlgorithm.prefix_eq_iff_sub_mem_direction {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm E sizes) (u v : E) (x : ℝ) (j : ℕ) (hj : j ≤ k) :
    A.prefix v x j hj = A.prefix u x j hj ↔ v - u ∈ A.direction u x j := by
  sorry

theorem GroupedAffineAlgorithm.prefix_eq_of_later_prefix_eq {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm E sizes) {u v : E} {x : ℝ} {i j : ℕ}
    (hij : i ≤ j) (hjk : j ≤ k)
    (heq : A.prefix v x j hjk = A.prefix u x j hjk) :
    A.prefix v x i (hij.trans hjk) = A.prefix u x i (hij.trans hjk) := by
  sorry

theorem GroupedAffineAlgorithm.actualObservations_eq_of_prefix_eq {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm E sizes) {u v : E} {x : ℝ} (g : Fin k)
    (heq : A.prefix v x g.val g.isLt.le = A.prefix u x g.val g.isLt.le) :
    A.actualObservations v x g = A.actualObservations u x g := by
  sorry

theorem GroupedAffineAlgorithm.actualLinearMap_eq_of_prefix_eq {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm E sizes) {u v : E} {x : ℝ} {j t : ℕ} (hj : j ≤ k)
    (ht : t < groupedObservationCount sizes) (hgroup : scalarGroupAt sizes t ≤ j)
    (heq : A.prefix v x j hj = A.prefix u x j hj) :
    A.actualLinearMap v x t = A.actualLinearMap u x t := by
  sorry

theorem GroupedAffineAlgorithm.direction_eq_of_prefix_eq {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm E sizes) {u v : E} {x : ℝ} {j : ℕ} (hj : j ≤ k)
    (heq : A.prefix v x j hj = A.prefix u x j hj) :
    A.direction v x j = A.direction u x j := by
  sorry

theorem GroupedAffineAlgorithm.direction_antitone {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm E sizes) (u : E) (x : ℝ) : Antitone (A.direction u x) := by
  sorry

theorem GroupedAffineAlgorithm.direction_zero {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm E sizes) (u : E) (x : ℝ) : A.direction u x 0 = ⊤ := by
  sorry

theorem GroupedAffineAlgorithm.mem_direction_iff_group_equations {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm E sizes) (u h : E) (x : ℝ) (j : ℕ) (hj : j ≤ k) :
    h ∈ A.direction u x j ↔
      ∀ g : Fin k, g.val < j → ∀ slot, (A.actualObservations u x g slot).linear h = 0 := by
  sorry

/-- All kernels in the current group are intersected at once. -/
theorem GroupedAffineAlgorithm.direction_succ {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm E sizes) (u : E) (x : ℝ) {j : ℕ} (hj : j < k) :
    A.direction u x (j + 1) = A.direction u x j ⊓
      ⨅ slot : Fin (sizes ⟨j, hj⟩), (A.actualObservations u x ⟨j, hj⟩ slot).linear.ker := by
  sorry

theorem GroupedAffineAlgorithm.direction_succ_of_prefix_eq {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm E sizes) {u v : E} {x : ℝ} {j : ℕ} (hj : j < k)
    (heq : A.prefix v x j hj.le = A.prefix u x j hj.le) :
    A.direction v x (j + 1) = A.direction u x j ⊓
      ⨅ slot : Fin (sizes ⟨j, hj⟩), (A.actualObservations u x ⟨j, hj⟩ slot).linear.ker := by
  sorry

theorem GroupedAffineAlgorithm.run_eq_of_sub_mem_direction {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm E sizes) (u v : E) (x : ℝ)
    (h : v - u ∈ A.direction u x k) : A.run v x = A.run u x := by
  sorry

/-- Restriction to an affine family preserves the actual group schedule. -/
def GroupedRealAlgorithm.toAffine {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedRealAlgorithm sizes) (observe : RealQuery → AffineObservation E) :
    GroupedAffineAlgorithm E sizes where
  query j x previous slot := observe (A.query j x previous slot)
  output := A.output

theorem GroupedRealAlgorithm.toAffine_prefix_eq {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedRealAlgorithm sizes) (observe : RealQuery → AffineObservation E)
    {u : E} {f : ℝ → ℝ} (hanswer : ∀ q, (observe q).answer u = q.answer f)
    (x : ℝ) (j : ℕ) (hj : j ≤ k) :
    (A.toAffine observe).prefix u x j hj = A.prefix f x j hj := by
  sorry

theorem GroupedRealAlgorithm.toAffine_run_eq {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedRealAlgorithm sizes) (observe : RealQuery → AffineObservation E)
    {u : E} {f : ℝ → ℝ} (hanswer : ∀ q, (observe q).answer u = q.answer f) (x : ℝ) :
    (A.toAffine observe).run u x = A.run f x := by
  sorry

theorem GroupedRealAlgorithm.toAffine_actual_location_eq {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedRealAlgorithm sizes) (observe : RealQuery → AffineObservation E)
    {u : E} {f : ℝ → ℝ} (hanswer : ∀ q, (observe q).answer u = q.answer f)
    (hlocation : ∀ q, (observe q).location = q.location) (x : ℝ)
    (g : Fin k) (slot : Fin (sizes g)) :
    ((A.toAffine observe).actualObservations u x g slot).location =
      (A.actualQueries f x g slot).location := by
  sorry

end KungTraub
