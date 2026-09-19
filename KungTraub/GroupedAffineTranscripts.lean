import KungTraub.AffineTranscripts
import KungTraub.GroupedIndexing

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
  simp only [actualLinearMap, dif_pos (groupSlotEquiv sizes ⟨g, slot⟩).isLt]
  exact congrArg (fun pair : (g : Fin k) × Fin (sizes g) =>
    (A.actualObservations u x pair.1 pair.2).linear)
    ((groupSlotEquiv sizes).symm_apply_apply ⟨g, slot⟩)

theorem GroupedAffineAlgorithm.prefix_eq_iff_group_equations {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm E sizes) (u v : E) (x : ℝ) (j : ℕ) (hj : j ≤ k) :
    A.prefix v x j hj = A.prefix u x j hj ↔
      ∀ g : Fin k, g.val < j → ∀ slot, (A.actualObservations u x g slot).linear (v - u) = 0 := by
  induction j with
  | zero => simp [GroupedAffineAlgorithm.prefix]
  | succ j ih =>
    have hlt : j < k := by omega
    constructor
    · intro h
      have hprev : A.prefix v x j hlt.le = A.prefix u x j hlt.le := by
        funext i slot
        have hi := congrFun (congrFun h i.castSucc) slot
        simpa only [GroupedAffineAlgorithm.prefix, Fin.lastCases_castSucc] using hi
      have hrows := (ih hlt.le).mp hprev
      intro g hg slot
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hg) with hgj | hgj
      · exact hrows g hgj slot
      · have hgeq : g = ⟨j, hlt⟩ := Fin.ext hgj
        subst g
        have hlast := congrFun (congrFun h (Fin.last j)) slot
        simp only [GroupedAffineAlgorithm.prefix, Fin.lastCases_last] at hlast
        rw [hprev] at hlast
        exact ((A.actualObservations u x ⟨j, hlt⟩ slot).answer_eq_iff u v).mp hlast
    · intro h
      have hprev := (ih hlt.le).mpr (fun g hg => h g (Nat.lt_succ_of_lt hg))
      simp only [GroupedAffineAlgorithm.prefix]
      rw [hprev]
      funext i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · funext slot
        simp only [Fin.lastCases_last]
        exact ((A.actualObservations u x ⟨j, hlt⟩ slot).answer_eq_iff u v).mpr
          (h ⟨j, hlt⟩ (Nat.lt_succ_self j) slot)
      · simp only [Fin.lastCases_castSucc]

theorem GroupedAffineAlgorithm.prefix_eq_iff_scalar_equations {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm E sizes) (u v : E) (x : ℝ) (j : ℕ) (hj : j ≤ k) :
    A.prefix v x j hj = A.prefix u x j hj ↔
      ∀ t < groupedPrefixCount sizes j, A.actualLinearMap u x t (v - u) = 0 := by
  rw [A.prefix_eq_iff_group_equations]
  constructor
  · intro h t ht
    have htotal : t < groupedObservationCount sizes :=
      ht.trans_le (groupedPrefixCount_le_total sizes hj)
    obtain ⟨pair, heq⟩ := (groupSlotEquiv sizes).surjective ⟨t, htotal⟩
    have hval : (groupSlotEquiv sizes pair).val = t := congrArg Fin.val heq
    have hg : pair.1.val < j := (groupSlotEquiv_lt_prefix_iff sizes pair.1 pair.2 hj).mp
      (by simpa only [hval] using ht)
    rw [← hval, A.actualLinearMap_groupSlotEquiv]
    exact h pair.1 hg pair.2
  · intro h g hg slot
    have ht := (groupSlotEquiv_lt_prefix_iff sizes g slot hj).mpr hg
    have heq := h _ ht
    rwa [A.actualLinearMap_groupSlotEquiv] at heq

theorem GroupedAffineAlgorithm.prefix_eq_iff_sub_mem_direction {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm E sizes) (u v : E) (x : ℝ) (j : ℕ) (hj : j ≤ k) :
    A.prefix v x j hj = A.prefix u x j hj ↔ v - u ∈ A.direction u x j := by
  rw [A.prefix_eq_iff_scalar_equations, direction, mem_scalarPrefixKernel]

theorem GroupedAffineAlgorithm.prefix_eq_of_later_prefix_eq {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm E sizes) {u v : E} {x : ℝ} {i j : ℕ}
    (hij : i ≤ j) (hjk : j ≤ k)
    (heq : A.prefix v x j hjk = A.prefix u x j hjk) :
    A.prefix v x i (hij.trans hjk) = A.prefix u x i (hij.trans hjk) := by
  rw [A.prefix_eq_iff_group_equations] at heq ⊢
  exact fun g hg => heq g (hg.trans_le hij)

theorem GroupedAffineAlgorithm.actualObservations_eq_of_prefix_eq {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm E sizes) {u v : E} {x : ℝ} (g : Fin k)
    (heq : A.prefix v x g.val g.isLt.le = A.prefix u x g.val g.isLt.le) :
    A.actualObservations v x g = A.actualObservations u x g :=
  congrArg (A.query g x) heq

theorem GroupedAffineAlgorithm.actualLinearMap_eq_of_prefix_eq {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm E sizes) {u v : E} {x : ℝ} {j t : ℕ} (hj : j ≤ k)
    (ht : t < groupedObservationCount sizes) (hgroup : scalarGroupAt sizes t ≤ j)
    (heq : A.prefix v x j hj = A.prefix u x j hj) :
    A.actualLinearMap v x t = A.actualLinearMap u x t := by
  obtain ⟨pair, hp⟩ := (groupSlotEquiv sizes).surjective ⟨t, ht⟩
  have hval : (groupSlotEquiv sizes pair).val = t := congrArg Fin.val hp
  have hgj : pair.1.val ≤ j := by
    rw [← hval, scalarGroupAt_groupSlotEquiv] at hgroup
    exact hgroup
  rw [← hval, A.actualLinearMap_groupSlotEquiv, A.actualLinearMap_groupSlotEquiv]
  rw [A.actualObservations_eq_of_prefix_eq pair.1 (A.prefix_eq_of_later_prefix_eq hgj hj heq)]

theorem GroupedAffineAlgorithm.direction_eq_of_prefix_eq {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm E sizes) {u v : E} {x : ℝ} {j : ℕ} (hj : j ≤ k)
    (heq : A.prefix v x j hj = A.prefix u x j hj) :
    A.direction v x j = A.direction u x j := by
  ext h
  simp only [direction, mem_scalarPrefixKernel]
  have hrows (t : ℕ) (ht : t < groupedPrefixCount sizes j) :
      A.actualLinearMap v x t = A.actualLinearMap u x t := by
    have htn := ht.trans_le (groupedPrefixCount_le_total sizes hj)
    have hg := (scalarGroupAt_lt_prefix_iff sizes ⟨t, htn⟩ hj).mpr ht
    exact A.actualLinearMap_eq_of_prefix_eq hj htn hg.le heq
  constructor
  · intro hv t ht
    rw [← hrows t ht]
    exact hv t ht
  · intro hu t ht
    rw [hrows t ht]
    exact hu t ht

theorem GroupedAffineAlgorithm.direction_antitone {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm E sizes) (u : E) (x : ℝ) : Antitone (A.direction u x) := by
  intro i j hij
  exact scalarPrefixKernel_antitone _ (groupedPrefixCount_mono sizes hij)

theorem GroupedAffineAlgorithm.direction_zero {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm E sizes) (u : E) (x : ℝ) : A.direction u x 0 = ⊤ := by
  simp only [direction, groupedPrefixCount_zero, scalarPrefixKernel_zero]

theorem GroupedAffineAlgorithm.mem_direction_iff_group_equations {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm E sizes) (u h : E) (x : ℝ) (j : ℕ) (hj : j ≤ k) :
    h ∈ A.direction u x j ↔
      ∀ g : Fin k, g.val < j → ∀ slot, (A.actualObservations u x g slot).linear h = 0 := by
  have heq := A.prefix_eq_iff_sub_mem_direction u (u + h) x j hj
  rw [A.prefix_eq_iff_group_equations] at heq
  simpa only [add_sub_cancel_left] using heq.symm

/-- All kernels in the current group are intersected at once. -/
theorem GroupedAffineAlgorithm.direction_succ {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm E sizes) (u : E) (x : ℝ) {j : ℕ} (hj : j < k) :
    A.direction u x (j + 1) = A.direction u x j ⊓
      ⨅ slot : Fin (sizes ⟨j, hj⟩), (A.actualObservations u x ⟨j, hj⟩ slot).linear.ker := by
  ext h
  rw [A.mem_direction_iff_group_equations u h x (j + 1) (Nat.succ_le_of_lt hj),
    Submodule.mem_inf, A.mem_direction_iff_group_equations u h x j hj.le]
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro hall
    exact ⟨fun g hg => hall g (Nat.lt_succ_of_lt hg), fun slot => hall ⟨j, hj⟩ (Nat.lt_succ_self j) slot⟩
  · rintro ⟨hold, hnew⟩ g hg slot
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hg) with hgj | hgj
    · exact hold g hgj slot
    · have heq : g = ⟨j, hj⟩ := Fin.ext hgj
      subst g
      exact hnew slot

theorem GroupedAffineAlgorithm.direction_succ_of_prefix_eq {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm E sizes) {u v : E} {x : ℝ} {j : ℕ} (hj : j < k)
    (heq : A.prefix v x j hj.le = A.prefix u x j hj.le) :
    A.direction v x (j + 1) = A.direction u x j ⊓
      ⨅ slot : Fin (sizes ⟨j, hj⟩), (A.actualObservations u x ⟨j, hj⟩ slot).linear.ker := by
  rw [A.direction_succ v x hj, A.direction_eq_of_prefix_eq hj.le heq,
    A.actualObservations_eq_of_prefix_eq ⟨j, hj⟩ heq]

theorem GroupedAffineAlgorithm.run_eq_of_sub_mem_direction {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedAffineAlgorithm E sizes) (u v : E) (x : ℝ)
    (h : v - u ∈ A.direction u x k) : A.run v x = A.run u x :=
  congrArg (A.output x) ((A.prefix_eq_iff_sub_mem_direction u v x k le_rfl).mpr h)

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
  induction j with
  | zero => rfl
  | succ j ih =>
    have hlt : j < k := by omega
    have hprev := ih hlt.le
    simp only [toAffine] at hprev
    simp only [GroupedAffineAlgorithm.prefix, GroupedRealAlgorithm.prefix, toAffine]
    rw [hprev]
    funext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · funext slot
      simp only [Fin.lastCases_last]
      exact hanswer _
    · simp only [Fin.lastCases_castSucc]

theorem GroupedRealAlgorithm.toAffine_run_eq {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedRealAlgorithm sizes) (observe : RealQuery → AffineObservation E)
    {u : E} {f : ℝ → ℝ} (hanswer : ∀ q, (observe q).answer u = q.answer f) (x : ℝ) :
    (A.toAffine observe).run u x = A.run f x :=
  congrArg (A.output x) (A.toAffine_prefix_eq observe hanswer x k le_rfl)

theorem GroupedRealAlgorithm.toAffine_actual_location_eq {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedRealAlgorithm sizes) (observe : RealQuery → AffineObservation E)
    {u : E} {f : ℝ → ℝ} (hanswer : ∀ q, (observe q).answer u = q.answer f)
    (hlocation : ∀ q, (observe q).location = q.location) (x : ℝ)
    (g : Fin k) (slot : Fin (sizes g)) :
    ((A.toAffine observe).actualObservations u x g slot).location =
      (A.actualQueries f x g slot).location := by
  have hprev := A.toAffine_prefix_eq observe hanswer x g.val g.isLt.le
  simp only [toAffine] at hprev
  simp only [GroupedAffineAlgorithm.actualObservations, toAffine]
  rw [hprev]
  exact hlocation _

end KungTraub
