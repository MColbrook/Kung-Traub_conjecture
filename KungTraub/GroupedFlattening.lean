import KungTraub.GroupedIndexing
import KungTraub.Transcripts

/-!
# Scalar representation of grouped algorithms

The scalar rule recovers only complete earlier groups from its available history.
Answers already present from the current group are ignored when selecting a query.
This permits the common entire-stage construction to store scalar queries while
retaining the grouped exponent.
-/

noncomputable section
namespace KungTraub

def scalarPrefixRestriction {n : ℕ} (answers : Fin n → ℝ) (t : ℕ) (ht : t ≤ n) : Fin t → ℝ :=
  fun i => answers ⟨i.val, i.isLt.trans_le ht⟩

def decodeGroupPrefix {k : ℕ} (sizes : Fin k → ℕ) {t : ℕ} (history : Fin t → ℝ)
    (j : ℕ) (hj : j ≤ k) (hN : groupedPrefixCount sizes j ≤ t) : GroupPrefix sizes j hj :=
  fun i slot => history ⟨(groupSlotEquiv sizes ⟨⟨i.val, i.isLt.trans_le hj⟩, slot⟩).val,
    ((groupSlotEquiv_lt_prefix_iff sizes ⟨i.val, i.isLt.trans_le hj⟩ slot hj).mpr i.isLt).trans_le hN⟩

theorem group_prefix_count_le_scalar_position {k : ℕ} (sizes : Fin k → ℕ)
    (t : Fin (groupedObservationCount sizes)) :
    groupedPrefixCount sizes ((groupSlotEquiv sizes).symm t).1.val ≤ t.val := by
  obtain ⟨pair, rfl⟩ := (groupSlotEquiv sizes).surjective t
  rw [Equiv.symm_apply_apply, groupSlotEquiv_apply]
  exact Nat.le_add_right _ _

def GroupedRealAlgorithm.flatten {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedRealAlgorithm sizes) : RealAlgorithm (groupedObservationCount sizes) where
  query t x history :=
    let pair := (groupSlotEquiv sizes).symm t
    A.query pair.1 x
      (decodeGroupPrefix sizes history pair.1.val pair.1.isLt.le
        (group_prefix_count_le_scalar_position sizes t)) pair.2
  output x history := A.output x
    (decodeGroupPrefix sizes history k le_rfl (by rw [groupedPrefixCount_eq_total]))

theorem GroupedRealAlgorithm.prefix_apply_eq_actual_answer {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedRealAlgorithm sizes) (f : ℝ → ℝ) (x : ℝ)
    (j : ℕ) (hj : j ≤ k) (g : Fin k) (hg : g.val < j) (slot : Fin (sizes g)) :
    A.prefix f x j hj ⟨g.val, hg⟩ slot = (A.actualQueries f x g slot).answer f := by
  induction j with
  | zero => omega
  | succ j ih =>
    have hjk : j < k := by omega
    by_cases hgj : g.val < j
    · change A.prefix f x (j + 1) hj (⟨g.val, hgj⟩ : Fin j).castSucc slot = _
      simpa only [GroupedRealAlgorithm.prefix, Fin.lastCases_castSucc] using ih hjk.le hgj
    · have hgeq : g = ⟨j, hjk⟩ := by apply Fin.ext; change g.val = j; omega
      subst g
      change A.prefix f x (j + 1) hj (Fin.last j) slot = _
      simp only [GroupedRealAlgorithm.prefix, Fin.lastCases_last, GroupedRealAlgorithm.actualQueries]

def GroupedRealAlgorithm.scalarAnswers {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedRealAlgorithm sizes) (f : ℝ → ℝ) (x : ℝ) :
    Fin (groupedObservationCount sizes) → ℝ := fun t =>
  let pair := (groupSlotEquiv sizes).symm t
  (A.actualQueries f x pair.1 pair.2).answer f

theorem GroupedRealAlgorithm.scalarAnswers_groupSlotEquiv {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedRealAlgorithm sizes) (f : ℝ → ℝ) (x : ℝ)
    (g : Fin k) (slot : Fin (sizes g)) :
    A.scalarAnswers f x (groupSlotEquiv sizes ⟨g, slot⟩) = (A.actualQueries f x g slot).answer f := by
  exact congrArg (fun pair : (g : Fin k) × Fin (sizes g) =>
    (A.actualQueries f x pair.1 pair.2).answer f)
    ((groupSlotEquiv sizes).symm_apply_apply ⟨g, slot⟩)

theorem GroupedRealAlgorithm.decode_scalarAnswers {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedRealAlgorithm sizes) (f : ℝ → ℝ) (x : ℝ)
    {t : ℕ} (ht : t ≤ groupedObservationCount sizes) (j : ℕ) (hj : j ≤ k)
    (hN : groupedPrefixCount sizes j ≤ t) :
    decodeGroupPrefix sizes (scalarPrefixRestriction (A.scalarAnswers f x) t ht) j hj hN =
      A.prefix f x j hj := by
  funext i slot
  change A.scalarAnswers f x (groupSlotEquiv sizes ⟨⟨i.val, i.isLt.trans_le hj⟩, slot⟩) = _
  rw [A.scalarAnswers_groupSlotEquiv]
  exact (A.prefix_apply_eq_actual_answer f x j hj ⟨i.val, i.isLt.trans_le hj⟩ i.isLt slot).symm

theorem GroupedRealAlgorithm.flatten_query_on_scalarAnswers {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedRealAlgorithm sizes) (f : ℝ → ℝ) (x : ℝ)
    (t : Fin (groupedObservationCount sizes)) :
    A.flatten.query t x (scalarPrefixRestriction (A.scalarAnswers f x) t.val t.isLt.le) =
      A.actualQueries f x ((groupSlotEquiv sizes).symm t).1 ((groupSlotEquiv sizes).symm t).2 := by
  simp only [GroupedRealAlgorithm.flatten]
  rw [A.decode_scalarAnswers]
  rfl

/-- A candidate full answer vector satisfying each scalar query determines every prefix. -/
theorem RealAlgorithm.prefix_eq_prescribed_answers {n : ℕ} (A : RealAlgorithm n)
    (f : ℝ → ℝ) (x : ℝ) (answers : Fin n → ℝ)
    (hanswers : ∀ t : Fin n,
      (A.query t x (scalarPrefixRestriction answers t.val t.isLt.le)).answer f = answers t)
    (j : ℕ) (hj : j ≤ n) : A.prefix f x j hj = scalarPrefixRestriction answers j hj := by
  induction j with
  | zero => funext i; exact Fin.elim0 i
  | succ j ih =>
    have hjn : j < n := by omega
    simp only [RealAlgorithm.prefix]
    rw [ih hjn.le]
    funext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [Fin.snoc_last]
      change (A.query ⟨j, hjn⟩ x (scalarPrefixRestriction answers j hjn.le)).answer f = answers ⟨j, hjn⟩
      exact hanswers ⟨j, hjn⟩
    · simp only [Fin.snoc_castSucc]
      rfl

theorem GroupedRealAlgorithm.flatten_prefix_eq_scalarAnswers {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedRealAlgorithm sizes) (f : ℝ → ℝ) (x : ℝ)
    (t : ℕ) (ht : t ≤ groupedObservationCount sizes) :
    A.flatten.prefix f x t ht = scalarPrefixRestriction (A.scalarAnswers f x) t ht := by
  apply RealAlgorithm.prefix_eq_prescribed_answers
  intro i
  rw [A.flatten_query_on_scalarAnswers]
  rfl

theorem GroupedRealAlgorithm.flatten_actualQuery {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedRealAlgorithm sizes) (f : ℝ → ℝ) (x : ℝ)
    (t : Fin (groupedObservationCount sizes)) :
    A.flatten.actualQuery f x t =
      A.actualQueries f x ((groupSlotEquiv sizes).symm t).1 ((groupSlotEquiv sizes).symm t).2 := by
  unfold RealAlgorithm.actualQuery
  rw [A.flatten_prefix_eq_scalarAnswers]
  exact A.flatten_query_on_scalarAnswers f x t

theorem GroupedRealAlgorithm.flatten_actualQuery_groupSlotEquiv {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedRealAlgorithm sizes) (f : ℝ → ℝ) (x : ℝ)
    (g : Fin k) (slot : Fin (sizes g)) :
    A.flatten.actualQuery f x (groupSlotEquiv sizes ⟨g, slot⟩) = A.actualQueries f x g slot := by
  rw [A.flatten_actualQuery]
  exact congrArg (fun pair : (g : Fin k) × Fin (sizes g) => A.actualQueries f x pair.1 pair.2)
    ((groupSlotEquiv sizes).symm_apply_apply ⟨g, slot⟩)

theorem GroupedRealAlgorithm.flatten_run_eq {k : ℕ} {sizes : Fin k → ℕ}
    (A : GroupedRealAlgorithm sizes) (f : ℝ → ℝ) (x : ℝ) : A.flatten.run f x = A.run f x := by
  unfold RealAlgorithm.run
  rw [A.flatten_prefix_eq_scalarAnswers]
  change A.output x (decodeGroupPrefix sizes
    (scalarPrefixRestriction (A.scalarAnswers f x) (groupedObservationCount sizes) le_rfl)
    k le_rfl _) = A.output x (A.prefix f x k le_rfl)
  rw [A.decode_scalarAnswers]

end KungTraub
