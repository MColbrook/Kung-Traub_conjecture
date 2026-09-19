import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

/-!
# Repeated Rolle arguments for the Hermite remainder

Mathlib's Rolle theorem supplies one derivative zero in each consecutive gap.
The resulting points remain in the original closed interval and are distinct.
The hypotheses on ordinary iterated derivatives are later discharged for the
analytic inverse and its polynomial interpolation error.
-/

noncomputable section

open Set

namespace KungTraubAppendices

/-- Consecutive distinct zeros give strictly interleaved derivative zeros. -/
theorem exists_interleaved_derivative_zeros {n : ℕ} {f : ℝ → ℝ} {a b : ℝ}
    (x : Fin (n + 1) → ℝ) (hx : StrictMono x)
    (hxin : ∀ i, x i ∈ Icc a b) (hf : ContinuousOn f (Icc a b))
    (hzero : ∀ i, f (x i) = 0) :
    ∃ y : Fin n → ℝ, StrictMono y ∧
      ∀ i, x i.castSucc < y i ∧ y i < x i.succ ∧
        y i ∈ Icc a b ∧ deriv f (y i) = 0 := by
  have hex : ∀ i : Fin n, ∃ c, x i.castSucc < c ∧ c < x i.succ ∧
      deriv f c = 0 := by
    intro i
    obtain ⟨c, hc, hd⟩ := exists_deriv_eq_zero
      (hx (show i.castSucc < i.succ by simp))
      (hf.mono (fun z hz => ⟨(hxin i.castSucc).1.trans hz.1,
        hz.2.trans (hxin i.succ).2⟩))
      ((hzero i.castSucc).trans (hzero i.succ).symm)
    exact ⟨c, hc.1, hc.2, hd⟩
  choose y hy using hex
  refine ⟨y, ?_, ?_⟩
  · intro i j hij
    have hij' : i.succ ≤ j.castSucc := by simpa using hij
    exact (hy i).2.1.trans_le (hx.monotone hij') |>.trans (hy j).1
  · intro i
    exact ⟨(hy i).1, (hy i).2.1,
      ⟨(hxin i.castSucc).1.trans (hy i).1.le,
        (hy i).2.1.le.trans (hxin i.succ).2⟩, (hy i).2.2⟩

/-- Interleaved points avoid every original node, including either endpoint. -/
theorem interleaved_ne_node {n : ℕ} {x : Fin (n + 1) → ℝ}
    (hx : StrictMono x) {y : Fin n → ℝ}
    (hy : ∀ i, x i.castSucc < y i ∧ y i < x i.succ)
    (i : Fin n) (j : Fin (n + 1)) : y i ≠ x j := by
  by_cases hji : j ≤ i.castSucc
  · exact ne_of_gt ((hx.monotone hji).trans_lt (hy i).1)
  · have hij : i.succ ≤ j := by
      have hval : i.val < j.val := lt_of_not_ge hji
      change i.val + 1 ≤ j.val
      omega
    exact ne_of_lt ((hy i).2.trans_le (hx.monotone hij))

/-- `n + 1` distinct zeros force a zero of the `n`th derivative in the same
closed interval. Continuity is required only for the derivatives used by Rolle. -/
theorem exists_iteratedDeriv_zero_of_strictMono (n : ℕ) {f : ℝ → ℝ} {a b : ℝ}
    (x : Fin (n + 1) → ℝ) (hx : StrictMono x)
    (hxin : ∀ i, x i ∈ Icc a b) (hzero : ∀ i, f (x i) = 0)
    (hcont : ∀ k < n, ContinuousOn (iteratedDeriv k f) (Icc a b)) :
    ∃ c ∈ Icc a b, iteratedDeriv n f c = 0 := by
  induction n generalizing f with
  | zero => exact ⟨x 0, hxin 0, by simpa using hzero 0⟩
  | succ n ih =>
    obtain ⟨y, hy, hys⟩ := exists_interleaved_derivative_zeros x hx hxin
      (by simpa using hcont 0 (Nat.zero_lt_succ n)) hzero
    obtain ⟨c, hcin, hc⟩ := ih y hy (fun i => (hys i).2.2.1)
      (fun i => (hys i).2.2.2) (fun k hk => by
        rw [← iteratedDeriv_succ']
        exact hcont (k + 1) (by omega))
    exact ⟨c, hcin, by simpa only [iteratedDeriv_succ'] using hc⟩

/-- An unordered finite set of distinct zeros gives the same repeated Rolle
conclusion; sorting introduces no restriction on the locations. -/
theorem exists_iteratedDeriv_zero_of_finset (n : ℕ) {f : ℝ → ℝ} {a b : ℝ}
    (s : Finset ℝ) (hs : s.card = n + 1)
    (hsin : ∀ z ∈ s, z ∈ Icc a b) (hzero : ∀ z ∈ s, f z = 0)
    (hcont : ∀ k < n, ContinuousOn (iteratedDeriv k f) (Icc a b)) :
    ∃ c ∈ Icc a b, iteratedDeriv n f c = 0 := by
  exact exists_iteratedDeriv_zero_of_strictMono n (s.orderEmbOfFin hs)
    (s.orderEmbOfFin hs).strictMono
    (fun i => hsin _ (s.orderEmbOfFin_mem hs i))
    (fun i => hzero _ (s.orderEmbOfFin_mem hs i)) hcont

/-- One zero is counted twice when the first derivative also vanishes there.
This is the repeated-node case needed for inverse Hermite interpolation. -/
theorem exists_iteratedDeriv_zero_of_derivative_zero (n : ℕ)
    {f : ℝ → ℝ} {a b : ℝ} (x : Fin (n + 1) → ℝ) (hx : StrictMono x)
    (hxin : ∀ i, x i ∈ Icc a b) (hzero : ∀ i, f (x i) = 0)
    (i : Fin (n + 1)) (hderiv : deriv f (x i) = 0)
    (hcont : ∀ k < n + 1, ContinuousOn (iteratedDeriv k f) (Icc a b)) :
    ∃ c ∈ Icc a b, iteratedDeriv (n + 1) f c = 0 := by
  classical
  obtain ⟨y, hy, hys⟩ := exists_interleaved_derivative_zeros x hx hxin
    (by simpa using hcont 0 (Nat.zero_lt_succ n)) hzero
  let s : Finset ℝ := insert (x i) (Finset.univ.image y)
  have hnotin : x i ∉ Finset.univ.image y := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro j hj
    exact interleaved_ne_node hx (fun j => ⟨(hys j).1, (hys j).2.1⟩) j i hj
  have hcard : s.card = n + 1 := by
    simp only [s, Finset.card_insert_of_notMem hnotin]
    rw [Finset.card_image_of_injective _ hy.injective]
    simp
  obtain ⟨c, hcin, hc⟩ := exists_iteratedDeriv_zero_of_finset n s hcard
    (fun z hz => by
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hxin i
      · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hz
        exact (hys j).2.2.1)
    (fun z hz => by
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hderiv
      · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hz
        exact (hys j).2.2.2)
    (fun k hk => by
      rw [← iteratedDeriv_succ']
      exact hcont (k + 1) (by omega))
  exact ⟨c, hcin, by simpa only [iteratedDeriv_succ'] using hc⟩

end KungTraubAppendices
