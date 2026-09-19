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
  sorry

/-- Interleaved points avoid every original node, including either endpoint. -/
theorem interleaved_ne_node {n : ℕ} {x : Fin (n + 1) → ℝ}
    (hx : StrictMono x) {y : Fin n → ℝ}
    (hy : ∀ i, x i.castSucc < y i ∧ y i < x i.succ)
    (i : Fin n) (j : Fin (n + 1)) : y i ≠ x j := by
  sorry

/-- `n + 1` distinct zeros force a zero of the `n`th derivative in the same
closed interval. Continuity is required only for the derivatives used by Rolle. -/
theorem exists_iteratedDeriv_zero_of_strictMono (n : ℕ) {f : ℝ → ℝ} {a b : ℝ}
    (x : Fin (n + 1) → ℝ) (hx : StrictMono x)
    (hxin : ∀ i, x i ∈ Icc a b) (hzero : ∀ i, f (x i) = 0)
    (hcont : ∀ k < n, ContinuousOn (iteratedDeriv k f) (Icc a b)) :
    ∃ c ∈ Icc a b, iteratedDeriv n f c = 0 := by
  sorry

/-- An unordered finite set of distinct zeros gives the same repeated Rolle
conclusion; sorting introduces no restriction on the locations. -/
theorem exists_iteratedDeriv_zero_of_finset (n : ℕ) {f : ℝ → ℝ} {a b : ℝ}
    (s : Finset ℝ) (hs : s.card = n + 1)
    (hsin : ∀ z ∈ s, z ∈ Icc a b) (hzero : ∀ z ∈ s, f z = 0)
    (hcont : ∀ k < n, ContinuousOn (iteratedDeriv k f) (Icc a b)) :
    ∃ c ∈ Icc a b, iteratedDeriv n f c = 0 := by
  sorry

/-- One zero is counted twice when the first derivative also vanishes there.
This is the repeated-node case needed for inverse Hermite interpolation. -/
theorem exists_iteratedDeriv_zero_of_derivative_zero (n : ℕ)
    {f : ℝ → ℝ} {a b : ℝ} (x : Fin (n + 1) → ℝ) (hx : StrictMono x)
    (hxin : ∀ i, x i ∈ Icc a b) (hzero : ∀ i, f (x i) = 0)
    (i : Fin (n + 1)) (hderiv : deriv f (x i) = 0)
    (hcont : ∀ k < n + 1, ContinuousOn (iteratedDeriv k f) (Icc a b)) :
    ∃ c ∈ Icc a b, iteratedDeriv (n + 1) f c = 0 := by
  sorry

end KungTraubAppendices
