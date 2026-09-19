import KungTraubAppendices.NewtonInterpolation
import Mathlib.Analysis.Analytic.Order

/-!
# All interpolation jets, including arbitrary coincidences

The exact Newton remainder has one linear factor for every list entry. Mathlib's
analytic-order product theorem and derivative characterization turn these factors
into all required derivative conditions, with no assumption of distinct nodes.
-/

noncomputable section

open Polynomial

namespace KungTraubAppendices

local instance instDecidableEqRealForJets : DecidableEq ℝ := Classical.decEq ℝ

theorem analyticAt_nodeProduct (xs : List ℝ) (b : ℝ) :
    AnalyticAt ℝ (fun t => (xs.map (fun a => t - a)).prod) b := by
  induction xs with
  | nil => simpa using (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ => (1 : ℝ)) b)
  | cons a xs ih =>
    have hlin : AnalyticAt ℝ (fun t : ℝ => t - a) b := by fun_prop
    change AnalyticAt ℝ (fun t => (t - a) * (xs.map (fun a => t - a)).prod) b
    exact hlin.mul ih

/-- Every occurrence of a node contributes one to the analytic order of the
product, regardless of zeros of the remaining analytic factor. -/
theorem count_le_analyticOrderAt_nodeProduct_mul (xs : List ℝ) {R : ℝ → ℝ} {b : ℝ}
    (hR : AnalyticAt ℝ R b) :
    (xs.count b : ℕ∞) ≤
      analyticOrderAt (fun t => (xs.map (fun a => t - a)).prod * R t) b := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have heq : (fun t => ((a :: xs).map (fun a => t - a)).prod * R t) =
        (fun t => t - a) * (fun t => (xs.map (fun a => t - a)).prod * R t) := by
      funext t
      simp only [List.map_cons, List.prod_cons, Pi.mul_apply]
      ring
    have hlin : AnalyticAt ℝ (fun t : ℝ => t - a) b := by fun_prop
    have hrest : AnalyticAt ℝ (fun t => (xs.map (fun a => t - a)).prod * R t) b :=
      (analyticAt_nodeProduct xs b).mul hR
    rw [heq, analyticOrderAt_mul hlin hrest]
    by_cases hab : a = b
    · subst a
      simpa [add_comm] using add_le_add_left ih (1 : ℕ∞)
    · simpa [hab, Ne.symm hab, analyticOrderAt_id_sub_const_of_ne (Ne.symm hab)] using ih

/-- The Newton error vanishes to at least the full listed multiplicity. -/
theorem newtonPolynomial_error_jet_zero (xs : List ℝ) {f : ℝ → ℝ} {b : ℝ}
    (hf : AnalyticAt ℝ f b) {k : ℕ} (hk : k < xs.count b) :
    iteratedDeriv k (fun t => f t - (newtonPolynomial f xs).eval t) b = 0 := by
  have hP : AnalyticAt ℝ (fun t => (newtonPolynomial f xs).eval t) b :=
    AnalyticOnNhd.eval_polynomial _ b (Set.mem_univ b)
  have herr : AnalyticAt ℝ (fun t => f t - (newtonPolynomial f xs).eval t) b :=
    hf.sub hP
  apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero herr).mp _ k hk
  have heq : (fun t => f t - (newtonPolynomial f xs).eval t) =
      fun t => (xs.map (fun a => t - a)).prod * newtonRemainderFunction f xs t :=
    funext (newtonPolynomial_remainder f xs)
  rw [heq]
  exact count_le_analyticOrderAt_nodeProduct_mul xs (newtonRemainderFunction_analyticAt hf xs)

/-- Every prescribed derivative of the analytic function equals that of the
constructed polynomial, through one less than the node's multiplicity. -/
theorem newtonPolynomial_jet_eq (xs : List ℝ) {f : ℝ → ℝ} {b : ℝ}
    (hf : AnalyticAt ℝ f b) {k : ℕ} (hk : k < xs.count b) :
    iteratedDeriv k (fun t => (newtonPolynomial f xs).eval t) b = iteratedDeriv k f b := by
  have hP : AnalyticAt ℝ (fun t => (newtonPolynomial f xs).eval t) b :=
    AnalyticOnNhd.eval_polynomial _ b (Set.mem_univ b)
  have hzero := newtonPolynomial_error_jet_zero xs hf hk
  rw [iteratedDeriv_fun_sub hf.contDiffAt hP.contDiffAt] at hzero
  exact (sub_eq_zero.mp hzero).symm

end KungTraubAppendices
