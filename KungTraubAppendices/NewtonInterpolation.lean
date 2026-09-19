import KungTraubAppendices.HermiteCalculus
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Newton interpolation with repeated nodes

Mathlib's `dslope` uses the derivative at a repeated node. Successive applications
therefore give the usual recursive Newton construction with all coincidences
allowed. These polynomials describe the interpolation error of the inverse Hermite method.

The analytic extension at a repeated node reuses Mathlib's power-series theorem
`HasFPowerSeriesAt.has_fpower_series_dslope_fslope`.
-/

noncomputable section

open Polynomial Set

namespace KungTraubAppendices

/-- The derivative-valued extension of a slope preserves local analyticity,
at the distinguished node and at every other point. -/
theorem analyticAt_dslope {f : ℝ → ℝ} {b : ℝ} (hf : AnalyticAt ℝ f b) (a : ℝ) :
    AnalyticAt ℝ (dslope f a) b := by
  by_cases hba : b = a
  · subst b
    obtain ⟨p, hp⟩ := hf
    exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩
  · have hs : AnalyticAt ℝ (slope f a) b := by
      have heq : slope f a = fun t => (f t - f a) / (t - a) :=
        funext (slope_def_field f a)
      rw [heq]
      exact (hf.sub analyticAt_const).div (analyticAt_id.sub analyticAt_const)
        (sub_ne_zero.mpr hba)
    exact hs.congr (dslope_eventuallyEq_slope_of_ne f hba).symm

/-- Successive slopes, including all derivative-valued diagonal extensions. -/
def newtonRemainderFunction (f : ℝ → ℝ) : List ℝ → ℝ → ℝ
  | [] => f
  | a :: xs => newtonRemainderFunction (dslope f a) xs

/-- The actual Newton interpolation polynomial for a list with repetitions. -/
def newtonPolynomial (f : ℝ → ℝ) : List ℝ → ℝ[X]
  | [] => 0
  | a :: xs => C (f a) + (X - C a) * newtonPolynomial (dslope f a) xs

theorem newtonRemainderFunction_analyticAt {f : ℝ → ℝ} {b : ℝ}
    (hf : AnalyticAt ℝ f b) (xs : List ℝ) :
    AnalyticAt ℝ (newtonRemainderFunction f xs) b := by
  induction xs generalizing f with
  | nil => exact hf
  | cons a xs ih => exact ih (analyticAt_dslope hf a)

/-- Newton's exact algebraic remainder identity, without distinctness or
analytic hypotheses. Analyticity supplies the derivative meaning afterwards. -/
theorem newtonPolynomial_remainder (f : ℝ → ℝ) (xs : List ℝ) (t : ℝ) :
    f t - (newtonPolynomial f xs).eval t =
      (xs.map (fun a => t - a)).prod * newtonRemainderFunction f xs t := by
  induction xs generalizing f with
  | nil => simp [newtonPolynomial, newtonRemainderFunction]
  | cons a xs ih =>
    have hs : (t - a) * dslope f a t = f t - f a := by
      simpa only [smul_eq_mul] using sub_smul_dslope f a t
    simp only [newtonPolynomial, eval_add, eval_C, eval_mul, eval_sub, eval_X,
      newtonRemainderFunction, List.map_cons, List.prod_cons]
    calc
      _ = (t - a) * (dslope f a t - (newtonPolynomial (dslope f a) xs).eval t) := by
        nlinarith [hs]
      _ = _ := by rw [ih]; ring

/-- The construction has the full Hermite degree bound even with repetitions. -/
theorem newtonPolynomial_natDegree_le (f : ℝ → ℝ) (xs : List ℝ) :
    (newtonPolynomial f xs).natDegree ≤ xs.length - 1 := by
  induction xs generalizing f with
  | nil => simp [newtonPolynomial]
  | cons a xs ih =>
    cases xs with
    | nil => simp [newtonPolynomial]
    | cons b xs =>
      have htail := ih (dslope f a)
      simp only [List.length_cons, Nat.add_sub_cancel] at htail ⊢
      apply (natDegree_add_le _ _).trans
      apply max_le
      · simp
      · apply (natDegree_mul_le).trans
        rw [natDegree_X_sub_C]
        omega

end KungTraubAppendices
