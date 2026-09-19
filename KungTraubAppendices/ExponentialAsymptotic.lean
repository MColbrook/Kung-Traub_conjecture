import KungTraubAppendices.HermiteHistorySequence
import KungTraubAppendices.ExponentialHermiteStep
import KungTraubAppendices.AsymptoticSeparation

/-! Exact leading coefficients for the actual finite observation histories. -/

noncomputable section
open Filter KungTraub
open scoped Topology
namespace KungTraubAppendices

/-- All entries of the actual unstopped history have the asymptotics,
with eventual distinctness derived at each preceding stage. -/
theorem inverseHermiteHistory_exp_asymptotic (j : ℕ) :
    ∀ i : Fin (j + 1), Tendsto (fun x : ℝ =>
      inverseHermiteHistory (fun t => Real.exp t - 1) j x i / x ^ (2 ^ i.val))
      (𝓝[≠] (0 : ℝ)) (𝓝 (sharpnessCoefficient i.val)) := by
  induction j with
  | zero =>
    intro i
    have hi : i = 0 := by apply Fin.ext; omega
    subst i
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with x (hx : x ≠ 0)
    simp [inverseHermiteHistory, sharpnessCoefficient, hx]
  | succ j ih =>
    have hvalid := sharpness_history_eventually_injective_nonzero
      (fun x => inverseHermiteHistory (fun t => Real.exp t - 1) j x) ih
    have hstep := exponentialHermiteStep_tendsto j
      (fun x => inverseHermiteHistory (fun t => Real.exp t - 1) j x)
      (hvalid.mono fun _ h => h.1) ih
    intro i
    refine Fin.lastCases ?_ (fun k => ?_) i
    · simpa only [inverseHermiteHistory_last, exponentialHermitePolynomial,
        inverseHermiteHistory_zero, Fin.val_last] using hstep
    · simpa only [inverseHermiteHistory_castSucc, Fin.val_castSucc] using ih k

/-- The unstopped exponential history eventually has no zero entries and
has distinct points, simultaneously for every entry of the finite history. -/
theorem inverseHermiteHistory_exp_eventually_valid (j : ℕ) :
    ∀ᶠ x in 𝓝[≠] (0 : ℝ),
      Function.Injective (inverseHermiteHistory (fun t => Real.exp t - 1) j x) ∧
      ∀ i, inverseHermiteHistory (fun t => Real.exp t - 1) j x i ≠ 0 :=
  sharpness_history_eventually_injective_nonzero _ (inverseHermiteHistory_exp_asymptotic j)

/-- Eventual nonvanishing excludes every early-return branch of the actual
exponential execution, while its final output remains unqueried. -/
theorem inverseHermite_exp_eventually_run_eq_history (n : ℕ) (hn : 2 ≤ n) :
    ∀ᶠ x in 𝓝[≠] (0 : ℝ),
      (inverseHermiteAlgorithm n).run (fun t => Real.exp t - 1) x =
        inverseHermiteHistory (fun t => Real.exp t - 1) (n - 1) x (Fin.last (n - 1)) := by
  have hnonzero : ∀ k : Fin (n - 1), ∀ᶠ x in 𝓝[≠] (0 : ℝ),
      Real.exp (inverseHermiteHistory (fun t => Real.exp t - 1) k.val x (Fin.last k.val)) - 1 ≠ 0 := by
    intro k
    filter_upwards [inverseHermiteHistory_exp_eventually_valid k.val] with x hx
    intro hz
    apply hx.2 (Fin.last k.val)
    apply Real.exp_injective
    rw [Real.exp_zero]
    linarith
  filter_upwards [Filter.eventually_all.mpr hnonzero] with x hx
  exact inverseHermite_run_eq_history n hn _ x
    (by rw [deriv_exp_sub_one]; exact Real.exp_ne_zero x)
    (fun k hk => hx ⟨k, hk⟩)

/-- The exact leading coefficient of the same actual algorithm on the
exponential example, with a two-sided punctured limit. -/
theorem inverseHermite_exp_asymptotic (n : ℕ) (hn : 2 ≤ n) :
    Tendsto (fun x : ℝ =>
      (inverseHermiteAlgorithm n).run (fun t => Real.exp t - 1) x /
        x ^ KungTraub.orderBound n)
      (𝓝[≠] (0 : ℝ)) (𝓝 (sharpnessCoefficient (n - 1))) := by
  have h := inverseHermiteHistory_exp_asymptotic (n - 1) (Fin.last (n - 1))
  have hnzero : n ≠ 0 := by omega
  simp only [Fin.val_last] at h
  apply h.congr'
  filter_upwards [inverseHermite_exp_eventually_run_eq_history n hn] with x hx
  rw [hx, orderBound, if_neg hnzero]

end KungTraubAppendices
