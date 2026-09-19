import KungTraubAppendices.HermiteNodal

/-!
# The inverse Hermite remainder on a closed interval

Subtracting a multiple of the monic nodal polynomial makes the error vanish
at the evaluation point as well as at the interpolation nodes. Rolle's theorem,
with the initial node counted twice, gives the precise factorial normalization.
The inverse function need only be analytic near the specified interval.
-/

noncomputable section

open Polynomial Set

namespace KungTraubAppendices

variable {ι : Type*}

/-- The exact mean-value remainder for arbitrary distinct value nodes and one
derivative condition, evaluated at a new point in the same closed interval. -/
theorem hermite_remainder_at_new_point {s : Finset ι} {nodes : ι → ℝ}
    (hnodes : Set.InjOn nodes s) {i : ι} (hi : i ∈ s)
    {a b t : ℝ} {g : ℝ → ℝ} (hg : AnalyticOnNhd ℝ g (Icc a b))
    (hxin : ∀ j ∈ s, nodes j ∈ Icc a b) (htin : t ∈ Icc a b)
    (ht : ∀ j ∈ s, t ≠ nodes j) {P : ℝ[X]}
    (hdegree : P.degree ≤ (s.card : WithBot ℕ))
    (hvalues : ∀ j ∈ s, P.eval (nodes j) = g (nodes j))
    (hderivative : P.derivative.eval (nodes i) = deriv g (nodes i)) :
    ∃ c ∈ Icc a b, g t - P.eval t =
      iteratedDeriv (s.card + 1) g c / ((s.card + 1).factorial : ℝ) *
        (doubleNodal s nodes i).eval t := by
  classical
  let N := doubleNodal s nodes i
  let q := (g t - P.eval t) / N.eval t
  let E : ℝ → ℝ := fun z => g z - P.eval z - q * N.eval z
  have hNne : N.eval t ≠ 0 := doubleNodal_eval_ne_zero nodes hi ht
  have hPan : AnalyticOnNhd ℝ (fun z => P.eval z) (Icc a b) :=
    (AnalyticOnNhd.eval_polynomial P).mono (subset_univ _)
  have hNan : AnalyticOnNhd ℝ (fun z => N.eval z) (Icc a b) :=
    (AnalyticOnNhd.eval_polynomial N).mono (subset_univ _)
  have hqan : AnalyticOnNhd ℝ (fun z => q * N.eval z) (Icc a b) :=
    analyticOnNhd_const.mul hNan
  have hEan : AnalyticOnNhd ℝ E (Icc a b) :=
    (hg.sub hPan).sub hqan
  have hEvalues : ∀ j ∈ s, E (nodes j) = 0 := by
    intro j hj
    dsimp [E, N]
    rw [hvalues j hj, doubleNodal_eval_at_node nodes i hj]
    ring
  have hEt : E t = 0 := by
    dsimp [E, q]
    rw [div_mul_cancel₀ _ hNne, sub_self]
  have hEderiv : deriv E (nodes i) = 0 := by
    have hd : HasDerivAt E
        (deriv g (nodes i) - P.derivative.eval (nodes i) -
          q * N.derivative.eval (nodes i)) (nodes i) :=
      (((hg _ (hxin i hi)).differentiableAt.hasDerivAt).sub
        (P.hasDerivAt _)).sub ((N.hasDerivAt _).const_mul q)
    rw [hd.deriv, hderivative]
    dsimp [N]
    rw [doubleNodal_derivative_at_node nodes hi]
    ring
  let S : Finset ℝ := insert t (s.image nodes)
  have htS : t ∉ s.image nodes := by
    simp only [Finset.mem_image, not_exists, not_and]
    intro j hj hjt
    exact ht j hj hjt.symm
  have hScard : S.card = s.card + 1 := by
    dsimp [S]
    rw [Finset.card_insert_of_notMem htS, Finset.card_image_of_injOn hnodes]
  have hSinside : ∀ z ∈ S, z ∈ Icc a b := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact htin
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
      exact hxin j hj
  have hSzero : ∀ z ∈ S, E z = 0 := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hEt
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
      exact hEvalues j hj
  have hni : nodes i ∈ S :=
    Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  obtain ⟨c, hc, hEc⟩ := analytic_exists_iteratedDeriv_zero_of_double_node
    s.card hEan S hScard hSinside hSzero hni hEderiv
  have hPzero : iteratedDeriv (s.card + 1) (fun z => P.eval z) c = 0 := by
    rw [iteratedDeriv_polynomial_eval,
      iterate_derivative_eq_zero_of_degree_lt
        (hdegree.trans_lt (by exact_mod_cast Nat.lt_succ_self s.card))]
    simp
  have hNtop : iteratedDeriv (s.card + 1) (fun z => N.eval z) c =
      ((s.card + 1).factorial : ℝ) := doubleNodal_top_derivative s nodes i c
  have hformula : iteratedDeriv (s.card + 1) E c =
      iteratedDeriv (s.card + 1) g c - q * ((s.card + 1).factorial : ℝ) := by
    change iteratedDeriv (s.card + 1)
      ((g - fun z => P.eval z) - fun z => q * N.eval z) c = _
    rw [iteratedDeriv_sub ((hg.sub hPan) c hc).contDiffAt (hqan c hc).contDiffAt,
      iteratedDeriv_sub (hg c hc).contDiffAt (hPan c hc).contDiffAt,
      iteratedDeriv_const_mul_field, hPzero, hNtop, sub_zero]
  have hfac : ((s.card + 1).factorial : ℝ) ≠ 0 := by positivity
  have hq : q = iteratedDeriv (s.card + 1) g c /
      ((s.card + 1).factorial : ℝ) := by
    apply (eq_div_iff hfac).mpr
    rw [hformula] at hEc
    exact (sub_eq_zero.mp hEc).symm
  refine ⟨c, hc, ?_⟩
  rw [← hq]
  exact (div_mul_cancel₀ _ hNne).symm

end KungTraubAppendices
