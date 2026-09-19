import KungTraubAppendices.HermiteTailAnalysis
import KungTraubAppendices.SharpnessElementary

/-! Local attainment for the actual bounded observation procedure. -/

noncomputable section
open Set KungTraub Polynomial
namespace KungTraubAppendices

/-- The first interpolant is precisely the initial Newton output. -/
theorem hermite_initial_eval (f : ℝ → ℝ) (x : ℝ) :
    (hermiteWithDerivative Finset.univ (fun _ : Fin 1 => f x)
      (fun _ : Fin 1 => x) 0 (deriv f x)⁻¹).eval 0 = x - f x / deriv f x := by
  have hs : (Finset.univ : Finset (Fin 1)) = {0} := by
    ext i
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact Subsingleton.elim _ _
  rw [hs, hermiteWithDerivative_singleton]
  simp only [eval_add, eval_C, eval_mul, eval_sub, eval_X]
  ring

/-- The initial observations and the recursively executed tail satisfy the
same fixed neighborhood and order bound. -/
theorem InverseHermiteLocalData.tree_analysis {n : ℕ} {hn : 2 ≤ n}
    {U : Set ℝ} {f : ℝ → ℝ} {α : ℝ} (d : InverseHermiteLocalData n hn U f α)
    (x : ℝ) (hx : x ≠ α) (hin : x ∈ Icc (α - d.δ) (α + d.δ)) :
    realTreeExecutionIn (inverseHermiteTree n x) f U ∧
      |(inverseHermiteTree n x).run f - α| ≤
        hermiteOrderConstant (inverseHermiteDerivativeBound n hn d.g (Icc (-d.r) d.r))
          d.L (n - 1) * |x - α| ^ (2 ^ (n - 1)) := by
  obtain ⟨k, hk⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  subst n
  have hxU : x ∈ U := d.interval_subset (d.closed_neighborhood_subset hin)
  have hf : f x ≠ 0 := (d.zero_iff hin).not.mpr hx
  have hd : deriv f x ≠ 0 := d.derivative_ne_zero x (d.closed_neighborhood_subset hin)
  have hp : Function.Injective (fun _ : Fin 1 => x) := fun _ _ _ => Subsingleton.elim _ _
  have hb : ∀ i : Fin 1, |x - α| ≤
      hermiteOrderConstant (inverseHermiteDerivativeBound (k + 2) hn d.g (Icc (-d.r) d.r))
        d.L i.val * |x - α| ^ (2 ^ i.val) := by
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp
  have ht := d.tail_analysis k 0 (by omega) (fun _ : Fin 1 => x) hp
    (fun _ => hin) hx (fun _ => le_rfl) hb
  dsimp only at ht
  rw [hermite_initial_eval] at ht
  simpa [inverseHermiteTree, realTreeExecutionIn, RealQuery.answer,
    BoundedRealTree.run, hf, hd, hxU] using ht

/-- The specified stationary observation algorithm attains order `2^(n-1)`
on every open real interval input near every simple analytic zero. -/
theorem inverseHermite_universal_local_order (n : ℕ) (hn : 2 ≤ n) :
    RealIntervalUniversalLocalOrder (inverseHermiteAlgorithm n)
      (KungTraub.orderBound n : ℝ) := by
  intro U hU _ f hf α hα hroot
  obtain ⟨d⟩ := exists_inverseHermiteLocalData n hn hU hα (hf α hα) hroot.1 hroot.2
  let D := inverseHermiteDerivativeBound n hn d.g (Icc (-d.r) d.r)
  refine ⟨hermiteOrderConstant D d.L (n - 1),
    hermiteOrderConstant_pos (inverseHermiteDerivativeBound_pos _ _ _ _)
      (lt_of_lt_of_le zero_lt_one d.linear_constant_ge_one) _, d.δ, d.delta_pos, ?_⟩
  intro x hx hsmall
  have hxne : x ≠ α := sub_ne_zero.mp (abs_pos.mp hx)
  have hin : x ∈ Icc (α - d.δ) (α + d.δ) := by
    have he := abs_lt.mp hsmall
    constructor <;> linarith [he.1, he.2]
  obtain ⟨hdom, herr⟩ := d.tree_analysis x hxne hin
  refine ⟨d.interval_subset (d.closed_neighborhood_subset hin),
    realExecutionIn_of_tree_execution (inverseHermiteMethod n) hdom, ?_⟩
  rw [inverseHermite_run_eq, Real.rpow_eq_pow, Real.rpow_natCast]
  have hnzero : n ≠ 0 := by omega
  simpa only [inverseHermiteMethod, StoppingRealAlgorithm.run, orderBound, if_neg hnzero] using herr

end KungTraubAppendices
