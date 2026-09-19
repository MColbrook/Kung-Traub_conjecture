import appendix_reference.KungTraubAppendices.HermiteTailAnalysis
import appendix_reference.KungTraubAppendices.SharpnessElementary

/-! Local attainment for the actual bounded observation procedure. -/

noncomputable section
open Set KungTraub Polynomial
namespace KungTraubAppendices

/-- The first interpolant is precisely the initial Newton output. -/
theorem hermite_initial_eval (f : ℝ → ℝ) (x : ℝ) :
    (hermiteWithDerivative Finset.univ (fun _ : Fin 1 => f x)
      (fun _ : Fin 1 => x) 0 (deriv f x)⁻¹).eval 0 = x - f x / deriv f x := by
  sorry

/-- The initial observations and the recursively executed tail satisfy the
same fixed neighborhood and order bound. -/
theorem InverseHermiteLocalData.tree_analysis {n : ℕ} {hn : 2 ≤ n}
    {U : Set ℝ} {f : ℝ → ℝ} {α : ℝ} (d : InverseHermiteLocalData n hn U f α)
    (x : ℝ) (hx : x ≠ α) (hin : x ∈ Icc (α - d.δ) (α + d.δ)) :
    realTreeExecutionIn (inverseHermiteTree n x) f U ∧
      |(inverseHermiteTree n x).run f - α| ≤
        hermiteOrderConstant (inverseHermiteDerivativeBound n hn d.g (Icc (-d.r) d.r))
          d.L (n - 1) * |x - α| ^ (2 ^ (n - 1)) := by
  sorry

/-- The specified stationary observation algorithm attains order `2^(n-1)`
on every open real interval input near every simple analytic zero. -/
theorem inverseHermite_universal_local_order (n : ℕ) (hn : 2 ≤ n) :
    RealIntervalUniversalLocalOrder (inverseHermiteAlgorithm n)
      (KungTraub.orderBound n : ℝ) := by
  sorry

end KungTraubAppendices
