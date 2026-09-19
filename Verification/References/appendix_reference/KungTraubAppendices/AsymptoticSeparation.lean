import appendix_reference.KungTraubAppendices.SharpnessElementary

/-!
# Separation of points with different leading powers

These elementary limit facts supply the node distinctness and nonvanishing
needed in Appendix A. All limits use the full two-sided punctured neighborhood
of zero. The proofs reuse Mathlib's `Filter.Tendsto.eventually_ne`, arithmetic
of limits and finite intersections of eventual statements. The input points may coincide.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace KungTraubAppendices

/-- A nonzero normalized leading coefficient excludes zero values nearby. -/
theorem eventually_ne_zero_of_normalized_pow (a : ℕ) (f : ℝ → ℝ) (c : ℝ)
    (hc : c ≠ 0)
    (hf : Tendsto (fun x => f x / x ^ a) (𝓝[≠] (0 : ℝ)) (𝓝 c)) :
    ∀ᶠ x in 𝓝[≠] (0 : ℝ), f x ≠ 0 := by
  sorry

/-- Normalizing a higher-order term by a smaller natural power gives zero. -/
theorem normalized_pow_tendsto_zero_of_lt {a b : ℕ} (hab : a < b)
    (g : ℝ → ℝ) (d : ℝ)
    (hg : Tendsto (fun x => g x / x ^ b) (𝓝[≠] (0 : ℝ)) (𝓝 d)) :
    Tendsto (fun x => g x / x ^ a) (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  sorry

/-- Different leading powers with a nonzero smaller-order coefficient imply
eventual separation, without any assumption on the other leading coefficient. -/
theorem eventually_ne_of_normalized_pow_lt {a b : ℕ} (hab : a < b)
    (f g : ℝ → ℝ) (c d : ℝ) (hc : c ≠ 0)
    (hf : Tendsto (fun x => f x / x ^ a) (𝓝[≠] (0 : ℝ)) (𝓝 c))
    (hg : Tendsto (fun x => g x / x ^ b) (𝓝[≠] (0 : ℝ)) (𝓝 d)) :
    ∀ᶠ x in 𝓝[≠] (0 : ℝ), f x ≠ g x := by
  sorry

/-- A finite family with strictly increasing leading powers is eventually
injective and contains no zero point. The empty family is included. -/
theorem eventually_injective_nonzero_of_normalized_powers {k : ℕ}
    (points : ℝ → Fin k → ℝ) (q : Fin k → ℕ) (c : Fin k → ℝ)
    (hq : StrictMono q) (hc : ∀ i, c i ≠ 0)
    (hpoints : ∀ i, Tendsto (fun x => points x i / x ^ q i)
      (𝓝[≠] (0 : ℝ)) (𝓝 (c i))) :
    ∀ᶠ x in 𝓝[≠] (0 : ℝ),
      Function.Injective (points x) ∧ ∀ i, points x i ≠ 0 := by
  sorry

/-- The powers and positive coefficients give eventual distinctness
and nonvanishing of any finite history with the specified asymptotics. -/
theorem sharpness_history_eventually_injective_nonzero {k : ℕ}
    (points : ℝ → Fin k → ℝ)
    (hpoints : ∀ i, Tendsto (fun x => points x i / x ^ (2 ^ i.val))
      (𝓝[≠] (0 : ℝ)) (𝓝 (sharpnessCoefficient i.val))) :
    ∀ᶠ x in 𝓝[≠] (0 : ℝ),
      Function.Injective (points x) ∧ ∀ i, points x i ≠ 0 := by
  sorry

end KungTraubAppendices
