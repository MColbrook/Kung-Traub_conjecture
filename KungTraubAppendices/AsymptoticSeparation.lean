import KungTraubAppendices.SharpnessElementary

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
  filter_upwards [hf.eventually_ne hc] with x hx
  intro hzero
  exact hx (by simp [hzero])

/-- Normalizing a higher-order term by a smaller natural power gives zero. -/
theorem normalized_pow_tendsto_zero_of_lt {a b : ℕ} (hab : a < b)
    (g : ℝ → ℝ) (d : ℝ)
    (hg : Tendsto (fun x => g x / x ^ b) (𝓝[≠] (0 : ℝ)) (𝓝 d)) :
    Tendsto (fun x => g x / x ^ a) (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hx : Tendsto (fun x : ℝ => x) (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hdiff : b - a ≠ 0 := by omega
  have hp : Tendsto (fun x : ℝ => x ^ (b - a))
      (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [zero_pow hdiff] using hx.pow (b - a)
  have hmul := hg.mul hp
  simp only [mul_zero] at hmul
  apply hmul.congr'
  filter_upwards [self_mem_nhdsWithin] with x (hx : x ≠ 0)
  have hpower : x ^ b = x ^ a * x ^ (b - a) := by
    rw [← pow_add, Nat.add_sub_of_le hab.le]
  rw [hpower]
  field_simp

/-- Different leading powers with a nonzero smaller-order coefficient imply
eventual separation, without any assumption on the other leading coefficient. -/
theorem eventually_ne_of_normalized_pow_lt {a b : ℕ} (hab : a < b)
    (f g : ℝ → ℝ) (c d : ℝ) (hc : c ≠ 0)
    (hf : Tendsto (fun x => f x / x ^ a) (𝓝[≠] (0 : ℝ)) (𝓝 c))
    (hg : Tendsto (fun x => g x / x ^ b) (𝓝[≠] (0 : ℝ)) (𝓝 d)) :
    ∀ᶠ x in 𝓝[≠] (0 : ℝ), f x ≠ g x := by
  have hgzero := normalized_pow_tendsto_zero_of_lt hab g d hg
  have hdiff : Tendsto (fun x => (f x - g x) / x ^ a)
      (𝓝[≠] (0 : ℝ)) (𝓝 c) := by
    simpa only [sub_div, sub_zero] using hf.sub hgzero
  filter_upwards [eventually_ne_zero_of_normalized_pow a (fun x => f x - g x) c hc hdiff]
    with x hx
  exact fun heq => hx (sub_eq_zero.mpr heq)

/-- A finite family with strictly increasing leading powers is eventually
injective and contains no zero point. The empty family is included. -/
theorem eventually_injective_nonzero_of_normalized_powers {k : ℕ}
    (points : ℝ → Fin k → ℝ) (q : Fin k → ℕ) (c : Fin k → ℝ)
    (hq : StrictMono q) (hc : ∀ i, c i ≠ 0)
    (hpoints : ∀ i, Tendsto (fun x => points x i / x ^ q i)
      (𝓝[≠] (0 : ℝ)) (𝓝 (c i))) :
    ∀ᶠ x in 𝓝[≠] (0 : ℝ),
      Function.Injective (points x) ∧ ∀ i, points x i ≠ 0 := by
  have hzero : ∀ᶠ x in 𝓝[≠] (0 : ℝ), ∀ i, points x i ≠ 0 :=
    Filter.eventually_all.mpr fun i =>
      eventually_ne_zero_of_normalized_pow (q i) (fun x => points x i) (c i) (hc i)
        (hpoints i)
  have hsep : ∀ i j, ∀ᶠ x in 𝓝[≠] (0 : ℝ), i ≠ j → points x i ≠ points x j := by
    intro i j
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall fun _ hne => (hne hij).elim
    · rcases lt_or_gt_of_ne hij with hijlt | hjilt
      · exact (eventually_ne_of_normalized_pow_lt (hq hijlt)
          (fun x => points x i) (fun x => points x j) (c i) (c j) (hc i)
          (hpoints i) (hpoints j)).mono fun _ h _ => h
      · exact (eventually_ne_of_normalized_pow_lt (hq hjilt)
          (fun x => points x j) (fun x => points x i) (c j) (c i) (hc j)
          (hpoints j) (hpoints i)).mono fun _ h _ => Ne.symm h
  have hsepall : ∀ᶠ x in 𝓝[≠] (0 : ℝ), ∀ i j, i ≠ j → points x i ≠ points x j :=
    Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => hsep i j
  filter_upwards [hzero, hsepall] with x hxzero hxsep
  refine ⟨?_, hxzero⟩
  intro i j heq
  by_contra hij
  exact hxsep i j hij heq

/-- The powers and positive coefficients give eventual distinctness
and nonvanishing of any finite history with the specified asymptotics. -/
theorem sharpness_history_eventually_injective_nonzero {k : ℕ}
    (points : ℝ → Fin k → ℝ)
    (hpoints : ∀ i, Tendsto (fun x => points x i / x ^ (2 ^ i.val))
      (𝓝[≠] (0 : ℝ)) (𝓝 (sharpnessCoefficient i.val))) :
    ∀ᶠ x in 𝓝[≠] (0 : ℝ),
      Function.Injective (points x) ∧ ∀ i, points x i ≠ 0 := by
  apply eventually_injective_nonzero_of_normalized_powers points
    (fun i => 2 ^ i.val) (fun i => sharpnessCoefficient i.val) ?_ ?_ hpoints
  · intro i j hij
    exact Nat.pow_lt_pow_right (by decide) hij
  · exact fun i => ne_of_gt (sharpnessCoefficient_pos i.val)

end KungTraubAppendices
