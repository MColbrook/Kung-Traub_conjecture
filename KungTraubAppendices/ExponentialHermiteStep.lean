import KungTraubAppendices.ExponentialInverse
import KungTraubAppendices.HermiteDividedDifference
import KungTraubAppendices.HermiteOrderConstants
import KungTraubAppendices.SharpnessElementary
import Mathlib.Topology.Algebra.Monoid

/-!
# One analytic sharpness step for the observed Hermite polynomial

Source: Appendix A of Matthew J. Colbrook's manuscript. The polynomial receives
only the observed values of `exp x - 1`, the earlier points and the reciprocal
of the derivative at the first point. The exact Hermite remainder, the logarithm
coefficient limit, and Mathlib's continuous derivative-valued slope supply the
step. The exponent product reuses `mul_prod_pow_two`.

The step uses the earlier point asymptotics and eventual injectivity.
-/

noncomputable section

open Set Filter Polynomial
open scoped Topology BigOperators

namespace KungTraubAppendices

/-- The single derivative datum in the exponential observation method. -/
theorem deriv_exp_sub_one (x : ℝ) :
    deriv (fun t : ℝ => Real.exp t - 1) x = Real.exp x :=
  ((Real.hasDerivAt_exp x).sub_const 1).deriv

/-- The derivative of the analytic inverse equals the reciprocal of the
one observed derivative; no additional observation is involved. -/
theorem deriv_log_one_add_at_exp_sub_one (x : ℝ) :
    deriv (fun t : ℝ => Real.log (1 + t)) (Real.exp x - 1) =
      (deriv (fun t : ℝ => Real.exp t - 1) x)⁻¹ := by
  have he : 1 + (Real.exp x - 1) = Real.exp x := by ring
  have hn : 1 + (Real.exp x - 1) ≠ 0 := by rw [he]; exact Real.exp_ne_zero x
  have h := ((hasDerivAt_id (Real.exp x - 1)).const_add 1).log hn
  simpa only [id_eq, he, one_div, deriv_exp_sub_one] using h.deriv

/-- The actual data polynomial, as a function of the earlier real points. -/
def exponentialHermitePolynomial {j : ℕ} (points : Fin (j + 1) → ℝ) : ℝ[X] :=
  hermiteWithDerivative Finset.univ (fun i => Real.exp (points i) - 1) points 0
    ((deriv (fun t : ℝ => Real.exp t - 1) (points 0))⁻¹)

/-- The exact signed remainder, expressed as an extra initial factor
times the product over all observed values. -/
theorem exponentialHermitePolynomial_zero (j : ℕ) (points : Fin (j + 1) → ℝ)
    (hpoints : Function.Injective points) :
    (exponentialHermitePolynomial points).eval 0 =
      (-1 : ℝ) ^ (j + 1) *
        confluentDividedDifference (fun t : ℝ => Real.log (1 + t))
          (0 :: (Real.exp (points 0) - 1) ::
            List.ofFn (fun i => Real.exp (points i) - 1)) *
        (Real.exp (points 0) - 1) * ∏ i, (Real.exp (points i) - 1) := by
  let nodes : Fin (j + 1) → ℝ := fun i => Real.exp (points i) - 1
  have hinj : Function.Injective nodes := by
    intro i k hik
    apply hpoints
    apply Real.exp_injective
    dsimp [nodes] at hik
    linarith
  have hg : ∀ i, AnalyticAt ℝ (fun t : ℝ => Real.log (1 + t)) (nodes i) :=
    fun i => analyticAt_log_one_add (exp_sub_one_mem_Ioi_neg_one (points i))
  have h := hermiteWithDerivative_dividedDifference_remainder_zero nodes hinj hg
    analyticAt_log_one_add_zero
  have hprod := Finset.mul_prod_erase (Finset.univ : Finset (Fin (j + 1))) nodes
    (Finset.mem_univ 0)
  simp only [nodes, log_one_add_exp_sub_one, deriv_log_one_add_at_exp_sub_one,
    add_zero, Real.log_one, sub_zero] at h
  dsimp [exponentialHermitePolynomial]
  rw [h]
  dsimp [nodes] at hprod
  rw [← hprod]
  ring

/-- A finite normalized power limit forces the point itself to approach zero. -/
theorem tendsto_zero_of_normalized_pow {k : ℕ} (hk : 0 < k)
    (y : ℝ → ℝ) (c : ℝ)
    (hy : Tendsto (fun x => y x / x ^ k) (𝓝[≠] (0 : ℝ)) (𝓝 c)) :
    Tendsto y (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have hx : Tendsto (fun x : ℝ => x) (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hp : Tendsto (fun x : ℝ => x ^ k) (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [zero_pow (Nat.ne_of_gt hk)] using hx.pow k
  have hmul := hy.mul hp
  simp only [mul_zero] at hmul
  apply hmul.congr'
  filter_upwards [self_mem_nhdsWithin] with x (hx : x ≠ 0)
  exact div_mul_cancel₀ (y x) (pow_ne_zero k hx)

/-- Exponentiation preserves the leading normalized point coefficient.
Derivative-valued slopes include zero points, at zero as well. -/
theorem exp_sub_one_normalized_tendsto {k : ℕ} (hk : 0 < k)
    (y : ℝ → ℝ) (c : ℝ)
    (hy : Tendsto (fun x => y x / x ^ k) (𝓝[≠] (0 : ℝ)) (𝓝 c)) :
    Tendsto (fun x => (Real.exp (y x) - 1) / x ^ k)
      (𝓝[≠] (0 : ℝ)) (𝓝 c) := by
  have hyzero := tendsto_zero_of_normalized_pow hk y c hy
  have hcont : ContinuousAt (dslope Real.exp 0) 0 :=
    continuousAt_dslope_same.mpr (Real.hasDerivAt_exp 0).differentiableAt
  have hs : Tendsto (fun x => dslope Real.exp 0 (y x))
      (𝓝[≠] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    convert hcont.tendsto.comp hyzero using 1 <;>
      simp [Function.comp_def, dslope_same, Real.deriv_exp, Real.exp_zero]
  have hmul := hs.mul hy
  simp only [one_mul] at hmul
  apply hmul.congr
  intro x
  have hid : y x * dslope Real.exp 0 (y x) = Real.exp (y x) - 1 := by
    simpa only [sub_zero, smul_eq_mul, Real.exp_zero] using sub_smul_dslope Real.exp 0 (y x)
  rw [← hid]
  ring

/-- Normalizing the extra first factor and every indexed factor gives the
exact doubled exponent, including the singleton stage. -/
theorem normalized_hermite_product (j : ℕ) (v : Fin (j + 1) → ℝ) (x : ℝ) :
    v 0 * (∏ i, v i) / x ^ (2 ^ (j + 1)) =
      (v 0 / x) * ∏ i, (v i / x ^ (2 ^ i.val)) := by
  rw [Finset.prod_div_distrib, div_mul_div_comm, mul_prod_pow_two]

/-- One analytic step gives the next exact coefficient. Eventual
injectivity and all earlier asymptotics remain explicit hypotheses. -/
theorem exponentialHermiteStep_tendsto (j : ℕ)
    (points : ℝ → Fin (j + 1) → ℝ)
    (hinj : ∀ᶠ x in 𝓝[≠] (0 : ℝ), Function.Injective (points x))
    (hpoints : ∀ i, Tendsto (fun x => points x i / x ^ (2 ^ i.val))
      (𝓝[≠] (0 : ℝ)) (𝓝 (sharpnessCoefficient i.val))) :
    Tendsto (fun x => (exponentialHermitePolynomial (points x)).eval 0 /
      x ^ (2 ^ (j + 1))) (𝓝[≠] (0 : ℝ)) (𝓝 (sharpnessCoefficient (j + 1))) := by
  let nodes : ℝ → Fin (j + 1) → ℝ := fun x i => Real.exp (points x i) - 1
  have hnorm : ∀ i, Tendsto (fun x => nodes x i / x ^ (2 ^ i.val))
      (𝓝[≠] (0 : ℝ)) (𝓝 (sharpnessCoefficient i.val)) :=
    fun i => exp_sub_one_normalized_tendsto (by positivity) _ _ (hpoints i)
  have hzero : ∀ i, Tendsto (fun x => nodes x i) (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    fun i => tendsto_zero_of_normalized_pow (by positivity) _ _ (hnorm i)
  have hD := log_one_add_hermite_coefficient_tendsto j nodes hzero
  have hfirst : Tendsto (fun x => nodes x 0 / x) (𝓝[≠] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    simpa only [Fin.val_zero, pow_zero, pow_one, sharpnessCoefficient] using hnorm 0
  have hprod := tendsto_finsetProd (Finset.univ : Finset (Fin (j + 1)))
    (fun i _ => hnorm i)
  have hsign : Tendsto (fun _ : ℝ => (-1 : ℝ) ^ (j + 1))
      (𝓝[≠] (0 : ℝ)) (𝓝 ((-1 : ℝ) ^ (j + 1))) := tendsto_const_nhds
  have hlimit := ((hsign.mul hD).mul hfirst).mul hprod
  have hcoef : (-1 : ℝ) ^ (j + 1) * ((-1 : ℝ) ^ (j + 1) / ((j : ℝ) + 2)) * 1 *
      (∏ i : Fin (j + 1), sharpnessCoefficient i.val) = sharpnessCoefficient (j + 1) := by
    have hκzero : sharpnessCoefficient 0 = 1 := by rw [sharpnessCoefficient]
    calc
      _ = (∏ i : Fin j, sharpnessCoefficient (i.val + 1)) / ((j : ℝ) + 2) := by
        rw [Fin.prod_univ_succ]
        simp only [Fin.val_zero, Fin.val_succ, hκzero, one_mul, mul_one]
        rcases neg_one_pow_eq_or ℝ (j + 1) with hs | hs <;> rw [hs] <;> ring
      _ = _ := (sharpnessCoefficient_succ j).symm
  rw [hcoef] at hlimit
  apply hlimit.congr'
  filter_upwards [hinj] with x hxinj
  rw [exponentialHermitePolynomial_zero j (points x) hxinj]
  dsimp only [nodes]
  rw [show (-1 : ℝ) ^ (j + 1) *
      confluentDividedDifference (fun t : ℝ => Real.log (1 + t))
        (0 :: (Real.exp (points x 0) - 1) :: List.ofFn (fun i => Real.exp (points x i) - 1)) *
      (Real.exp (points x 0) - 1) * (∏ i, (Real.exp (points x i) - 1)) /
      x ^ (2 ^ (j + 1)) =
      ((-1 : ℝ) ^ (j + 1) *
        confluentDividedDifference (fun t : ℝ => Real.log (1 + t))
          (0 :: (Real.exp (points x 0) - 1) :: List.ofFn (fun i => Real.exp (points x i) - 1))) *
      ((Real.exp (points x 0) - 1) * (∏ i, (Real.exp (points x i) - 1)) /
        x ^ (2 ^ (j + 1))) by ring]
  rw [normalized_hermite_product j (fun i => Real.exp (points x i) - 1) x]
  ring

end KungTraubAppendices
