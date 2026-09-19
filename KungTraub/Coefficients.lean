import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic

/-!
# Polynomial coefficient estimates

Supporting estimates for Lemma 2.2 of Matthew J. Colbrook's
`kung_traub_solution.tex`. The Euclidean coefficient norm and the inverse
constant-coordinate scaling are explicit. The argument is adapted from the
author's proof; general norm and arithmetic facts are supplied by Mathlib.

The estimates include the numerical series identity used in the derivative bound.
-/

namespace KungTraub

noncomputable section

open scoped BigOperators

/-- The coefficient vector of a degree-at-most-`n` polynomial, with the
Euclidean norm rather than the supremum norm of a function space. -/
def coefficientVector (n : ℕ) (q : Polynomial ℂ) :
    EuclideanSpace ℂ (Fin (n + 1)) :=
  WithLp.toLp 2 (fun i => q.coeff i.val)

/-- Inverse of the scaling of the constant coefficient by a real number. -/
def inverseConstantScale {n : ℕ} (ε : ℝ)
    (b : EuclideanSpace ℂ (Fin (n + 1))) :
    EuclideanSpace ℂ (Fin (n + 1)) :=
  WithLp.toLp 2 (fun i => if i = 0 then b i / (ε : ℂ) else b i)

/-- The Euclidean norm is bounded by the sum of coordinate norms. -/
theorem euclidean_norm_le_sum {ι : Type*} [Fintype ι]
    (b : EuclideanSpace ℂ ι) : ‖b‖ ≤ ∑ i, ‖b i‖ := by
  have hs := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ) (f := fun i => ‖b i‖) (fun i _ => norm_nonneg (b i))
  rw [← EuclideanSpace.norm_sq_eq] at hs
  have hp : 0 ≤ ∑ i, ‖b i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg (b i))
  nlinarith [norm_nonneg b]

/-- The elementary coefficient bound needed in the product estimate.
This uses Mathlib's `Polynomial.norm_coeff_le_choose_mul_mahlerMeasure`,
in the module by Fabrizio Barroero and Kevin H. Wilson. -/
theorem coefficientVector_norm_le_mahler {n : ℕ} (q : Polynomial ℂ)
    (hq : q.natDegree ≤ n) :
    ‖coefficientVector n q‖ ≤ 2 ^ q.natDegree * q.mahlerMeasure := by
  calc
    ‖coefficientVector n q‖ ≤ ∑ i : Fin (n + 1), ‖q.coeff i.val‖ :=
      euclidean_norm_le_sum (coefficientVector n q)
    _ = ∑ i ∈ Finset.range (q.natDegree + 1), ‖q.coeff i‖ := by
      rw [Fin.sum_univ_eq_sum_range (fun i => ‖q.coeff i‖)]
      rw [← q.sum_over_range' (f := fun _ z => ‖z‖) (by simp) (n + 1) (by omega)]
      exact q.sum_over_range (by simp)
    _ ≤ ∑ i ∈ Finset.range (q.natDegree + 1),
        (q.natDegree.choose i : ℝ) * q.mahlerMeasure := by
      exact Finset.sum_le_sum (fun i _ => q.norm_coeff_le_choose_mul_mahlerMeasure i)
    _ = 2 ^ q.natDegree * q.mahlerMeasure := by
      rw [← Finset.sum_mul]
      congr 1
      exact_mod_cast Nat.sum_range_choose q.natDegree

/-- A single normalized root factor on the closed half-unit disc. -/
theorem root_factor_bound {a β : ℂ} (ha : ‖a‖ ≤ 1 / 2) :
    max 1 ‖β‖ * min 1 ‖a - β‖ ≤ 2 * ‖a - β‖ := by
  have hd := norm_nonneg (a - β)
  by_cases hb : ‖β‖ ≤ 1
  · rw [max_eq_left hb, one_mul]
    exact (min_le_right _ _).trans (by linarith)
  · rw [max_eq_right (le_of_not_ge hb)]
    have htriangle : ‖β‖ ≤ ‖a - β‖ + ‖a‖ := by
      calc
        ‖β‖ = ‖β - a + a‖ := by congr 1; ring
        _ ≤ ‖β - a‖ + ‖a‖ := norm_add_le _ _
        _ = ‖a - β‖ + ‖a‖ := by rw [norm_sub_rev]
    have hdist : 1 / 2 ≤ ‖a - β‖ := by linarith
    have hmin : min 1 ‖a - β‖ ≤ 1 := min_le_left _ _
    have hmul := mul_le_mul_of_nonneg_left hmin (norm_nonneg β)
    nlinarith

/-- The root-factor bound with roots counted with multiplicity. -/
theorem root_product_bound (s : Multiset ℂ) {a : ℂ} (ha : ‖a‖ ≤ 1 / 2) :
    (s.map (fun β => max 1 ‖β‖)).prod *
      (s.map (fun β => min 1 ‖a - β‖)).prod ≤
    2 ^ s.card * ‖(s.map (fun β => a - β)).prod‖ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons β s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, norm_mul]
    have hnonneg : 0 ≤ (s.map (fun β => max 1 ‖β‖)).prod *
        (s.map (fun β => min 1 ‖a - β‖)).prod := by
      apply mul_nonneg
      · exact Multiset.prod_nonneg (by intro x hx; obtain ⟨z, _, rfl⟩ := Multiset.mem_map.mp hx; positivity)
      · exact Multiset.prod_nonneg (by intro x hx; obtain ⟨z, _, rfl⟩ := Multiset.mem_map.mp hx; positivity)
    have hfirst := root_factor_bound (β := β) ha
    have h := mul_le_mul hfirst ih hnonneg (by positivity : 0 ≤ 2 * ‖a - β‖)
    calc
      (max 1 ‖β‖ * (s.map (fun β => max 1 ‖β‖)).prod) *
          (min 1 ‖a - β‖ * (s.map (fun β => min 1 ‖a - β‖)).prod) =
        (max 1 ‖β‖ * min 1 ‖a - β‖) *
          ((s.map (fun β => max 1 ‖β‖)).prod *
            (s.map (fun β => min 1 ‖a - β‖)).prod) := by ring
      _ ≤ (2 * ‖a - β‖) * (2 ^ s.card * ‖(s.map (fun β => a - β)).prod‖) := h
      _ = 2 ^ (s.card + 1) * (‖a - β‖ * ‖(s.map (fun β => a - β)).prod‖) := by
        rw [pow_succ]
        ring

/-- Lemma 2.2's product estimate, in division form, on the full stated domain. -/
theorem polynomial_product_estimate {n : ℕ} (q : Polynomial ℂ)
    (hq : q.natDegree ≤ n) (hnorm : ‖coefficientVector n q‖ = 1)
    {a : ℂ} (ha : ‖a‖ ≤ 1 / 2) :
    (q.roots.map (fun β => min 1 ‖a - β‖)).prod / 4 ^ q.natDegree ≤
      ‖q.eval a‖ := by
  have hcoeff := coefficientVector_norm_le_mahler q hq
  rw [hnorm, q.mahlerMeasure_eq_leadingCoeff_mul_prod_roots] at hcoeff
  have hprod := root_product_bound q.roots ha
  have hcard : q.roots.card = q.natDegree :=
    Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits q)
  rw [hcard] at hprod
  have hnonneg : 0 ≤ (q.roots.map (fun β => min 1 ‖a - β‖)).prod :=
    Multiset.prod_nonneg (by intro x hx; obtain ⟨z, _, rfl⟩ := Multiset.mem_map.mp hx; positivity)
  have hfirst := mul_le_mul_of_nonneg_right hcoeff hnonneg
  have hsecond := mul_le_mul_of_nonneg_left hprod
    (show 0 ≤ 2 ^ q.natDegree * ‖q.leadingCoeff‖ by positivity)
  have heval := (IsAlgClosed.splits q).eval_eq_prod_roots a
  have hevalnorm : ‖q.eval a‖ =
      ‖q.leadingCoeff‖ * ‖(q.roots.map (fun β => a - β)).prod‖ := by
    rw [heval, norm_mul]
  have hpow : (2 : ℝ) ^ q.natDegree * 2 ^ q.natDegree = 4 ^ q.natDegree := by
    rw [← mul_pow]
    norm_num
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 ^ q.natDegree)).2
  rw [hevalnorm]
  calc
    (q.roots.map (fun β => min 1 ‖a - β‖)).prod ≤
        (2 ^ q.natDegree * ‖q.leadingCoeff‖) *
          ((q.roots.map (fun β => max 1 ‖β‖)).prod *
            (q.roots.map (fun β => min 1 ‖a - β‖)).prod) := by
      nlinarith only [hfirst]
    _ ≤ (2 ^ q.natDegree * ‖q.leadingCoeff‖) *
        (2 ^ q.natDegree * ‖(q.roots.map (fun β => a - β)).prod‖) := hsecond
    _ = (‖q.leadingCoeff‖ * ‖(q.roots.map (fun β => a - β)).prod‖) *
        4 ^ q.natDegree := by
      calc
        _ = (‖q.leadingCoeff‖ * ‖(q.roots.map (fun β => a - β)).prod‖) *
            (2 ^ q.natDegree * 2 ^ q.natDegree) := by ring
        _ = _ := by rw [hpow]

/-- Coordinatewise domination implies domination of the Euclidean norm. -/
theorem euclidean_norm_mono {ι : Type*} [Fintype ι]
    (b c : EuclideanSpace ℂ ι) (h : ∀ i, ‖b i‖ ≤ ‖c i‖) : ‖b‖ ≤ ‖c‖ := by
  have hs : ∑ i, ‖b i‖ ^ 2 ≤ ∑ i, ‖c i‖ ^ 2 := by
    exact Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (norm_nonneg (b i)) (h i) 2)
  rw [← EuclideanSpace.norm_sq_eq, ← EuclideanSpace.norm_sq_eq] at hs
  nlinarith [norm_nonneg b, norm_nonneg c]

/-- Scaling only the constant coordinate gives the required dimension-free bound. -/
theorem inverseConstantScale_norm_le {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (b : EuclideanSpace ℂ (Fin (n + 1))) :
    ‖inverseConstantScale ε b‖ ≤ ‖b 0‖ / ε + ‖b‖ := by
  have hpoint (i : Fin (n + 1)) : ‖inverseConstantScale ε b i‖ ^ 2 ≤
      (if i = 0 then (‖b 0‖ / ε) ^ 2 else 0) + ‖b i‖ ^ 2 := by
    by_cases hi : i = 0 <;>
      simp [inverseConstantScale, hi, abs_of_pos hε]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpoint i)
  rw [Finset.sum_add_distrib] at hs
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at hs
  rw [← EuclideanSpace.norm_sq_eq, ← EuclideanSpace.norm_sq_eq] at hs
  have hquot : 0 ≤ ‖b 0‖ / ε := div_nonneg (norm_nonneg _) (le_of_lt hε)
  nlinarith [norm_nonneg b, norm_nonneg (inverseConstantScale ε b)]

/-- A nonzero coefficient vector remains nonzero under positive inverse scaling. -/
theorem inverseConstantScale_norm_pos {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (b : EuclideanSpace ℂ (Fin (n + 1))) (hb : ‖b‖ = 1) :
    0 < ‖inverseConstantScale ε b‖ := by
  apply norm_pos_iff.mpr
  intro hz
  have heps : (ε : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hε
  have hbzero : b = 0 := by
    ext i
    have hi := congrArg (fun v : EuclideanSpace ℂ (Fin (n + 1)) => v i) hz
    by_cases hi0 : i = 0
    · simpa [inverseConstantScale, hi0, heps] using hi
    · simpa [inverseConstantScale, hi0] using hi
  simp [hbzero] at hb

/-- A finite geometric sum on the closed half-unit interval. -/
theorem sum_powers_le_two {r : ℝ} (hr : 0 ≤ r) (hrhalf : r ≤ 1 / 2) (n : ℕ) :
    ∑ k ∈ Finset.range n, r ^ k ≤ 2 := by
  have hgeom := geom_sum_mul_neg r n
  have hs : 0 ≤ ∑ k ∈ Finset.range n, r ^ k :=
    Finset.sum_nonneg (fun k _ => pow_nonneg hr k)
  have hp := pow_nonneg hr n
  nlinarith

/-- The numerical series in the manuscript's derivative estimate, reindexed from zero. -/
theorem derivative_coefficient_series :
    HasSum (fun k : ℕ => ((k : ℝ) + 1) ^ 2 * (1 / 2 : ℝ) ^ (2 * k))
      (80 / 27 : ℝ) := by
  have hr : ‖(1 / 4 : ℝ)‖ < 1 := by norm_num
  have htwo := hasSum_choose_mul_geometric_of_norm_lt_one 2 hr
  have hone := hasSum_choose_mul_geometric_of_norm_lt_one 1 hr
  convert! (htwo.mul_left (2 : ℝ)).sub hone using 1
  · ext k
    rw [Nat.cast_choose_two]
    simp only [Nat.choose_one_right, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
    have hp : (1 / 2 : ℝ) ^ (2 * k) = (1 / 4 : ℝ) ^ k := by
      rw [pow_mul]
      norm_num
    rw [hp]
    ring
  · norm_num

theorem derivative_coefficient_series_sqrt_lt_two :
    Real.sqrt (80 / 27 : ℝ) < 2 := by
  rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2)]
  norm_num

/-- Unit Euclidean coefficient norm controls the change from the constant term.
A finite geometric sum suffices here; no derivative regularity is assumed. -/
theorem polynomial_eval_sub_constant_le {n : ℕ} (q : Polynomial ℂ)
    (hq : q.natDegree ≤ n) (hnorm : ‖coefficientVector n q‖ = 1)
    {a : ℂ} (ha : ‖a‖ ≤ 1 / 2) :
    ‖q.eval a - q.coeff 0‖ ≤ 2 * ‖a‖ := by
  have heval : q.eval a - q.coeff 0 =
      ∑ k ∈ Finset.range n, q.coeff (k + 1) * a ^ (k + 1) := by
    rw [Polynomial.eval_eq_sum_range' (show q.natDegree < n + 1 by omega) a,
      Finset.sum_range_succ']
    simp
  rw [heval]
  calc
    ‖∑ k ∈ Finset.range n, q.coeff (k + 1) * a ^ (k + 1)‖ ≤
        ∑ k ∈ Finset.range n, ‖q.coeff (k + 1) * a ^ (k + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range n, ‖a‖ ^ (k + 1) := by
      apply Finset.sum_le_sum
      intro k hk
      have hk' : k + 1 < n + 1 := by simpa using hk
      have hc := PiLp.norm_apply_le (coefficientVector n q) ⟨k + 1, hk'⟩
      rw [hnorm] at hc
      change ‖q.coeff (k + 1)‖ ≤ 1 at hc
      simpa only [norm_mul, norm_pow, one_mul] using
        mul_le_mul_of_nonneg_right hc (pow_nonneg (norm_nonneg a) (k + 1))
    _ = ‖a‖ * ∑ k ∈ Finset.range n, ‖a‖ ^ k := by
      simp [Finset.mul_sum, pow_succ']
    _ ≤ ‖a‖ * 2 := mul_le_mul_of_nonneg_left
      (sum_powers_le_two (norm_nonneg a) ha n) (norm_nonneg a)
    _ = 2 * ‖a‖ := mul_comm _ _

/-- The final real inequality in the scaled-norm estimate. -/
theorem scaled_ratio_bound {x D ε R : ℝ} (hx : 0 ≤ x) (hD : 0 < D)
    (hε : 0 < ε) (hR : 0 ≤ R) (hbound : D ≤ x / ε + 2 * R + 1) :
    min ε x / (2 * R + 2) ≤ x / D := by
  have hden : 0 < 2 * R + 2 := by positivity
  apply (div_le_div_iff₀ hden hD).2
  rcases le_total x ε with hsmall | hlarge
  · rw [min_eq_right hsmall]
    have hquot : x / ε ≤ 1 := (div_le_one hε).2 hsmall
    have hD' : D ≤ 2 * R + 2 := by linarith
    exact mul_le_mul_of_nonneg_left hD' hx
  · rw [min_eq_left hlarge]
    have hquot : D - (2 * R + 1) ≤ x / ε := by linarith
    have hmul := (le_div_iff₀ hε).1 hquot
    have hlarge' := mul_le_mul_of_nonneg_right hlarge
      (show 0 ≤ 2 * R + 1 by positivity)
    nlinarith

/-- Lemma 2.2's scaled estimate, including degree zero and all positive scales. -/
theorem polynomial_scaled_estimate {n : ℕ} (q : Polynomial ℂ)
    (hq : q.natDegree ≤ n) (hnorm : ‖coefficientVector n q‖ = 1)
    {a : ℂ} {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R)
    (ha : ‖a‖ ≤ R * ε) (hhalf : R * ε ≤ 1 / 2) :
    min ε ‖q.eval a‖ / (2 * R + 2) ≤
      ‖q.eval a‖ / ‖inverseConstantScale ε (coefficientVector n q)‖ := by
  have hdiff := polynomial_eval_sub_constant_le q hq hnorm (ha.trans hhalf)
  have hc : ‖q.coeff 0‖ ≤ ‖q.eval a‖ + 2 * R * ε := by
    have htriangle : ‖q.coeff 0‖ ≤ ‖q.eval a‖ + ‖q.eval a - q.coeff 0‖ := by
      calc
        ‖q.coeff 0‖ = ‖q.eval a - (q.eval a - q.coeff 0)‖ := by congr 1; ring
        _ ≤ ‖q.eval a‖ + ‖q.eval a - q.coeff 0‖ := norm_sub_le _ _
    nlinarith
  have hinv := inverseConstantScale_norm_le hε (coefficientVector n q)
  rw [hnorm] at hinv
  change ‖inverseConstantScale ε (coefficientVector n q)‖ ≤ ‖q.coeff 0‖ / ε + 1 at hinv
  have hcdiv : ‖q.coeff 0‖ / ε ≤ ‖q.eval a‖ / ε + 2 * R := by
    apply (div_le_iff₀ hε).2
    have hcancel : (‖q.eval a‖ / ε) * ε = ‖q.eval a‖ := div_mul_cancel₀ _ (ne_of_gt hε)
    nlinarith
  exact scaled_ratio_bound (norm_nonneg _) (inverseConstantScale_norm_pos hε _ hnorm)
    hε (le_of_lt hR) (by linarith)

end

end KungTraub
