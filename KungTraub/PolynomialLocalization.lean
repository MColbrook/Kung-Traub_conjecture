import KungTraub.PolynomialFrames
import KungTraub.PolynomialBases
import KungTraub.PolynomialNormalization

/-!
# Uniform localisation of polynomial Wronskians

The compactness argument in Section 2.1 is assembled from actual subsequence,
root-multiplicity retention, root-persistence, and Wronskian classification theorems.
The unit-disc result is first proved for orthonormal coefficient frames. Gram--Schmidt
and scalar normalization remove those restrictions. The final result treats arbitrary
closed discs, including radius zero, and arbitrary bases of bounded-degree spaces.
Affine root transport reuses Mathlib's polynomial algebra automorphism and exact
root-multiplicity and root-multiset formulas.
-/

noncomputable section

open Filter Polynomial
open scoped BigOperators Topology

namespace KungTraub

/-- Uniform localisation in the unit disc for coefficient-orthonormal frames and a
normalized member. The constant depends only on the dimension and degree bound. -/
theorem polynomialWronskian_uniform_localization_normalized {m d : ℕ}
    (hm : 0 < m) (hmd : m ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Fin m → Polynomial ℂ) (q : Polynomial ℂ),
      (∀ i, (p i).natDegree ≤ d) → q.natDegree ≤ d →
      Orthonormal ℂ (fun i => coefficientVector d (p i)) →
      ‖coefficientVector d q‖ = 1 →
      q ∈ Submodule.span ℂ (Set.range p) →
      (∃ a : Fin m → ℂ, (∀ i, ‖a i‖ ≤ 1) ∧
        (List.ofFn a : Multiset ℂ) ≤ q.roots) →
      ∃ z : ℂ, ‖z‖ ≤ C ∧ (polynomialWronskian p).eval z = 0 := by
  classical
  by_contra! hnot
  have hbad (n : ℕ) := hnot ((n : ℝ) + 1) (by positivity)
  choose P Q hPdeg hQdeg hPortho hQnorm hQmem hQroots haway using hbad
  have hPind (n : ℕ) : LinearIndependent ℂ (P n) := by
    apply LinearIndependent.of_comp (polynomialCoefficientLinearMap d)
    change LinearIndependent ℂ (fun i => coefficientVector d (P n i))
    exact (hPortho n).linearIndependent
  have hQzero (n : ℕ) : Q n ≠ 0 := by
    intro hz
    have hcoefzero : coefficientVector d (Q n) = 0 := by
      ext i
      simp [hz, coefficientVector]
    have h := hQnorm n
    rw [hcoefzero, norm_zero] at h
    exact zero_ne_one h
  obtain ⟨p, q, hpdeg, hqdeg, hportho, hpind, hpdim,
      hqnorm, hqzero, hqmem, φ, hφ, hPlim, hQlim⟩ :=
    exists_polynomial_frame_member_subseq P Q hPdeg hQdeg hPortho hQnorm hQmem
  obtain ⟨a, ha, haroots, hacard⟩ :=
    polynomial_retains_roots_counted_with_multiplicity
      (m := m) (c := 0) (r := 1)
      (fun n => hQzero (φ n)) hqzero (fun n => hQdeg (φ n)) hQlim (by
        intro n
        simpa only [sub_zero] using hQroots (φ n))
  have hspace : Submodule.span ℂ (Set.range p) ≠ Polynomial.degreeLT ℂ m := by
    intro heq
    have hqsmall : q.natDegree < m := by
      have hmem : q ∈ Polynomial.degreeLT ℂ m := heq ▸ hqmem
      have hdegree := Polynomial.mem_degreeLT.mp hmem
      rw [Polynomial.degree_eq_natDegree hqzero] at hdegree
      exact WithBot.coe_lt_coe.mp hdegree
    have hcard : m ≤ q.natDegree := by
      rw [← hacard]
      exact (Multiset.card_le_card haroots).trans (Polynomial.card_roots' q)
    exact (not_lt_of_ge hcard) hqsmall
  obtain ⟨z, hz⟩ := (polynomialWronskian_has_root_iff_span_ne_degreeLT p hpind).mpr hspace
  have hWdeg (n : ℕ) : (polynomialWronskian (P (φ n))).natDegree ≤ m * (d + 1 - m) :=
    polynomialWronskian_natDegree_le hm (by omega) _ (hPind (φ n)) (hPdeg (φ n))
  have hWlim := polynomialWronskian_coeff_tendsto hPlim
  have hnear := polynomial_eventually_has_nearby_root_of_coeff_tendsto hWdeg hWlim
    (polynomialWronskian_ne_zero_of_linearIndependent p hpind) hz (show (0 : ℝ) < 1 by norm_num)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hnear
  obtain ⟨n, hn⟩ := exists_nat_gt (‖z‖ + 1)
  obtain ⟨β, hβ, hdist⟩ := hN (max N n) (le_max_left _ _)
  have hnφ : (n : ℝ) ≤ (φ (max N n) : ℝ) := by
    exact_mod_cast (le_max_right N n).trans (hφ.id_le (max N n))
  have hβbound : ‖β‖ ≤ (φ (max N n) : ℝ) + 1 := by
    have ht : ‖β‖ ≤ ‖z‖ + ‖z - β‖ := calc
      ‖β‖ = ‖z + (β - z)‖ := by congr 1; ring
      _ ≤ ‖z‖ + ‖β - z‖ := norm_add_le z (β - z)
      _ = ‖z‖ + ‖z - β‖ := by rw [norm_sub_rev]
    linarith
  exact haway (φ (max N n)) β hβbound hβ

/-- Removing the coefficient normalizations gives a uniform unit-disc statement for
every independent family. The member's degree bound follows from span membership. -/
theorem polynomialWronskian_uniform_localization_unitDisc {m d : ℕ}
    (hm : 0 < m) (hmd : m ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Fin m → Polynomial ℂ), LinearIndependent ℂ p →
      (∀ i, (p i).natDegree ≤ d) → ∀ q ∈ Submodule.span ℂ (Set.range p), q ≠ 0 →
      (∃ a : Fin m → ℂ, (∀ i, ‖a i‖ ≤ 1) ∧
        (List.ofFn a : Multiset ℂ) ≤ q.roots) →
      ∃ z : ℂ, ‖z‖ ≤ C ∧ (polynomialWronskian p).eval z = 0 := by
  obtain ⟨C, hC, hbound⟩ := polynomialWronskian_uniform_localization_normalized hm hmd
  refine ⟨C, hC, fun p hp hdeg q hqmem hqzero hroots => ?_⟩
  obtain ⟨P, hPdeg, hPortho, hPind, hPspan⟩ :=
    exists_polynomial_coefficient_orthonormal_frame p hp hdeg
  have hqdeg := polynomial_natDegree_le_of_mem_span p hdeg hqmem
  obtain ⟨c, Q, hc, hQ, hQdeg, hQnorm, hQroots⟩ :=
    exists_polynomial_unit_coefficient_norm q hqzero hqdeg
  have hQmem : Q ∈ Submodule.span ℂ (Set.range P) := by
    rw [hPspan, hQ]
    exact Submodule.smul_mem _ c hqmem
  obtain ⟨z, hz, hWz⟩ := hbound P Q hPdeg hQdeg hPortho hQnorm hQmem (by
    simpa only [hQroots] using hroots)
  refine ⟨z, hz, (polynomialWronskian_eval_eq_zero_iff_span p hp z).mpr ?_⟩
  rw [← hPspan]
  exact (polynomialWronskian_eval_eq_zero_iff_span P hPind z).mp hWz

/-- Composition with an invertible affine polynomial preserves family independence. -/
theorem polynomial_affine_family_linearIndependent {m : ℕ}
    (p : Fin m → Polynomial ℂ) (hp : LinearIndependent ℂ p)
    (a b : ℂ) (hb : b ≠ 0) :
    LinearIndependent ℂ (fun i => (p i).comp (Polynomial.C b * Polynomial.X + Polynomial.C a)) := by
  let : Invertible b := (isUnit_iff_ne_zero.mpr hb).invertible
  let e := Polynomial.algEquivCMulXAddC b a
  change LinearIndependent ℂ (e.toLinearMap ∘ p)
  exact hp.map' e.toLinearMap (LinearMap.ker_eq_bot.mpr e.injective)

/-- An affine change of variable transports a Wronskian zero, via the intrinsic
root-multiplicity criterion. No determinant scaling formula is assumed. -/
theorem polynomialWronskian_affine_zero {m : ℕ} (hm : 0 < m)
    (p : Fin m → Polynomial ℂ) (hp : LinearIndependent ℂ p)
    (a b : ℂ) (hb : b ≠ 0) (z : ℂ)
    (hz : (polynomialWronskian
      (fun i => (p i).comp (Polynomial.C b * Polynomial.X + Polynomial.C a))).eval z = 0) :
    (polynomialWronskian p).eval (b * z + a) = 0 := by
  let : Invertible b := (isUnit_iff_ne_zero.mpr hb).invertible
  let e := Polynomial.algEquivCMulXAddC b a
  have hp' := polynomial_affine_family_linearIndependent p hp a b hb
  obtain ⟨Q, hQmem, hQzero, hQmult⟩ :=
    (polynomialWronskian_eval_eq_zero_iff_multiplicity hm _ hp' z).mp hz
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hQmem
  let q : Polynomial ℂ := ∑ i, c i • p i
  have heq : e q = Q := by
    simpa only [q, map_sum, map_smul, e, Polynomial.algEquivCMulXAddC_apply,
      ← Polynomial.comp_eq_aeval] using hc
  have hqzero : q ≠ 0 := by
    intro hq
    apply hQzero
    rw [← heq, hq, map_zero]
  apply (polynomialWronskian_eval_eq_zero_iff_multiplicity hm p hp (b * z + a)).mpr
  refine ⟨q, (Submodule.mem_span_range_iff_exists_fun ℂ).mpr ⟨c, rfl⟩, hqzero, ?_⟩
  have hmult := Polynomial.rootMultiplicity_comp_C_mul_X_add_C q b a z
    (isUnit_iff_ne_zero.mpr hb)
  change (e q).rootMultiplicity z = q.rootMultiplicity (b * z + a) at hmult
  rw [heq] at hmult
  exact hmult ▸ hQmult

/-- The manuscript's uniform localization lemma for arbitrary closed discs, with
multiplicity counted in the root multiset. The radius may be zero. -/
theorem polynomialWronskian_uniform_localization {m d : ℕ}
    (hm : 0 < m) (hmd : m ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (p : Fin m → Polynomial ℂ), LinearIndependent ℂ p →
      (∀ i, (p i).natDegree ≤ d) → ∀ (a : ℂ) (r : ℝ), 0 ≤ r →
      ∀ q ∈ Submodule.span ℂ (Set.range p), q ≠ 0 →
      (∃ z : Fin m → ℂ, (∀ i, ‖z i - a‖ ≤ r) ∧
        (List.ofFn z : Multiset ℂ) ≤ q.roots) →
      ∃ z : ℂ, ‖z - a‖ ≤ C * r ∧ (polynomialWronskian p).eval z = 0 := by
  classical
  obtain ⟨C, hC, hunit⟩ := polynomialWronskian_uniform_localization_unitDisc hm hmd
  refine ⟨C, hC, fun p hp hdeg a r hr q hqmem hqzero hroots => ?_⟩
  obtain ⟨z, hz, hzroots⟩ := hroots
  rcases eq_or_lt_of_le hr with hrzero | hrpos
  · subst r
    have hza (i : Fin m) : z i = a := sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (hz i) (norm_nonneg _)))
    have hmultiplicity : m ≤ q.rootMultiplicity a := by
      have hc := Multiset.count_le_of_le a hzroots
      simpa only [show z = (fun _ => a) from funext hza, List.ofFn_const,
        Multiset.coe_replicate, Multiset.count_replicate_self, Polynomial.count_roots] using hc
    refine ⟨a, by simp, ?_⟩
    exact (polynomialWronskian_eval_eq_zero_iff_multiplicity hm p hp a).mpr
      ⟨q, hqmem, hqzero, hmultiplicity⟩
  · have hrcomplex : (r : ℂ) ≠ 0 := by exact_mod_cast hrpos.ne'
    let : Invertible (r : ℂ) := (isUnit_iff_ne_zero.mpr hrcomplex).invertible
    let e := Polynomial.algEquivCMulXAddC (r : ℂ) a
    let P : Fin m → Polynomial ℂ := fun i => e (p i)
    have hPind : LinearIndependent ℂ P :=
      polynomial_affine_family_linearIndependent p hp a (r : ℂ) hrcomplex
    have hPdeg (i : Fin m) : (P i).natDegree ≤ d := by
      change ((p i).comp (Polynomial.C (r : ℂ) * Polynomial.X + Polynomial.C a)).natDegree ≤ d
      rw [Polynomial.natDegree_comp, Polynomial.natDegree_linear hrcomplex, mul_one]
      exact hdeg i
    have hqmem' : e q ∈ Submodule.span ℂ (Set.range P) := by
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hqmem
      apply (Submodule.mem_span_range_iff_exists_fun ℂ).mpr
      refine ⟨c, ?_⟩
      simpa only [map_sum, map_smul] using congrArg e hc
    have hqzero' : e q ≠ 0 := by
      intro hzero
      exact hqzero (e.injective (hzero.trans (map_zero e).symm))
    have hrootnorm (i : Fin m) : ‖(r : ℂ)⁻¹ * (z i - a)‖ ≤ 1 := by
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos]
      have h := mul_le_mul_of_nonneg_left (hz i) (inv_nonneg.mpr hr)
      simpa only [inv_mul_cancel₀ hrpos.ne'] using h
    have hroots' : ∃ w : Fin m → ℂ, (∀ i, ‖w i‖ ≤ 1) ∧
        (List.ofFn w : Multiset ℂ) ≤ (e q).roots := by
      refine ⟨fun i => (r : ℂ)⁻¹ * (z i - a), hrootnorm, ?_⟩
      change (List.ofFn (fun i => (r : ℂ)⁻¹ * (z i - a)) : Multiset ℂ) ≤
        (q.comp (Polynomial.C (r : ℂ) * Polynomial.X + Polynomial.C a)).roots
      rw [Polynomial.roots_comp_C_mul_X_add_C q (r : ℂ) a
        (isUnit_iff_ne_zero.mpr hrcomplex)]
      simp only [Ring.inverse_eq_inv]
      simpa only [Multiset.map_coe, List.map_ofFn, Function.comp_def] using
        (Multiset.map_le_map (f := fun w : ℂ => (r : ℂ)⁻¹ * (w - a)) hzroots)
    obtain ⟨w, hw, hW⟩ := hunit P hPind hPdeg (e q) hqmem' hqzero' hroots'
    refine ⟨(r : ℂ) * w + a, ?_, ?_⟩
    · rw [add_sub_cancel_right, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos]
      simpa only [mul_comm C r] using mul_le_mul_of_nonneg_left hw hr
    · exact polynomialWronskian_affine_zero hm p hp a (r : ℂ) hrcomplex w hW

/-- The space-and-basis formulation of uniform localization. The same constant works
for every `m`-dimensional space of polynomials of degree at most `d`, every chosen basis,
and every closed disc. -/
theorem polynomialWronskian_uniform_localization_basis {m d : ℕ}
    (hm : 0 < m) (hmd : m ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Submodule ℂ (Polynomial ℂ)),
      (∀ q ∈ V, q.natDegree ≤ d) → ∀ (b : Module.Basis (Fin m) ℂ V),
      ∀ (a : ℂ) (r : ℝ), 0 ≤ r → ∀ q ∈ V, q ≠ 0 →
      (∃ z : Fin m → ℂ, (∀ i, ‖z i - a‖ ≤ r) ∧
        (List.ofFn z : Multiset ℂ) ≤ q.roots) →
      ∃ z : ℂ, ‖z - a‖ ≤ C * r ∧
        (polynomialWronskian (fun i => (b i : Polynomial ℂ))).eval z = 0 := by
  obtain ⟨C, hC, hbound⟩ := polynomialWronskian_uniform_localization hm hmd
  refine ⟨C, hC, fun V hV b a r hr q hq hqzero hroots => ?_⟩
  let p : Fin m → Polynomial ℂ := fun i => b i
  have hp : LinearIndependent ℂ p := b.linearIndependent.map' V.subtype (by simp)
  have hspan : Submodule.span ℂ (Set.range p) = V := by
    change Submodule.span ℂ (Set.range (V.subtype ∘ b)) = V
    rw [Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  exact hbound p hp (fun i => hV (b i) (b i).property) a r hr q
    (hspan.symm ▸ hq) hqzero hroots

end KungTraub
