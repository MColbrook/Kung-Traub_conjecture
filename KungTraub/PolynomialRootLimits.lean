import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Topology.Sequences
import Mathlib.Tactic

/-!
# Roots of bounded-degree polynomial limits

The compactness proof of Wronskian localisation in Section 2.1 of the manuscript uses
coefficientwise limits of complex polynomials of uniformly bounded degree. Selected roots
are represented by linear factors, so repetition in a tuple retains multiplicity.

The proofs use Mathlib's explicit coefficients for division by `X - C a`, finite-sum limit
rules, complex polynomial factorisation, and sequential compactness of finite products of
closed discs. No constancy of the polynomial degree or monicity of the inputs is assumed.
The division module is by Chris Hughes, Johannes Hölzl, Kim Morrison and Jens Wagemaker;
the sequential compactness module is by Jan-David Salchow, Patrick Massot and Yury Kudryashov.
The nearby-root argument below uses a direct factor comparison, which also covers degree
loss not covered by Mathlib's monic, equal-degree approximation theorem.
-/

noncomputable section

open Filter Polynomial
open scoped BigOperators Topology

namespace KungTraub

/-- A coefficientwise limit retains a common upper bound on the degrees. -/
theorem polynomial_natDegree_le_of_coeff_tendsto {P : ℕ → Polynomial ℂ}
    {p : Polynomial ℂ} {d : ℕ} (hdeg : ∀ n, (P n).natDegree ≤ d)
    (hcoeff : ∀ k, Tendsto (fun n => (P n).coeff k) atTop (𝓝 (p.coeff k))) :
    p.natDegree ≤ d := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  have hz : ∀ n, (P n).coeff k = 0 := fun n =>
    Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hdeg n) hk)
  have hzero : Tendsto (fun n => (P n).coeff k) atTop (𝓝 0) := by
    simpa only [hz] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ))
      atTop (𝓝 0))
  exact tendsto_nhds_unique (hcoeff k) hzero

/-- Evaluation at convergent points respects bounded-degree coefficient convergence. -/
theorem polynomial_eval_tendsto_of_coeff_tendsto {P : ℕ → Polynomial ℂ}
    {p : Polynomial ℂ} {d : ℕ} (hdeg : ∀ n, (P n).natDegree ≤ d)
    (hcoeff : ∀ k, Tendsto (fun n => (P n).coeff k) atTop (𝓝 (p.coeff k)))
    {z : ℕ → ℂ} {a : ℂ} (hz : Tendsto z atTop (𝓝 a)) :
    Tendsto (fun n => (P n).eval (z n)) atTop (𝓝 (p.eval a)) := by
  have hpdeg := polynomial_natDegree_le_of_coeff_tendsto hdeg hcoeff
  have heval (n : ℕ) : (P n).eval (z n) =
      ∑ k ∈ Finset.range (d + 1), (P n).coeff k * z n ^ k :=
    Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (hdeg n)) (z n)
  have hevalp : p.eval a = ∑ k ∈ Finset.range (d + 1), p.coeff k * a ^ k :=
    Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hpdeg) a
  simp only [heval, hevalp]
  exact tendsto_finsetSum _ fun k _ => (hcoeff k).mul (hz.pow k)

/-- Synthetic division has a finite coefficient formula with a common degree bound. -/
theorem polynomial_coeff_divByMonic_X_sub_C_of_degree_le (p : Polynomial ℂ)
    {d : ℕ} (hdeg : p.natDegree ≤ d) (a : ℂ) (k : ℕ) :
    (p /ₘ (X - C a)).coeff k =
      ∑ i ∈ Finset.Icc (k + 1) d, a ^ (i - (k + 1)) * p.coeff i := by
  rw [Polynomial.coeff_divByMonic_X_sub_C]
  apply Finset.sum_subset
  · exact Finset.Icc_subset_Icc_right hdeg
  · intro i hi hnot
    have hlarge : p.natDegree < i := by
      simp only [Finset.mem_Icc] at hi hnot
      omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlarge, mul_zero]

/-- Coefficients of the synthetic quotient converge when the input coefficients and the
selected divisor root converge. No nonvanishing leading coefficient is needed. -/
theorem polynomial_divByMonic_X_sub_C_coeff_tendsto {P : ℕ → Polynomial ℂ}
    {p : Polynomial ℂ} {d : ℕ} (hdeg : ∀ n, (P n).natDegree ≤ d)
    (hcoeff : ∀ k, Tendsto (fun n => (P n).coeff k) atTop (𝓝 (p.coeff k)))
    {z : ℕ → ℂ} {a : ℂ} (hz : Tendsto z atTop (𝓝 a)) (k : ℕ) :
    Tendsto (fun n => (P n /ₘ (X - C (z n))).coeff k) atTop
      (𝓝 ((p /ₘ (X - C a)).coeff k)) := by
  have hpdeg := polynomial_natDegree_le_of_coeff_tendsto hdeg hcoeff
  simp only [polynomial_coeff_divByMonic_X_sub_C_of_degree_le _ (hdeg _),
    polynomial_coeff_divByMonic_X_sub_C_of_degree_le _ hpdeg]
  exact tendsto_finsetSum _ fun i _ => (hz.pow (i - (k + 1))).mul (hcoeff i)

/-- The monic factor containing a prescribed tuple of roots, including repeated roots. -/
def polynomialRootFactor {m : ℕ} (z : Fin m → ℂ) : Polynomial ℂ :=
  ∏ i, (X - C (z i))

/-- A tuple factor divides a nonzero polynomial exactly when its root multiset is a
submultiset of the polynomial's roots. Thus the representation retains multiplicity. -/
theorem polynomialRootFactor_dvd_iff_le_roots {m : ℕ} (z : Fin m → ℂ)
    {p : Polynomial ℂ} (hp : p ≠ 0) :
    polynomialRootFactor z ∣ p ↔ (List.ofFn z : Multiset ℂ) ≤ p.roots := by
  simpa [polynomialRootFactor, Multiset.map_coe, Multiset.prod_coe,
    List.map_ofFn, List.prod_ofFn, Function.comp_def] using
    (Multiset.prod_X_sub_C_dvd_iff_le_roots hp (List.ofFn z : Multiset ℂ))

/-- Limits of selected root factors still divide the coefficientwise polynomial limit.
This includes coalescing roots and retains every repeated linear factor. -/
theorem polynomialRootFactor_dvd_of_coeff_tendsto {m d : ℕ}
    {P : ℕ → Polynomial ℂ} {p : Polynomial ℂ}
    (hdeg : ∀ n, (P n).natDegree ≤ d)
    (hcoeff : ∀ k, Tendsto (fun n => (P n).coeff k) atTop (𝓝 (p.coeff k)))
    (z : ℕ → Fin m → ℂ) (a : Fin m → ℂ)
    (hz : ∀ i, Tendsto (fun n => z n i) atTop (𝓝 (a i)))
    (hdiv : ∀ n, polynomialRootFactor (z n) ∣ P n) : polynomialRootFactor a ∣ p := by
  induction m generalizing P p with
  | zero => simp [polynomialRootFactor]
  | succ m ih =>
    let Q : ℕ → Polynomial ℂ := fun n => P n /ₘ (X - C (z n 0))
    let q : Polynomial ℂ := p /ₘ (X - C (a 0))
    have hQdeg : ∀ n, (Q n).natDegree ≤ d := by
      intro n
      dsimp [Q]
      rw [Polynomial.natDegree_divByMonic _ (Polynomial.monic_X_sub_C _)]
      exact (Nat.sub_le _ _).trans (hdeg n)
    have hQcoeff : ∀ k, Tendsto (fun n => (Q n).coeff k) atTop (𝓝 (q.coeff k)) :=
      polynomial_divByMonic_X_sub_C_coeff_tendsto hdeg hcoeff (hz 0)
    have hQdiv : ∀ n, polynomialRootFactor (fun i : Fin m => z n i.succ) ∣ Q n := by
      intro n
      obtain ⟨u, hu⟩ := hdiv n
      refine ⟨u, ?_⟩
      dsimp [Q]
      rw [hu]
      simp only [polynomialRootFactor, Fin.prod_univ_succ, mul_assoc]
      exact Polynomial.mul_divByMonic_cancel_left _ (Polynomial.monic_X_sub_C _)
    have hrootn : ∀ n, (P n).eval (z n 0) = 0 := by
      intro n
      obtain ⟨u, hu⟩ := hdiv n
      rw [hu]
      simp [polynomialRootFactor, Fin.prod_univ_succ]
    have hroot : p.eval (a 0) = 0 := by
      apply tendsto_nhds_unique (polynomial_eval_tendsto_of_coeff_tendsto hdeg hcoeff (hz 0))
      simpa only [hrootn] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ))
        atTop (𝓝 0))
    have htail := ih hQdeg hQcoeff (fun n i => z n i.succ) (fun i => a i.succ)
      (fun i => hz i.succ) hQdiv
    obtain ⟨u, hu⟩ := htail
    refine ⟨u, ?_⟩
    calc
      p = (X - C (a 0)) * q :=
        (Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hroot).symm
      _ = (X - C (a 0)) * (polynomialRootFactor (fun i : Fin m => a i.succ) * u) := by
        rw [hu]
      _ = polynomialRootFactor a * u := by
        simp only [polynomialRootFactor, Fin.prod_univ_succ, mul_assoc]

/-- Having at least `m` selected roots in one closed disc is closed under bounded-degree
coefficient convergence. For a nonzero limit, the root-multiset lemma makes this precisely
the assertion with multiplicity used in the manuscript's compactness argument. -/
theorem polynomial_roots_in_closedDisc_of_coeff_tendsto {m d : ℕ}
    {P : ℕ → Polynomial ℂ} {p : Polynomial ℂ} {c : ℂ} {r : ℝ}
    (hdeg : ∀ n, (P n).natDegree ≤ d)
    (hcoeff : ∀ k, Tendsto (fun n => (P n).coeff k) atTop (𝓝 (p.coeff k)))
    (hroots : ∀ n, ∃ z : Fin m → ℂ,
      (∀ i, ‖z i - c‖ ≤ r) ∧ polynomialRootFactor z ∣ P n) :
    ∃ a : Fin m → ℂ, (∀ i, ‖a i - c‖ ≤ r) ∧ polynomialRootFactor a ∣ p := by
  classical
  choose z hmem hdiv using hroots
  have hcompact : IsCompact {v : Fin m → ℂ | ∀ i, v i ∈ Metric.closedBall c r} :=
    isCompact_pi_infinite fun _ => isCompact_closedBall c r
  have hzin : ∀ n, z n ∈ {v : Fin m → ℂ | ∀ i, v i ∈ Metric.closedBall c r} := by
    intro n i
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hmem n i
  obtain ⟨a, ha, φ, hφ, hlim⟩ := hcompact.tendsto_subseq hzin
  refine ⟨a, ?_, ?_⟩
  · intro i
    simpa only [Metric.mem_closedBall, dist_eq_norm] using ha i
  · apply polynomialRootFactor_dvd_of_coeff_tendsto
      (fun n => hdeg (φ n)) (fun k => (hcoeff k).comp hφ.tendsto_atTop)
      (fun n => z (φ n)) a
    · intro i
      exact (continuous_apply i).continuousAt.tendsto.comp hlim
    · exact fun n => hdiv (φ n)

/-- The closed-disc assertion expressed directly as inclusion of root multisets. The tuple
has exactly `m` entries, so repetitions count toward the required number of roots. -/
theorem polynomial_retains_roots_counted_with_multiplicity {m d : ℕ}
    {P : ℕ → Polynomial ℂ} {p : Polynomial ℂ} {c : ℂ} {r : ℝ}
    (hP : ∀ n, P n ≠ 0) (hp : p ≠ 0) (hdeg : ∀ n, (P n).natDegree ≤ d)
    (hcoeff : ∀ k, Tendsto (fun n => (P n).coeff k) atTop (𝓝 (p.coeff k)))
    (hroots : ∀ n, ∃ z : Fin m → ℂ,
      (∀ i, ‖z i - c‖ ≤ r) ∧ (List.ofFn z : Multiset ℂ) ≤ (P n).roots) :
    ∃ a : Fin m → ℂ, (∀ i, ‖a i - c‖ ≤ r) ∧
      (List.ofFn a : Multiset ℂ) ≤ p.roots ∧ (List.ofFn a : Multiset ℂ).card = m := by
  obtain ⟨a, ha, hdiv⟩ := polynomial_roots_in_closedDisc_of_coeff_tendsto hdeg hcoeff (by
    intro n
    obtain ⟨z, hz, hzroots⟩ := hroots n
    exact ⟨z, hz, (polynomialRootFactor_dvd_iff_le_roots z (hP n)).mpr hzroots⟩)
  exact ⟨a, ha, (polynomialRootFactor_dvd_iff_le_roots a hp).mp hdiv, by simp⟩

/-- If no root approaches `z`, each linear factor controls its value at any other point.
The constant depends only on the two points and the excluded root distance. -/
theorem polynomial_root_factor_comparison {a z β : ℂ} {ε : ℝ}
    (hε : 0 < ε) (haway : ε ≤ ‖z - β‖) :
    ‖a - β‖ ≤ (1 + ‖a - z‖ / ε) * ‖z - β‖ := by
  have htriangle : ‖a - β‖ ≤ ‖a - z‖ + ‖z - β‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le (a - z) (z - β)
  have hmul := mul_le_mul_of_nonneg_left haway
    (div_nonneg (norm_nonneg (a - z)) hε.le)
  rw [div_mul_cancel₀ _ hε.ne'] at hmul
  nlinarith

/-- A degree-bounded polynomial without a root near `z` has a uniform comparison between
its values at `a` and `z`. This estimate permits vanishing leading coefficients in a limit. -/
theorem polynomial_eval_comparison_of_roots_away (q : Polynomial ℂ) {d : ℕ}
    (hdeg : q.natDegree ≤ d) (a z : ℂ) {ε : ℝ} (hε : 0 < ε)
    (haway : ∀ β ∈ q.roots, ε ≤ ‖z - β‖) :
    ‖q.eval a‖ ≤ (1 + ‖a - z‖ / ε) ^ d * ‖q.eval z‖ := by
  let C : ℝ := 1 + ‖a - z‖ / ε
  have hC : 1 ≤ C := by
    dsimp [C]
    exact le_add_of_nonneg_right (div_nonneg (norm_nonneg _) hε.le)
  have hCnonneg : 0 ≤ C := zero_le_one.trans hC
  have hprod (s : Multiset ℂ) (hs : ∀ β ∈ s, ε ≤ ‖z - β‖) :
      ‖(s.map (fun β => a - β)).prod‖ ≤
        C ^ s.card * ‖(s.map (fun β => z - β)).prod‖ := by
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons β s ih =>
      have hfirst := polynomial_root_factor_comparison (a := a) hε (hs β (by simp))
      have hrest := ih (fun γ hγ => hs γ (by simp [hγ]))
      simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, norm_mul]
      calc
        ‖a - β‖ * ‖(s.map (fun γ => a - γ)).prod‖ ≤
            (C * ‖z - β‖) * (C ^ s.card * ‖(s.map (fun γ => z - γ)).prod‖) :=
          mul_le_mul hfirst hrest (norm_nonneg _) (mul_nonneg hCnonneg (norm_nonneg _))
        _ = C ^ (s.card + 1) * (‖z - β‖ * ‖(s.map (fun γ => z - γ)).prod‖) := by
          rw [pow_succ]
          ring
  have hcard : q.roots.card ≤ d :=
    (Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits q)).trans_le hdeg
  have hpow : C ^ q.roots.card ≤ C ^ d := pow_le_pow_right₀ hC hcard
  rw [(IsAlgClosed.splits q).eval_eq_prod_roots a,
    (IsAlgClosed.splits q).eval_eq_prod_roots z, norm_mul, norm_mul]
  calc
    ‖q.leadingCoeff‖ * ‖(q.roots.map (fun β => a - β)).prod‖ ≤
        ‖q.leadingCoeff‖ * (C ^ q.roots.card * ‖(q.roots.map (fun β => z - β)).prod‖) :=
      mul_le_mul_of_nonneg_left (hprod q.roots haway) (norm_nonneg _)
    _ = C ^ q.roots.card * (‖q.leadingCoeff‖ * ‖(q.roots.map (fun β => z - β)).prod‖) := by ring
    _ ≤ C ^ d * (‖q.leadingCoeff‖ * ‖(q.roots.map (fun β => z - β)).prod‖) :=
      mul_le_mul_of_nonneg_right hpow (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- Every finite root of a nonzero coefficientwise polynomial limit attracts roots of
all sufficiently late polynomials. The common degree bound allows degree loss, and the
neighbourhood radius is arbitrary and positive. -/
theorem polynomial_eventually_has_nearby_root_of_coeff_tendsto
    {P : ℕ → Polynomial ℂ} {p : Polynomial ℂ} {d : ℕ}
    (hdeg : ∀ n, (P n).natDegree ≤ d)
    (hcoeff : ∀ k, Tendsto (fun n => (P n).coeff k) atTop (𝓝 (p.coeff k)))
    (hp : p ≠ 0) {z : ℂ} (hz : p.eval z = 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∃ β : ℂ, (P n).eval β = 0 ∧ ‖z - β‖ < ε := by
  have hexists : ∃ a : ℂ, p.eval a ≠ 0 := by
    by_contra! h
    apply hp
    apply Polynomial.funext
    simpa using h
  obtain ⟨a, ha⟩ := hexists
  let C : ℝ := (1 + ‖a - z‖ / ε) ^ d
  have hsmall : Tendsto (fun n => C * ‖(P n).eval z‖) atTop (𝓝 0) := by
    simpa only [hz, norm_zero, mul_zero] using
      (polynomial_eval_tendsto_of_coeff_tendsto hdeg hcoeff
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => z) atTop (𝓝 z))).norm.const_mul C
  have hlarge : Tendsto (fun n => ‖(P n).eval a‖) atTop (𝓝 ‖p.eval a‖) :=
    (polynomial_eval_tendsto_of_coeff_tendsto hdeg hcoeff
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => a) atTop (𝓝 a))).norm
  filter_upwards [hsmall.eventually_lt hlarge (norm_pos_iff.mpr ha)] with n hn
  by_contra! hnone
  have haway : ∀ β ∈ (P n).roots, ε ≤ ‖z - β‖ := by
    intro β hβ
    exact hnone β (Polynomial.isRoot_of_mem_roots hβ)
  exact (not_lt_of_ge (polynomial_eval_comparison_of_roots_away (P n) (hdeg n) a z hε haway)) hn

/-- A sequence converging coefficientwise to a nonzero polynomial is eventually nonzero.
This observation needs no common degree bound. -/
theorem polynomial_eventually_ne_zero_of_coeff_tendsto
    {P : ℕ → Polynomial ℂ} {p : Polynomial ℂ}
    (hcoeff : ∀ k, Tendsto (fun n => (P n).coeff k) atTop (𝓝 (p.coeff k)))
    (hp : p ≠ 0) : ∀ᶠ n in atTop, P n ≠ 0 := by
  have hexists : ∃ k, p.coeff k ≠ 0 := by
    by_contra! h
    apply hp
    ext k
    simpa using h k
  obtain ⟨k, hk⟩ := hexists
  filter_upwards [(hcoeff k).eventually_ne hk] with n hn
  intro hzero
  exact hn (by simp [hzero])

/-- The nearby roots can also be identified as members of the actual root multisets of
the late polynomials, since a nonzero limit makes those polynomials eventually nonzero. -/
theorem polynomial_eventually_has_nearby_mem_roots_of_coeff_tendsto
    {P : ℕ → Polynomial ℂ} {p : Polynomial ℂ} {d : ℕ}
    (hdeg : ∀ n, (P n).natDegree ≤ d)
    (hcoeff : ∀ k, Tendsto (fun n => (P n).coeff k) atTop (𝓝 (p.coeff k)))
    (hp : p ≠ 0) {z : ℂ} (hz : p.eval z = 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∃ β ∈ (P n).roots, ‖z - β‖ < ε := by
  filter_upwards [polynomial_eventually_ne_zero_of_coeff_tendsto hcoeff hp,
    polynomial_eventually_has_nearby_root_of_coeff_tendsto hdeg hcoeff hp hz hε]
    with n hn hroot
  obtain ⟨β, hβ, hnear⟩ := hroot
  exact ⟨β, (Polynomial.mem_roots hn).mpr hβ, hnear⟩

end KungTraub
