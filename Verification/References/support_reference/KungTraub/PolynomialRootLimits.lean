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
  sorry

/-- Evaluation at convergent points respects bounded-degree coefficient convergence. -/
theorem polynomial_eval_tendsto_of_coeff_tendsto {P : ℕ → Polynomial ℂ}
    {p : Polynomial ℂ} {d : ℕ} (hdeg : ∀ n, (P n).natDegree ≤ d)
    (hcoeff : ∀ k, Tendsto (fun n => (P n).coeff k) atTop (𝓝 (p.coeff k)))
    {z : ℕ → ℂ} {a : ℂ} (hz : Tendsto z atTop (𝓝 a)) :
    Tendsto (fun n => (P n).eval (z n)) atTop (𝓝 (p.eval a)) := by
  sorry

/-- Synthetic division has a finite coefficient formula with a common degree bound. -/
theorem polynomial_coeff_divByMonic_X_sub_C_of_degree_le (p : Polynomial ℂ)
    {d : ℕ} (hdeg : p.natDegree ≤ d) (a : ℂ) (k : ℕ) :
    (p /ₘ (X - C a)).coeff k =
      ∑ i ∈ Finset.Icc (k + 1) d, a ^ (i - (k + 1)) * p.coeff i := by
  sorry

/-- Coefficients of the synthetic quotient converge when the input coefficients and the
selected divisor root converge. No nonvanishing leading coefficient is needed. -/
theorem polynomial_divByMonic_X_sub_C_coeff_tendsto {P : ℕ → Polynomial ℂ}
    {p : Polynomial ℂ} {d : ℕ} (hdeg : ∀ n, (P n).natDegree ≤ d)
    (hcoeff : ∀ k, Tendsto (fun n => (P n).coeff k) atTop (𝓝 (p.coeff k)))
    {z : ℕ → ℂ} {a : ℂ} (hz : Tendsto z atTop (𝓝 a)) (k : ℕ) :
    Tendsto (fun n => (P n /ₘ (X - C (z n))).coeff k) atTop
      (𝓝 ((p /ₘ (X - C a)).coeff k)) := by
  sorry

/-- The monic factor containing a prescribed tuple of roots, including repeated roots. -/
def polynomialRootFactor {m : ℕ} (z : Fin m → ℂ) : Polynomial ℂ :=
  ∏ i, (X - C (z i))

/-- A tuple factor divides a nonzero polynomial exactly when its root multiset is a
submultiset of the polynomial's roots. Thus the representation retains multiplicity. -/
theorem polynomialRootFactor_dvd_iff_le_roots {m : ℕ} (z : Fin m → ℂ)
    {p : Polynomial ℂ} (hp : p ≠ 0) :
    polynomialRootFactor z ∣ p ↔ (List.ofFn z : Multiset ℂ) ≤ p.roots := by
  sorry

/-- Limits of selected root factors still divide the coefficientwise polynomial limit.
This includes coalescing roots and retains every repeated linear factor. -/
theorem polynomialRootFactor_dvd_of_coeff_tendsto {m d : ℕ}
    {P : ℕ → Polynomial ℂ} {p : Polynomial ℂ}
    (hdeg : ∀ n, (P n).natDegree ≤ d)
    (hcoeff : ∀ k, Tendsto (fun n => (P n).coeff k) atTop (𝓝 (p.coeff k)))
    (z : ℕ → Fin m → ℂ) (a : Fin m → ℂ)
    (hz : ∀ i, Tendsto (fun n => z n i) atTop (𝓝 (a i)))
    (hdiv : ∀ n, polynomialRootFactor (z n) ∣ P n) : polynomialRootFactor a ∣ p := by
  sorry

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
  sorry

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
  sorry

/-- If no root approaches `z`, each linear factor controls its value at any other point.
The constant depends only on the two points and the excluded root distance. -/
theorem polynomial_root_factor_comparison {a z β : ℂ} {ε : ℝ}
    (hε : 0 < ε) (haway : ε ≤ ‖z - β‖) :
    ‖a - β‖ ≤ (1 + ‖a - z‖ / ε) * ‖z - β‖ := by
  sorry

/-- A degree-bounded polynomial without a root near `z` has a uniform comparison between
its values at `a` and `z`. This estimate permits vanishing leading coefficients in a limit. -/
theorem polynomial_eval_comparison_of_roots_away (q : Polynomial ℂ) {d : ℕ}
    (hdeg : q.natDegree ≤ d) (a z : ℂ) {ε : ℝ} (hε : 0 < ε)
    (haway : ∀ β ∈ q.roots, ε ≤ ‖z - β‖) :
    ‖q.eval a‖ ≤ (1 + ‖a - z‖ / ε) ^ d * ‖q.eval z‖ := by
  sorry

/-- Every finite root of a nonzero coefficientwise polynomial limit attracts roots of
all sufficiently late polynomials. The common degree bound allows degree loss, and the
neighbourhood radius is arbitrary and positive. -/
theorem polynomial_eventually_has_nearby_root_of_coeff_tendsto
    {P : ℕ → Polynomial ℂ} {p : Polynomial ℂ} {d : ℕ}
    (hdeg : ∀ n, (P n).natDegree ≤ d)
    (hcoeff : ∀ k, Tendsto (fun n => (P n).coeff k) atTop (𝓝 (p.coeff k)))
    (hp : p ≠ 0) {z : ℂ} (hz : p.eval z = 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∃ β : ℂ, (P n).eval β = 0 ∧ ‖z - β‖ < ε := by
  sorry

/-- A sequence converging coefficientwise to a nonzero polynomial is eventually nonzero.
This observation needs no common degree bound. -/
theorem polynomial_eventually_ne_zero_of_coeff_tendsto
    {P : ℕ → Polynomial ℂ} {p : Polynomial ℂ}
    (hcoeff : ∀ k, Tendsto (fun n => (P n).coeff k) atTop (𝓝 (p.coeff k)))
    (hp : p ≠ 0) : ∀ᶠ n in atTop, P n ≠ 0 := by
  sorry

/-- The nearby roots can also be identified as members of the actual root multisets of
the late polynomials, since a nonzero limit makes those polynomials eventually nonzero. -/
theorem polynomial_eventually_has_nearby_mem_roots_of_coeff_tendsto
    {P : ℕ → Polynomial ℂ} {p : Polynomial ℂ} {d : ℕ}
    (hdeg : ∀ n, (P n).natDegree ≤ d)
    (hcoeff : ∀ k, Tendsto (fun n => (P n).coeff k) atTop (𝓝 (p.coeff k)))
    (hp : p ≠ 0) {z : ℂ} (hz : p.eval z = 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∃ β ∈ (P n).roots, ‖z - β‖ < ε := by
  sorry

end KungTraub
