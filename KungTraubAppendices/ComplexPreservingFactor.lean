import KungTraubAppendices.ComplexQueryHistories
import Mathlib.Algebra.Polynomial.Monic

/-!
# The polynomial factor preserving the saved complex observations

The product is taken over the actual query-node set, with exponent one more
than the greatest saved derivative order. It adapts the algebraic product
facts of `KungTraub.EntireStages` directly over ℂ. Nonzero evaluation at a
selected root assumes only that the saved nodes differ from that root; no
condition excludes other zeros of the input outside the unit disc.
-/

noncomputable section

open Polynomial
open scoped BigOperators

namespace KungTraubAppendices

/-- The actual finite-query product prescribing every old complex derivative jet. -/
def complexPreservingFactor (Q : Finset ComplexQuery) : Polynomial ℂ :=
  ∏ z ∈ complexQueryNodes Q, (X - C z) ^ (complexMaxQueryOrder Q z + 1)

theorem complexPreservingFactor_empty : complexPreservingFactor ∅ = 1 := by
  classical
  simp [complexPreservingFactor, complexQueryNodes]

/-- The product is monic, including the empty history. -/
theorem complexPreservingFactor_monic (Q : Finset ComplexQuery) :
    (complexPreservingFactor Q).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun z _ => (Polynomial.monic_X_sub_C z).pow _

theorem complexPreservingFactor_ne_zero (Q : Finset ComplexQuery) :
    complexPreservingFactor Q ≠ 0 := (complexPreservingFactor_monic Q).ne_zero

/-- Each saved node occurs with its complete greatest-order multiplicity. -/
theorem complexPreservingFactor_factor_dvd {Q : Finset ComplexQuery} {z : ℂ}
    (hz : z ∈ complexQueryNodes Q) :
    (X - C z) ^ (complexMaxQueryOrder Q z + 1) ∣ complexPreservingFactor Q :=
  Finset.dvd_prod_of_mem _ hz

/-- Each actual saved derivative order has the required power factor. -/
theorem complexPreservingFactor_query_dvd {Q : Finset ComplexQuery} {z : ℂ} {k : ℕ}
    (hq : ComplexQuery.derivative z k ∈ Q) :
    (X - C z) ^ (k + 1) ∣ complexPreservingFactor Q := by
  have hz := (mem_complexQueryNodes_iff Q z).mpr ⟨k, hq⟩
  exact (pow_dvd_pow _ (Nat.add_le_add_right (complex_query_order_le_maxQueryOrder hq) 1)).trans
    (complexPreservingFactor_factor_dvd hz)

/-- The selected root need only differ from the saved nodes; values of an input
at unrelated or exterior nodes are not constrained. -/
theorem complexPreservingFactor_eval_ne_zero {Q : Finset ComplexQuery} {α : ℂ}
    (havoid : ∀ z ∈ complexQueryNodes Q, z ≠ α) :
    (complexPreservingFactor Q).eval α ≠ 0 := by
  classical
  simp only [complexPreservingFactor, Polynomial.eval_prod, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  apply Finset.prod_ne_zero_iff.mpr
  intro z hz
  exact pow_ne_zero _ (sub_ne_zero.mpr (havoid z hz).symm)

/-- The positive real multiplier leaves the old-root weight nonzero. -/
theorem complexPreservingFactor_scaled_eval_ne_zero {Q : Finset ComplexQuery} {α : ℂ}
    {lam : ℝ} (hlam : 0 < lam) (havoid : ∀ z ∈ complexQueryNodes Q, z ≠ α) :
    (lam : ℂ) * (complexPreservingFactor Q).eval α ≠ 0 := by
  have hlamc : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
  exact mul_ne_zero hlamc (complexPreservingFactor_eval_ne_zero havoid)

end KungTraubAppendices
