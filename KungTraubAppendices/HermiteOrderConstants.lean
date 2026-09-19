import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Uniform constants for the inverse Hermite error estimate

These constants depend only on the fixed derivative bound `D`, linear bound `L`,
and stage. They propagate an upper error estimate and are independent of the
starting point. They are distinct from the leading coefficients for the sharpness
example. The exponent identity reuses Mathlib's `geom_sum_mul_add`; the finite
product estimate reuses `Finset.prod_le_prod` and `Finset.prod_pow_eq_pow_sum`.
-/

noncomputable section

open scoped BigOperators

namespace KungTraubAppendices

/-- Uniform upper-bound constants for errors of orders `2^j`. -/
def hermiteOrderConstant (D L : ℝ) : ℕ → ℝ
  | 0 => 1
  | j + 1 => D * L ^ (j + 2) * ∏ i : Fin (j + 1), hermiteOrderConstant D L i.val
termination_by j => j
decreasing_by omega

/-- The initial error has constant one. -/
@[simp] theorem hermiteOrderConstant_zero (D L : ℝ) :
    hermiteOrderConstant D L 0 = 1 := by
  rw [hermiteOrderConstant]

/-- The exact recurrence includes the constant for the initial point. -/
theorem hermiteOrderConstant_succ (D L : ℝ) (j : ℕ) :
    hermiteOrderConstant D L (j + 1) =
      D * L ^ (j + 2) * ∏ i : Fin (j + 1), hermiteOrderConstant D L i.val := by
  rw [hermiteOrderConstant]

/-- Positive fixed bounds give positive constants at every stage. -/
theorem hermiteOrderConstant_pos {D L : ℝ} (hD : 0 < D) (hL : 0 < L) (j : ℕ) :
    0 < hermiteOrderConstant D L j := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    cases j with
    | zero => simp
    | succ j =>
      rw [hermiteOrderConstant_succ]
      exact mul_pos (mul_pos hD (pow_pos hL _))
        (Finset.prod_pos (fun i _ => ih i.val i.isLt))

/-- The geometric sum including its empty-range case. -/
theorem one_add_sum_range_pow_two (m : ℕ) :
    1 + ∑ i ∈ Finset.range m, 2 ^ i = 2 ^ m := by
  simpa [Nat.add_comm] using geom_sum_mul_add (1 : ℕ) m

/-- The exponent identity in the same finite-index form as an observed history. -/
theorem one_add_sum_fin_pow_two (m : ℕ) :
    1 + ∑ i : Fin m, 2 ^ i.val = 2 ^ m := by
  rw [Fin.sum_univ_eq_sum_range]
  exact one_add_sum_range_pow_two m

/-- The extra initial-error factor gives exactly the next order, also at zero. -/
theorem mul_prod_pow_two (r : ℝ) (m : ℕ) :
    r * (∏ i : Fin m, r ^ (2 ^ i.val)) = r ^ (2 ^ m) := by
  rw [Finset.prod_pow_eq_pow_sum]
  calc
    r * r ^ (∑ i : Fin m, 2 ^ i.val) =
        r ^ (1 + ∑ i : Fin m, 2 ^ i.val) := by rw [pow_add, pow_one]
    _ = r ^ (2 ^ m) := by rw [one_add_sum_fin_pow_two]

/-- Pointwise finite error estimates imply the next uniform order bound.
The estimate includes the singleton stage and the zero starting error. -/
theorem hermiteOrderConstant_product_bound {D L r : ℝ}
    (hD : 0 ≤ D) (hL : 0 ≤ L) (hr : 0 ≤ r) (j : ℕ) (e : Fin (j + 1) → ℝ)
    (he : ∀ i, 0 ≤ e i)
    (hbound : ∀ i, e i ≤ hermiteOrderConstant D L i.val * r ^ (2 ^ i.val)) :
    D * L ^ (j + 2) * r * (∏ i, e i) ≤
      hermiteOrderConstant D L (j + 1) * r ^ (2 ^ (j + 1)) := by
  have hprod : (∏ i, e i) ≤
      ∏ i : Fin (j + 1), hermiteOrderConstant D L i.val * r ^ (2 ^ i.val) :=
    Finset.prod_le_prod (fun i _ => he i) (fun i _ => hbound i)
  calc
    _ ≤ D * L ^ (j + 2) * r *
        (∏ i : Fin (j + 1), hermiteOrderConstant D L i.val * r ^ (2 ^ i.val)) :=
      mul_le_mul_of_nonneg_left hprod (mul_nonneg (mul_nonneg hD (pow_nonneg hL _)) hr)
    _ = (D * L ^ (j + 2) * ∏ i : Fin (j + 1), hermiteOrderConstant D L i.val) *
        (r * ∏ i : Fin (j + 1), r ^ (2 ^ i.val)) := by
      rw [Finset.prod_mul_distrib]
      ring
    _ = _ := by rw [hermiteOrderConstant_succ, mul_prod_pow_two]

end KungTraubAppendices
