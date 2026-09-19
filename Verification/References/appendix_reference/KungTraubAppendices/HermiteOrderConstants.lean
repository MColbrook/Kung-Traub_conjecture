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
  sorry

/-- The exact recurrence includes the constant for the initial point. -/
theorem hermiteOrderConstant_succ (D L : ℝ) (j : ℕ) :
    hermiteOrderConstant D L (j + 1) =
      D * L ^ (j + 2) * ∏ i : Fin (j + 1), hermiteOrderConstant D L i.val := by
  sorry

/-- Positive fixed bounds give positive constants at every stage. -/
theorem hermiteOrderConstant_pos {D L : ℝ} (hD : 0 < D) (hL : 0 < L) (j : ℕ) :
    0 < hermiteOrderConstant D L j := by
  sorry

/-- The geometric sum including its empty-range case. -/
theorem one_add_sum_range_pow_two (m : ℕ) :
    1 + ∑ i ∈ Finset.range m, 2 ^ i = 2 ^ m := by
  sorry

/-- The exponent identity in the same finite-index form as an observed history. -/
theorem one_add_sum_fin_pow_two (m : ℕ) :
    1 + ∑ i : Fin m, 2 ^ i.val = 2 ^ m := by
  sorry

/-- The extra initial-error factor gives exactly the next order, also at zero. -/
theorem mul_prod_pow_two (r : ℝ) (m : ℕ) :
    r * (∏ i : Fin m, r ^ (2 ^ i.val)) = r ^ (2 ^ m) := by
  sorry

/-- Pointwise finite error estimates imply the next uniform order bound.
The estimate includes the singleton stage and the zero starting error. -/
theorem hermiteOrderConstant_product_bound {D L r : ℝ}
    (hD : 0 ≤ D) (hL : 0 ≤ L) (hr : 0 ≤ r) (j : ℕ) (e : Fin (j + 1) → ℝ)
    (he : ∀ i, 0 ≤ e i)
    (hbound : ∀ i, e i ≤ hermiteOrderConstant D L i.val * r ^ (2 ^ i.val)) :
    D * L ^ (j + 2) * r * (∏ i, e i) ≤
      hermiteOrderConstant D L (j + 1) * r ^ (2 ^ (j + 1)) := by
  sorry

end KungTraubAppendices
