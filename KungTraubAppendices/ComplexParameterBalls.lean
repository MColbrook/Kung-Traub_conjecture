import KungTraubAppendices.ComplexAffineOracle

/-!
# Closed complex parameter balls in adaptive affine fibres

The geometric arguments of `KungTraub.ParameterBalls` apply to complex normed
spaces and hence to the Euclidean parameter spaces of the finite adversary.
Prefix-fibre identities preserve the selected rows when the center changes.
-/

noncomputable section

namespace KungTraubAppendices

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The closed ball in the complex affine space through its center. -/
def complexParameterBall (center : E) (V : Submodule ℂ E) (r : ℝ) : Set E :=
  {u | u - center ∈ V ∧ ‖u - center‖ ≤ r}

/-- The center belongs to every such ball with nonnegative radius. -/
theorem complexParameterBall_center (center : E) (V : Submodule ℂ E) {r : ℝ}
    (hr : 0 ≤ r) : center ∈ complexParameterBall center V r := by
  simp [complexParameterBall, hr]

/-- A direction with the stated norm budget gives a member of the ball. -/
theorem complexParameterBall_add_mem {center h : E} {V : Submodule ℂ E} {r : ℝ}
    (hh : h ∈ V) (hnorm : ‖h‖ ≤ r) : center + h ∈ complexParameterBall center V r := by
  simpa only [complexParameterBall, Set.mem_ofPred_eq, add_sub_cancel_left] using
    And.intro hh hnorm

/-- A complex unit direction carries the full closed scalar parameter disc
into the corresponding affine ball. -/
theorem complexParameterBall_unit_disc {center e : E} {V : Submodule ℂ E}
    {r : ℝ} {ξ : ℂ} (he : e ∈ V) (hnorm : ‖e‖ = 1) (hξ : ‖ξ‖ ≤ r) :
    center + ξ • e ∈ complexParameterBall center V r := by
  apply complexParameterBall_add_mem (V.smul_mem ξ he)
  simpa only [norm_smul, hnorm, mul_one] using hξ

/-- Increasing the radius preserves all members without changing directions. -/
theorem complexParameterBall_mono_radius {center : E} {V : Submodule ℂ E} {r s : ℝ}
    (hrs : r ≤ s) : complexParameterBall center V r ⊆ complexParameterBall center V s :=
  fun _ hu => ⟨hu.1, hu.2.trans hrs⟩

/-- Every member satisfies the ambient norm budget from the center and radius. -/
theorem complexParameterBall_norm_le {center u : E} {V : Submodule ℂ E} {r : ℝ}
    (hu : u ∈ complexParameterBall center V r) : ‖u‖ ≤ ‖center‖ + r := by
  calc
    ‖u‖ = ‖(u - center) + center‖ := by rw [sub_add_cancel]
    _ ≤ ‖u - center‖ + ‖center‖ := norm_add_le _ _
    _ ≤ r + ‖center‖ := add_le_add hu.2 le_rfl
    _ = _ := add_comm _ _

/-- A center-radius budget places the complete affine ball in the ambient
closed ball; in particular it can ensure admissible unit-ball parameters. -/
theorem complexParameterBall_subset_closedBall {center : E} {V : Submodule ℂ E}
    {r R : ℝ} (hbudget : ‖center‖ + r ≤ R) :
    complexParameterBall center V r ⊆ Metric.closedBall (0 : E) R := by
  intro u hu
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    (complexParameterBall_norm_le hu).trans hbudget

/-- Moving the center within the old direction space and reducing directions
preserves containment whenever the two radius budgets sum to the old radius. -/
theorem complexParameterBall_nested {center next : E} {V W : Submodule ℂ E}
    {r s δ : ℝ} (hcenter : next ∈ complexParameterBall center V δ)
    (hWV : W ≤ V) (hs : δ + s ≤ r) :
    complexParameterBall next W s ⊆ complexParameterBall center V r := by
  intro u hu
  have hsum : u - center = (u - next) + (next - center) := by abel
  constructor
  · rw [hsum]
    exact V.add_mem (hWV hu.1) hcenter.1
  · calc
      ‖u - center‖ = ‖(u - next) + (next - center)‖ := congrArg norm hsum
      _ ≤ ‖u - next‖ + ‖next - center‖ := norm_add_le _ _
      _ ≤ s + δ := add_le_add hu.2 hcenter.2
      _ ≤ r := by linarith

/-- Half the old radius allows both the center movement and the new ball. -/
theorem complexParameterBall_nested_half {center next : E} {V W : Submodule ℂ E}
    {r s : ℝ} (hcenter : next ∈ complexParameterBall center V (r / 2))
    (hWV : W ≤ V) (hs : s ≤ r / 2) :
    complexParameterBall next W s ⊆ complexParameterBall center V r :=
  complexParameterBall_nested hcenter hWV (by linarith)

/-- Every member of the actual direction ball gives the same exact prefix. -/
theorem ComplexAffineAlgorithm.prefix_eq_on_parameterBall {n : ℕ}
    (A : ComplexAffineAlgorithm E n) {center u : E} {x : ℂ} {r : ℝ} {j : ℕ}
    (hj : j ≤ n) (hu : u ∈ complexParameterBall center (A.direction center x j) r) :
    A.prefix u x j hj = A.prefix center x j hj :=
  (A.prefix_eq_iff_sub_mem_direction center u x j hj).mpr hu.1

/-- On the final direction ball the actual output is exactly constant. -/
theorem ComplexAffineAlgorithm.run_eq_on_parameterBall {n : ℕ}
    (A : ComplexAffineAlgorithm E n) {center u : E} {x : ℂ} {r : ℝ}
    (hu : u ∈ complexParameterBall center (A.direction center x n) r) :
    A.run u x = A.run center x :=
  congrArg (A.output x) (A.prefix_eq_on_parameterBall le_rfl hu)

/-- The actual next observation, including its optional location, is constant
on the old direction ball. -/
theorem ComplexAffineAlgorithm.query_eq_on_parameterBall {n : ℕ}
    (A : ComplexAffineAlgorithm E n) {center u : E} {x : ℂ} {r : ℝ} (j : Fin n)
    (hu : u ∈ complexParameterBall center (A.direction center x j.val) r) :
    A.actualObservation u x j = A.actualObservation center x j :=
  A.actualObservation_eq_of_prefix_eq j
    (A.prefix_eq_on_parameterBall (Nat.le_of_lt j.isLt) hu)

/-- The common kernel selected by the actual prefix is unchanged on the ball. -/
theorem ComplexAffineAlgorithm.direction_eq_on_parameterBall {n : ℕ}
    (A : ComplexAffineAlgorithm E n) {center u : E} {x : ℂ} {r : ℝ} {j : ℕ}
    (hj : j ≤ n) (hu : u ∈ complexParameterBall center (A.direction center x j) r) :
    A.direction u x j = A.direction center x j :=
  A.direction_eq_of_prefix_eq hj (A.prefix_eq_on_parameterBall hj hu)

/-- The successor ball lies in the old one, using the actual next row at the
moved center. Equality of the old prefixes identifies the selected kernel. -/
theorem ComplexAffineAlgorithm.parameterBall_next_subset {n : ℕ}
    (A : ComplexAffineAlgorithm E n) {center next : E} {x : ℂ} {r s : ℝ} {j : ℕ}
    (hj : j < n)
    (hnext : next ∈ complexParameterBall center (A.direction center x j) (r / 2))
    (hs : s ≤ r / 2) :
    complexParameterBall next (A.direction next x (j + 1)) s ⊆
      complexParameterBall center (A.direction center x j) r := by
  have hp := A.prefix_eq_on_parameterBall (Nat.le_of_lt hj) hnext
  apply complexParameterBall_nested_half hnext _ hs
  rw [A.direction_succ_of_prefix_eq hj hp]
  exact inf_le_left

end KungTraubAppendices
