import KungTraub.AffineTranscripts
import KungTraub.ParameterGeometry

/-!
# Nested balls in adaptive transcript fibres

The finite-stage argument moves the centre within half of the current ball and
then intersects the direction space with the kernel of the next observation.
These lemmas preserve both the full radius bound and the actual adaptive prefix.
No regularity of the algorithm's decision rules is required.
-/

noncomputable section

namespace KungTraub

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def parameterBall (center : E) (V : Submodule ℝ E) (r : ℝ) : Set E :=
  {u | u - center ∈ V ∧ ‖u - center‖ ≤ r}

theorem parameterBall_center (center : E) (V : Submodule ℝ E) {r : ℝ}
    (hr : 0 ≤ r) : center ∈ parameterBall center V r := by
  simp [parameterBall, hr]

theorem parameterBall_add_mem {center h : E} {V : Submodule ℝ E} {r : ℝ}
    (hh : h ∈ V) (hnorm : ‖h‖ ≤ r) : center + h ∈ parameterBall center V r := by
  simpa only [parameterBall, Set.mem_ofPred_eq, add_sub_cancel_left] using And.intro hh hnorm

theorem parameterBall_unit_segment {center e : E} {V : Submodule ℝ E} {r t : ℝ}
    (he : e ∈ V) (hnorm : ‖e‖ = 1) (ht : |t| ≤ r) :
    center + t • e ∈ parameterBall center V r := by
  apply parameterBall_add_mem (V.smul_mem t he)
  simpa only [norm_smul, Real.norm_eq_abs, hnorm, mul_one] using ht

theorem parameterBall_mono_radius {center : E} {V : Submodule ℝ E} {r s : ℝ}
    (hrs : r ≤ s) : parameterBall center V r ⊆ parameterBall center V s :=
  fun _ hu => ⟨hu.1, hu.2.trans hrs⟩

theorem parameterBall_nested {center next : E} {V W : Submodule ℝ E} {r s d : ℝ}
    (hcenter : next ∈ parameterBall center V d) (hWV : W ≤ V) (hs : d + s ≤ r) :
    parameterBall next W s ⊆ parameterBall center V r := by
  intro u hu
  have hsum : u - center = (u - next) + (next - center) := by abel
  constructor
  · rw [hsum]
    exact V.add_mem (hWV hu.1) hcenter.1
  · calc
      ‖u - center‖ = ‖(u - next) + (next - center)‖ := congrArg norm hsum
      _ ≤ ‖u - next‖ + ‖next - center‖ := norm_add_le _ _
      _ ≤ s + d := add_le_add hu.2 hcenter.2
      _ ≤ r := by linarith

theorem parameterBall_nested_half {center next : E} {V W : Submodule ℝ E} {r s : ℝ}
    (hcenter : next ∈ parameterBall center V (r / 2)) (hWV : W ≤ V) (hs : s ≤ r / 2) :
    parameterBall next W s ⊆ parameterBall center V r :=
  parameterBall_nested hcenter hWV (by linarith)

theorem AffineAlgorithm.prefix_eq_on_parameterBall {n : ℕ} (A : AffineAlgorithm E n)
    {center u : E} {x r : ℝ} {j : ℕ} (hj : j ≤ n)
    (hu : u ∈ parameterBall center (A.direction center x j) r) :
    A.prefix u x j hj = A.prefix center x j hj :=
  (A.prefix_eq_iff_sub_mem_direction center u x j hj).mpr hu.1

theorem AffineAlgorithm.run_eq_on_parameterBall {n : ℕ} (A : AffineAlgorithm E n)
    {center u : E} {x r : ℝ}
    (hu : u ∈ parameterBall center (A.direction center x n) r) :
    A.run u x = A.run center x :=
  congrArg (A.output x) (A.prefix_eq_on_parameterBall le_rfl hu)

theorem AffineAlgorithm.parameterBall_next_subset {n : ℕ} (A : AffineAlgorithm E n)
    {center next : E} {x r s : ℝ} {j : ℕ} (hj : j < n)
    (hnext : next ∈ parameterBall center (A.direction center x j) (r / 2))
    (hs : s ≤ r / 2) :
    parameterBall next (A.direction next x (j + 1)) s ⊆
      parameterBall center (A.direction center x j) r := by
  have hp := A.prefix_eq_on_parameterBall (Nat.le_of_lt hj) hnext
  apply parameterBall_nested_half hnext _ hs
  rw [A.direction_succ_of_prefix_eq hj hp]
  exact inf_le_left

theorem AffineAlgorithm.query_eq_on_parameterBall {n : ℕ} (A : AffineAlgorithm E n)
    {center u : E} {x r : ℝ} (j : Fin n)
    (hu : u ∈ parameterBall center (A.direction center x j.val) r) :
    A.actualObservation u x j = A.actualObservation center x j :=
  A.actualObservation_eq_of_prefix_eq j
    (A.prefix_eq_on_parameterBall (Nat.le_of_lt j.isLt) hu)

end KungTraub

