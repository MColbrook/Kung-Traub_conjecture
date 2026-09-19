import appendix_b_reference.KungTraubAppendices.ComplexParameterGeometry
import appendix_b_reference.KungTraubAppendices.ComplexRootDisc

/-!
# Root motion and attained discs for complex affine families

Appendix B uses bilinear complex parameter evaluations and the projection of the
conjugated evaluation vector. The projection and motion arguments follow
`KungTraub.ParameterGeometry` over the complex scalar field. The maximizing
direction and `complexPencil_parameter_at_target` realize each point of the
target disc by an admissible family parameter.

The family hypotheses specify root existence, a spatial lower bound and
containment in the spatial domain.
-/

noncomputable section

open Set
open scoped BigOperators InnerProductSpace

namespace KungTraubAppendices

variable {d : ℕ}
local notation "E" => EuclideanSpace ℂ (Fin d)

/-- The exact affine identity and spatial lower bound imply displacement
controlled by the old projected sensitivity in the actual complex direction. -/
theorem complexFamily_root_displacement
    (V : Submodule ℂ E) [V.HasOrthogonalProjection]
    {P : Set E} {J : Set ℂ} {F : E → ℂ → ℂ} {root : E → ℂ}
    {vector : ℂ → E} {m : ℝ} (hm : 0 < m)
    (hroot : ∀ u ∈ P, root u ∈ J ∧ F u (root u) = 0)
    (hlower : ∀ u ∈ P, ∀ z ∈ J, ∀ t ∈ J,
      m * ‖z - t‖ ≤ ‖F u z - F u t‖)
    (haffine : ∀ u ∈ P, ∀ v ∈ P, ∀ t ∈ J,
      F u t = F v t + complexBilinearDot (u - v) (vector t))
    {u v : E} (hu : u ∈ P) (hv : v ∈ P) (hdir : u - v ∈ V) :
    ‖root u - root v‖ ≤
      (‖V.starProjection (complexConjVector (vector (root v)))‖ / m) * ‖u - v‖ := by
  sorry

/-- Projection is nonexpansive after the required coordinatewise conjugation.
The factor follows from a half-radius root shift and r≤1. -/
theorem complex_projected_sensitivity_comparison
    (V : Submodule ℂ E) [V.HasOrthogonalProjection]
    {vector : ℂ → E} {α β : ℂ} {a K r m : ℝ}
    (hK : 0 ≤ K) (hr : r ≤ 1) (hm : 0 < m)
    (ha : a = ‖V.starProjection (complexConjVector (vector α))‖)
    (hshift : ‖β - α‖ ≤ a * r / (2 * m))
    (hvector : ‖vector β - vector α‖ ≤ K * ‖β - α‖) :
    ‖V.starProjection (complexConjVector (vector β))‖ ≤ (1 + K / (2 * m)) * a := by
  sorry

/-- Moving the center by at most half the parameter radius increases the
old projected sensitivity by at most the exact factor Q=1+K/(2m). -/
theorem complexFamily_projected_sensitivity_half_ball
    (V : Submodule ℂ E) [V.HasOrthogonalProjection]
    {P : Set E} {J : Set ℂ} {F : E → ℂ → ℂ} {root : E → ℂ}
    {vector : ℂ → E} {m K r : ℝ} (hm : 0 < m) (hK : 0 ≤ K) (hr : r ≤ 1)
    (hroot : ∀ u ∈ P, root u ∈ J ∧ F u (root u) = 0)
    (hlower : ∀ u ∈ P, ∀ z ∈ J, ∀ t ∈ J,
      m * ‖z - t‖ ≤ ‖F u z - F u t‖)
    (haffine : ∀ u ∈ P, ∀ v ∈ P, ∀ t ∈ J,
      F u t = F v t + complexBilinearDot (u - v) (vector t))
    (hvector : ∀ z ∈ J, ∀ t ∈ J, ‖vector z - vector t‖ ≤ K * ‖z - t‖)
    {u v : E} (hu : u ∈ P) (hv : v ∈ P)
    (hdir : u - v ∈ V) (hstep : ‖u - v‖ ≤ r / 2) :
    ‖V.starProjection (complexConjVector (vector (root u)))‖ ≤
      (1 + K / (2 * m)) * ‖V.starProjection (complexConjVector (vector (root v)))‖ := by
  sorry

/-- After the center moves into the old half-ball, every admissible parameter
in a smaller direction space has root motion controlled by Q times the old
sensitivity. A parameter-radius bound can then be substituted directly. -/
theorem complexFamily_root_motion_from_half_ball
    (V W : Submodule ℂ E) [V.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (hWV : W ≤ V)
    {P : Set E} {J : Set ℂ} {F : E → ℂ → ℂ} {root : E → ℂ}
    {vector : ℂ → E} {m K r : ℝ} (hm : 0 < m) (hK : 0 ≤ K) (hr : r ≤ 1)
    (hroot : ∀ u ∈ P, root u ∈ J ∧ F u (root u) = 0)
    (hlower : ∀ u ∈ P, ∀ z ∈ J, ∀ t ∈ J,
      m * ‖z - t‖ ≤ ‖F u z - F u t‖)
    (haffine : ∀ u ∈ P, ∀ v ∈ P, ∀ t ∈ J,
      F u t = F v t + complexBilinearDot (u - v) (vector t))
    (hvector : ∀ z ∈ J, ∀ t ∈ J, ‖vector z - vector t‖ ≤ K * ‖z - t‖)
    {u v w : E} (hu : u ∈ P) (hv : v ∈ P) (hw : w ∈ P)
    (hdir : u - v ∈ V) (hstep : ‖u - v‖ ≤ r / 2) (hnewdir : w - u ∈ W) :
    ‖root w - root u‖ ≤
      ((1 + K / (2 * m)) * ‖V.starProjection (complexConjVector (vector (root v)))‖ / m) *
        ‖w - u‖ := by
  sorry

/-- The actual family roots cover the full disc. The maximizing
complex direction and each realizing parameter are constructed, while the
full target-disc containment in the spatial domain remains explicit. -/
theorem complexFamily_attained_closedBall
    (V : Submodule ℂ E) [V.HasOrthogonalProjection]
    {P : Set E} {J : Set ℂ} {F : E → ℂ → ℂ} {root : E → ℂ}
    {vector : ℂ → E} {m M K r : ℝ}
    (hm : 0 < m) (hM : 0 < M) (hK : 0 ≤ K) (hr : 0 < r)
    (hKr : K * r ≤ 2 * M)
    (hroot : ∀ v ∈ P, root v ∈ J ∧ F v (root v) = 0)
    (hlower : ∀ v ∈ P, ∀ z ∈ J, ∀ t ∈ J,
      m * ‖z - t‖ ≤ ‖F v z - F v t‖)
    (haffine : ∀ v ∈ P, ∀ u ∈ P, ∀ t ∈ J,
      F v t = F u t + complexBilinearDot (v - u) (vector t))
    (hvector : ∀ z ∈ J, ∀ t ∈ J, ‖vector z - vector t‖ ≤ K * ‖z - t‖)
    {u : E} (hu : u ∈ P)
    (hparameter : ∀ h ∈ V, ‖h‖ ≤ r / 2 → u + h ∈ P)
    (hupper : ∀ t ∈ J, ‖F u t - F u (root u)‖ ≤ M * ‖t - root u‖)
    (ha : 0 < ‖V.starProjection (complexConjVector (vector (root u)))‖)
    (hcontain : Metric.closedBall (root u)
      (r * ‖V.starProjection (complexConjVector (vector (root u)))‖ / (4 * M)) ⊆ J) :
    Metric.closedBall (root u)
      (r * ‖V.starProjection (complexConjVector (vector (root u)))‖ / (4 * M)) ⊆
        root '' {v | v ∈ P ∧ v - u ∈ V ∧ ‖v - u‖ ≤ r / 2} := by
  sorry

end KungTraubAppendices
