import KungTraubAppendices.ComplexParameterGeometry
import KungTraubAppendices.ComplexRootDisc

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
  have hl := hlower u hu (root u) (hroot u hu).1 (root v) (hroot v hv).1
  simp only [(hroot u hu).2, zero_sub, norm_neg] at hl
  have hvalue : F u (root v) = complexBilinearDot (u - v) (vector (root v)) := by
    simpa only [(hroot v hv).2, zero_add] using
      haffine u hu v hv (root v) (hroot v hv).1
  exact complex_root_displacement_le_projected V hdir hm hl hvalue

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
  have ha0 : 0 ≤ a := ha.symm ▸ norm_nonneg _
  have hproj : ‖V.starProjection (complexConjVector (vector β)) -
      V.starProjection (complexConjVector (vector α))‖ ≤ ‖vector β - vector α‖ := by
    simpa only [map_sub, norm_complexConjVector_sub] using
      V.norm_starProjection_apply_le
        (complexConjVector (vector β) - complexConjVector (vector α))
  have htriangle := norm_add_le
    (V.starProjection (complexConjVector (vector β)) -
      V.starProjection (complexConjVector (vector α)))
    (V.starProjection (complexConjVector (vector α)))
  rw [sub_add_cancel, ← ha] at htriangle
  have hscale : a * r / (2 * m) ≤ a / (2 * m) :=
    div_le_div_of_nonneg_right (mul_le_of_le_one_right ha0 hr) (by positivity)
  have hmotion := mul_le_mul_of_nonneg_left (hshift.trans hscale) hK
  calc
    ‖V.starProjection (complexConjVector (vector β))‖ ≤ ‖vector β - vector α‖ + a := by
      linarith
    _ ≤ K * (a / (2 * m)) + a := by linarith
    _ = (1 + K / (2 * m)) * a := by ring

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
  have hmove := complexFamily_root_displacement V hm hroot hlower haffine hu hv hdir
  have hshift : ‖root u - root v‖ ≤
      ‖V.starProjection (complexConjVector (vector (root v)))‖ * r / (2 * m) := by
    calc
      _ ≤ (‖V.starProjection (complexConjVector (vector (root v)))‖ / m) * ‖u - v‖ := hmove
      _ ≤ (‖V.starProjection (complexConjVector (vector (root v)))‖ / m) * (r / 2) :=
        mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = _ := by ring
  exact complex_projected_sensitivity_comparison V hK hr hm rfl hshift
    (hvector (root u) (hroot u hu).1 (root v) (hroot v hv).1)

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
  have hmove := complexFamily_root_displacement W hm hroot hlower haffine hw hu hnewdir
  have hnext := complexFamily_projected_sensitivity_half_ball V hm hK hr
    hroot hlower haffine hvector hu hv hdir hstep
  have hproj := complex_projected_norm_mono_subspace hWV (vector (root u))
  exact hmove.trans (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (hproj.trans hnext) hm.le) (norm_nonneg _))

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
  obtain ⟨e, heV, henorm, hevalue⟩ :=
    exists_complex_unit_direction_attaining_projected_norm V (vector (root u)) ha
  let q : ℂ → ℂ := fun t => complexBilinearDot e (vector t)
  have hqa : ‖q (root u)‖ =
      ‖V.starProjection (complexConjVector (vector (root u)))‖ := by
    simp only [q, hevalue, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  have hq : ∀ t ∈ J, ‖q t - q (root u)‖ ≤ K * ‖t - root u‖ := by
    intro t ht
    have heq : q t - q (root u) = complexBilinearDot e (vector t - vector (root u)) := by
      simp [q, complexBilinearDot, mul_sub, Finset.sum_sub_distrib]
    rw [heq]
    have h := norm_complexBilinearDot_le e (vector t - vector (root u))
    rw [henorm, mul_one] at h
    exact h.trans (hvector t ht (root u) (hroot u hu).1)
  intro t ht
  have htJ := hcontain ht
  have hFt : ‖F u t‖ ≤ M * ‖t - root u‖ := by
    simpa only [(hroot u hu).2, sub_zero] using hupper t htJ
  obtain ⟨_, hξ, hzero⟩ :=
    complexPencil_parameter_at_target ha hM hK hr hKr hqa ht hFt (hq t htJ)
  let ξ : ℂ := -F u t / q t
  have hparam : u + ξ • e ∈ P := hparameter (ξ • e) (V.smul_mem ξ heV)
    (by simpa only [norm_smul, henorm, mul_one] using hξ)
  have hnewzero : F (u + ξ • e) t = 0 := by
    rw [haffine (u + ξ • e) hparam u hu t htJ]
    have hdot : complexBilinearDot ((u + ξ • e) - u) (vector t) = ξ * q t := by
      simp [q, complexBilinearDot, Finset.mul_sum, mul_assoc]
    rw [hdot]
    exact hzero
  have hdist := hlower (u + ξ • e) hparam t htJ
    (root (u + ξ • e)) (hroot (u + ξ • e) hparam).1
  rw [hnewzero, (hroot (u + ξ • e) hparam).2, sub_self, norm_zero] at hdist
  have hnorm : ‖t - root (u + ξ • e)‖ = 0 := by nlinarith [norm_nonneg (t - root (u + ξ • e))]
  have hequal : t = root (u + ξ • e) := sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  refine ⟨u + ξ • e, ⟨hparam, ?_, ?_⟩, hequal.symm⟩
  · simpa only [add_sub_cancel_left] using V.smul_mem ξ heV
  · simpa only [add_sub_cancel_left, norm_smul, henorm, mul_one] using hξ

end KungTraubAppendices
