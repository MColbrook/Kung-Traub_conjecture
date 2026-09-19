import KungTraub.PolynomialInformation
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Real and complex ranks of real observation matrices

Real and imaginary parts identify the complex kernel, regarded as a real vector space,
with two copies of the real kernel. Rank equality then follows from rank-nullity and
the scalar-tower dimension formula in mathlib.
-/

noncomputable section
namespace KungTraub
open scoped BigOperators

theorem complexified_matrix_mulVec_re {j D : ℕ} (A : Matrix (Fin j) (Fin D) ℝ)
    (z : Fin D → ℂ) (i : Fin j) :
    (Matrix.mulVec (A.map Complex.ofReal) z i).re =
      Matrix.mulVec A (fun k => (z k).re) i := by
  simp [Matrix.mulVec, dotProduct, Complex.mul_re]

theorem complexified_matrix_mulVec_im {j D : ℕ} (A : Matrix (Fin j) (Fin D) ℝ)
    (z : Fin D → ℂ) (i : Fin j) :
    (Matrix.mulVec (A.map Complex.ofReal) z i).im =
      Matrix.mulVec A (fun k => (z k).im) i := by
  simp [Matrix.mulVec, dotProduct, Complex.mul_im]

theorem complexified_matrix_kernel_mem_iff {j D : ℕ} (A : Matrix (Fin j) (Fin D) ℝ)
    (z : Fin D → ℂ) :
    z ∈ (A.map Complex.ofReal).mulVecLin.ker ↔
      (fun k => (z k).re) ∈ A.mulVecLin.ker ∧
        (fun k => (z k).im) ∈ A.mulVecLin.ker := by
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, funext_iff, Pi.zero_apply]
  constructor
  · intro h
    constructor
    · intro i
      have hh := congrArg Complex.re (h i)
      simpa only [complexified_matrix_mulVec_re, Complex.zero_re] using hh
    · intro i
      have hh := congrArg Complex.im (h i)
      simpa only [complexified_matrix_mulVec_im, Complex.zero_im] using hh
  · rintro ⟨hr, hi⟩ i
    apply Complex.ext
    · simpa only [complexified_matrix_mulVec_re, Complex.zero_re] using hr i
    · simpa only [complexified_matrix_mulVec_im, Complex.zero_im] using hi i

/-- The complex kernel consists exactly of a real kernel vector plus `I` times another. -/
def complexifiedMatrixKernelEquiv {j D : ℕ} (A : Matrix (Fin j) (Fin D) ℝ) :
    (A.map Complex.ofReal).mulVecLin.ker ≃ₗ[ℝ] A.mulVecLin.ker × A.mulVecLin.ker where
  toFun z :=
    (⟨fun k => (z.val k).re, ((complexified_matrix_kernel_mem_iff A z.val).mp z.property).1⟩,
     ⟨fun k => (z.val k).im, ((complexified_matrix_kernel_mem_iff A z.val).mp z.property).2⟩)
  invFun xy := ⟨fun k => (xy.1.val k : ℂ) + (xy.2.val k : ℂ) * Complex.I,
    (complexified_matrix_kernel_mem_iff A _).mpr ⟨by simp, by simp⟩⟩
  left_inv := by
    intro z
    ext k
    exact Complex.re_add_im (z.val k)
  right_inv := by
    intro xy
    ext k <;> simp
  map_add' := by
    intro z w
    ext k <;> simp
  map_smul' := by
    intro c z
    ext k <;> simp

theorem complexified_matrix_finrank_kernel {j D : ℕ} (A : Matrix (Fin j) (Fin D) ℝ) :
    Module.finrank ℂ (A.map Complex.ofReal).mulVecLin.ker =
      Module.finrank ℝ A.mulVecLin.ker := by
  have heq := (complexifiedMatrixKernelEquiv A).finrank_eq
  rw [Module.finrank_prod] at heq
  have htower := Module.finrank_mul_finrank ℝ ℂ (A.map Complex.ofReal).mulVecLin.ker
  rw [Complex.finrank_real_complex] at htower
  omega

theorem complexified_matrix_finrank_range {j D : ℕ} (A : Matrix (Fin j) (Fin D) ℝ) :
    Module.finrank ℂ (A.map Complex.ofReal).mulVecLin.range =
      Module.finrank ℝ A.mulVecLin.range := by
  have hcomplex := (A.map Complex.ofReal).mulVecLin.finrank_range_add_finrank_ker
  have hreal := A.mulVecLin.finrank_range_add_finrank_ker
  rw [complexified_matrix_finrank_kernel] at hcomplex
  simp only [Module.finrank_pi, Fintype.card_fin] at hcomplex hreal
  omega

theorem complexified_matrix_rank {j D : ℕ} (A : Matrix (Fin j) (Fin D) ℝ) :
    (A.map Complex.ofReal).rank = A.rank :=
  complexified_matrix_finrank_range A

/-- A finite independent family of real vectors remains independent over the complex numbers. -/
theorem linearIndependent_complexification {r D : ℕ} (v : Fin r → Fin D → ℝ)
    (hv : LinearIndependent ℝ v) :
    LinearIndependent ℂ (fun i k => (v i k : ℂ)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hre : ∑ k, (c k).re • v k = 0 := by
    funext t
    have hh := congrArg Complex.re (congrFun hc t)
    simpa [Finset.sum_apply, Complex.mul_re] using hh
  have him : ∑ k, (c k).im • v k = 0 := by
    funext t
    have hh := congrArg Complex.im (congrFun hc t)
    simpa [Finset.sum_apply, Complex.mul_im] using hh
  apply Complex.ext
  · exact (Fintype.linearIndependent_iff.mp hv) (fun k => (c k).re) hre i
  · exact (Fintype.linearIndependent_iff.mp hv) (fun k => (c k).im) him i

/-- Any real basis of the real kernel extends to a complex basis consisting of the same real vectors. -/
theorem complexified_matrix_has_real_basis {j D r : ℕ} (A : Matrix (Fin j) (Fin D) ℝ)
    (b : Module.Basis (Fin r) ℝ A.mulVecLin.ker) :
    ∃ c : Module.Basis (Fin r) ℂ (A.map Complex.ofReal).mulVecLin.ker,
      ∀ i k, (c i).val k = ((b i).val k : ℂ) := by
  classical
  let v : Fin r → Fin D → ℝ := fun i => (b i).val
  have hv : LinearIndependent ℝ v := b.linearIndependent.map' A.mulVecLin.ker.subtype (by simp)
  have hmem (i : Fin r) : (fun k => (v i k : ℂ)) ∈ (A.map Complex.ofReal).mulVecLin.ker := by
    rw [complexified_matrix_kernel_mem_iff]
    constructor
    · simp [v]
    · apply LinearMap.mem_ker.mpr
      funext k
      change (∑ l : Fin D, A k l * (Complex.ofReal (v i l)).im) = 0
      simp
  let w : Fin r → (A.map Complex.ofReal).mulVecLin.ker := fun i => ⟨_, hmem i⟩
  have hw : LinearIndependent ℂ w := by
    apply LinearIndependent.of_comp (f := (A.map Complex.ofReal).mulVecLin.ker.subtype)
    exact linearIndependent_complexification v hv
  have hcard : Fintype.card (Fin r) = Module.finrank ℂ (A.map Complex.ofReal).mulVecLin.ker := by
    rw [complexified_matrix_finrank_kernel, Module.finrank_eq_card_basis b]
  let c := basisOfLinearIndependentOfCardEqFinrank' w hw hcard
  refine ⟨c, ?_⟩
  intro i k
  have hc : c i = w i := congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' w hw hcard) i
  rw [hc]

end KungTraub
