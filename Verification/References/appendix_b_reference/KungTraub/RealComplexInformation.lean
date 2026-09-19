import appendix_b_reference.KungTraub.PolynomialInformation
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
  sorry

theorem complexified_matrix_mulVec_im {j D : ℕ} (A : Matrix (Fin j) (Fin D) ℝ)
    (z : Fin D → ℂ) (i : Fin j) :
    (Matrix.mulVec (A.map Complex.ofReal) z i).im =
      Matrix.mulVec A (fun k => (z k).im) i := by
  sorry

theorem complexified_matrix_kernel_mem_iff {j D : ℕ} (A : Matrix (Fin j) (Fin D) ℝ)
    (z : Fin D → ℂ) :
    z ∈ (A.map Complex.ofReal).mulVecLin.ker ↔
      (fun k => (z k).re) ∈ A.mulVecLin.ker ∧
        (fun k => (z k).im) ∈ A.mulVecLin.ker := by
  sorry

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
  sorry

theorem complexified_matrix_finrank_range {j D : ℕ} (A : Matrix (Fin j) (Fin D) ℝ) :
    Module.finrank ℂ (A.map Complex.ofReal).mulVecLin.range =
      Module.finrank ℝ A.mulVecLin.range := by
  sorry

theorem complexified_matrix_rank {j D : ℕ} (A : Matrix (Fin j) (Fin D) ℝ) :
    (A.map Complex.ofReal).rank = A.rank := by
  sorry

/-- A finite independent family of real vectors remains independent over the complex numbers. -/
theorem linearIndependent_complexification {r D : ℕ} (v : Fin r → Fin D → ℝ)
    (hv : LinearIndependent ℝ v) :
    LinearIndependent ℂ (fun i k => (v i k : ℂ)) := by
  sorry

/-- Any real basis of the real kernel extends to a complex basis consisting of the same real vectors. -/
theorem complexified_matrix_has_real_basis {j D r : ℕ} (A : Matrix (Fin j) (Fin D) ℝ)
    (b : Module.Basis (Fin r) ℝ A.mulVecLin.ker) :
    ∃ c : Module.Basis (Fin r) ℂ (A.map Complex.ofReal).mulVecLin.ker,
      ∀ i k, (c i).val k = ((b i).val k : ℂ) := by
  sorry

end KungTraub
