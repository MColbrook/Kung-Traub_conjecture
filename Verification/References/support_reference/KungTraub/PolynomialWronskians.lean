import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic

/-!
# Wronskians of finite families of complex polynomials

The determinant has derivative orders in its rows and family members in its
columns, as in Section 2.1 of Matthew J. Colbrook's `kung_traub_solution.tex`.
The identities below apply to arbitrary finite families. The nonvanishing
theorem and the pointwise span criterion require linear independence.

The implementation uses Mathlib's polynomial derivative, determinant,
matrix-kernel and root-multiplicity theorems. The pinned polynomial Wronskian
module treats pairs only; the finite-family definition here is independent of
that pair definition. The Vandermonde results are due to Anne Baanen and
Peter Nelson in Mathlib; the Pochhammer polynomial results are due to Kim
Morrison.
-/

namespace KungTraub

noncomputable section

open scoped BigOperators

/-- The polynomial matrix whose row `k` contains derivatives of order `k`. -/
def polynomialWronskianMatrix {m : ℕ} (p : Fin m → Polynomial ℂ) :
    Matrix (Fin m) (Fin m) (Polynomial ℂ) :=
  fun k i => Polynomial.derivative^[k.val] (p i)

/-- The Wronskian polynomial of an arbitrary finite family, including the empty family. -/
def polynomialWronskian {m : ℕ} (p : Fin m → Polynomial ℂ) : Polynomial ℂ :=
  (polynomialWronskianMatrix p).det

/-- The matrix of derivative values at a complex point. -/
def polynomialJetMatrix {m : ℕ} (p : Fin m → Polynomial ℂ) (a : ℂ) :
    Matrix (Fin m) (Fin m) ℂ :=
  fun k i => (Polynomial.derivative^[k.val] (p i)).eval a

/-- A finite complex linear combination of the family. -/
def polynomialCombination {m : ℕ} (p : Fin m → Polynomial ℂ) (c : Fin m → ℂ) :
    Polynomial ℂ :=
  ∑ i, c i • p i

/-- A matrix acts on the family through its columns. -/
def polynomialFamilyChange {m : ℕ} (p : Fin m → Polynomial ℂ)
    (A : Matrix (Fin m) (Fin m) ℂ) : Fin m → Polynomial ℂ :=
  fun j => polynomialCombination p (fun i => A i j)

@[simp] theorem polynomialWronskian_empty (p : Fin 0 → Polynomial ℂ) :
    polynomialWronskian p = 1 := by
  sorry

theorem polynomialWronskian_eval {m : ℕ} (p : Fin m → Polynomial ℂ) (a : ℂ) :
    (polynomialWronskian p).eval a = (polynomialJetMatrix p a).det := by
  sorry

theorem polynomialCombination_iterate_derivative {m : ℕ}
    (p : Fin m → Polynomial ℂ) (c : Fin m → ℂ) (k : ℕ) :
    Polynomial.derivative^[k] (polynomialCombination p c) =
      ∑ i, c i • Polynomial.derivative^[k] (p i) := by
  sorry

theorem polynomialJetMatrix_mulVec {m : ℕ} (p : Fin m → Polynomial ℂ)
    (c : Fin m → ℂ) (a : ℂ) (k : Fin m) :
    (Matrix.mulVec (polynomialJetMatrix p a) c) k =
      (Polynomial.derivative^[k.val] (polynomialCombination p c)).eval a := by
  sorry

theorem polynomialWronskianMatrix_familyChange {m : ℕ}
    (p : Fin m → Polynomial ℂ) (A : Matrix (Fin m) (Fin m) ℂ) :
    polynomialWronskianMatrix (polynomialFamilyChange p A) =
      polynomialWronskianMatrix p * Polynomial.C.mapMatrix A := by
  sorry

/-- Constant changes of family multiply the Wronskian by the matrix determinant. -/
theorem polynomialWronskian_familyChange {m : ℕ}
    (p : Fin m → Polynomial ℂ) (A : Matrix (Fin m) (Fin m) ℂ) :
    polynomialWronskian (polynomialFamilyChange p A) =
      Polynomial.C A.det * polynomialWronskian p := by
  sorry

theorem polynomialWronskian_familyChange_eval_eq_zero_iff {m : ℕ}
    (p : Fin m → Polynomial ℂ) (A : Matrix (Fin m) (Fin m) ℂ)
    (hA : A.det ≠ 0) (a : ℂ) :
    (polynomialWronskian (polynomialFamilyChange p A)).eval a = 0 ↔
      (polynomialWronskian p).eval a = 0 := by
  sorry

theorem polynomialWronskian_familyChange_degree {m : ℕ}
    (p : Fin m → Polynomial ℂ) (A : Matrix (Fin m) (Fin m) ℂ)
    (hA : A.det ≠ 0) :
    (polynomialWronskian (polynomialFamilyChange p A)).degree =
      (polynomialWronskian p).degree := by
  sorry

/-- Two bases of the same polynomial subspace differ by a nonzero constant factor. -/
theorem polynomialWronskian_basis_change {m : ℕ} (V : Submodule ℂ (Polynomial ℂ))
    (b b' : Module.Basis (Fin m) ℂ V) :
    ∃ c : ℂ, c ≠ 0 ∧
      polynomialWronskian (fun i => (b' i : Polynomial ℂ)) =
        Polynomial.C c * polynomialWronskian (fun i => (b i : Polynomial ℂ)) := by
  sorry

/-- A zero Wronskian value is precisely a nontrivial kernel of the derivative-value matrix. -/
theorem polynomialWronskian_eval_eq_zero_iff_coefficients {m : ℕ}
    (p : Fin m → Polynomial ℂ) (a : ℂ) :
    (polynomialWronskian p).eval a = 0 ↔
      ∃ c : Fin m → ℂ, c ≠ 0 ∧ ∀ k : Fin m,
        (Polynomial.derivative^[k.val] (polynomialCombination p c)).eval a = 0 := by
  sorry

theorem polynomialCombination_ne_zero {m : ℕ} (p : Fin m → Polynomial ℂ)
    (hp : LinearIndependent ℂ p) (c : Fin m → ℂ) (hc : c ≠ 0) :
    polynomialCombination p c ≠ 0 := by
  sorry

/-- The vanishing-derivative criterion expressed intrinsically in the family's span. -/
theorem polynomialWronskian_eval_eq_zero_iff_span {m : ℕ}
    (p : Fin m → Polynomial ℂ) (hp : LinearIndependent ℂ p) (a : ℂ) :
    (polynomialWronskian p).eval a = 0 ↔
      ∃ q ∈ Submodule.span ℂ (Set.range p), q ≠ 0 ∧ ∀ k : Fin m,
        (Polynomial.derivative^[k.val] q).eval a = 0 := by
  sorry

/-- The jet criterion retains actual root multiplicity, with the nonzero hypothesis explicit. -/
theorem polynomial_jets_vanish_iff_multiplicity {m : ℕ} (hm : 0 < m)
    (q : Polynomial ℂ) (hq : q ≠ 0) (a : ℂ) :
    (∀ k : Fin m, (Polynomial.derivative^[k.val] q).eval a = 0) ↔
      m ≤ q.rootMultiplicity a := by
  sorry

/-- The manuscript's pointwise Wronskian criterion for every nonempty independent family. -/
theorem polynomialWronskian_eval_eq_zero_iff_multiplicity {m : ℕ} (hm : 0 < m)
    (p : Fin m → Polynomial ℂ) (hp : LinearIndependent ℂ p) (a : ℂ) :
    (polynomialWronskian p).eval a = 0 ↔
      ∃ q ∈ Submodule.span ℂ (Set.range p), q ≠ 0 ∧ m ≤ q.rootMultiplicity a := by
  sorry

/-- The standard monomials have the nonzero constant Wronskian used for the full space. -/
theorem polynomialWronskian_monomials (m : ℕ) :
    polynomialWronskian (fun i : Fin m => (Polynomial.X : Polynomial ℂ) ^ i.val) =
      Polynomial.C (∏ i : Fin m, (i.val.factorial : ℂ)) := by
  sorry

theorem polynomialWronskian_monomials_ne_zero (m : ℕ) :
    polynomialWronskian (fun i : Fin m => (Polynomial.X : Polynomial ℂ) ^ i.val) ≠ 0 := by
  sorry

/-- Invertible changes of the monomial family still have a nonzero constant Wronskian. -/
theorem polynomialWronskian_changed_monomials {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) :
    polynomialWronskian (polynomialFamilyChange
      (fun i : Fin m => (Polynomial.X : Polynomial ℂ) ^ i.val) A) =
      Polynomial.C (A.det * ∏ i : Fin m, (i.val.factorial : ℂ)) := by
  sorry

theorem polynomialWronskian_changed_monomials_ne_zero {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (hA : A.det ≠ 0) :
    polynomialWronskian (polynomialFamilyChange
      (fun i : Fin m => (Polynomial.X : Polynomial ℂ) ^ i.val) A) ≠ 0 := by
  sorry

/-- The falling-factorial determinant is the Vandermonde determinant, without a sign change.
This uses Mathlib's determinant theorem for evaluations of monic polynomial sequences. -/
theorem fallingFactorial_det_eq_vandermonde {m : ℕ} (d : Fin m → ℕ) :
    (Matrix.of (fun k j : Fin m => (Nat.descFactorial (d j) k.val : ℂ))).det =
      (Matrix.vandermonde (fun j => (d j : ℂ))).det := by
  sorry

theorem fallingFactorial_det_ne_zero {m : ℕ} (d : Fin m → ℕ)
    (hd : Function.Injective d) :
    (Matrix.of (fun k j : Fin m => (Nat.descFactorial (d j) k.val : ℂ))).det ≠ 0 := by
  sorry

/-- The coefficient at the sum of individual degree bounds in a finite product. -/
theorem polynomial_coeff_prod_degreeBounds {ι : Type*} (s : Finset ι)
    (q : ι → Polynomial ℂ) (d : ι → ℕ)
    (hq : ∀ i ∈ s, (q i).natDegree ≤ d i) :
    (∏ i ∈ s, q i).coeff (∑ i ∈ s, d i) = ∏ i ∈ s, (q i).coeff (d i) := by
  sorry

/-- A determinant with a separate degree bound on each column has the expected top coefficient. -/
theorem polynomial_det_coeff_degreeBounds {m : ℕ}
    (M : Matrix (Fin m) (Fin m) (Polynomial ℂ)) (d : Fin m → ℕ)
    (hM : ∀ i j, (M i j).natDegree ≤ d j) :
    M.det.coeff (∑ j, d j) = (Matrix.of (fun i j => (M i j).coeff (d j))).det := by
  sorry

theorem polynomial_det_natDegree_le_degreeBounds {m : ℕ}
    (M : Matrix (Fin m) (Fin m) (Polynomial ℂ)) (d : Fin m → ℕ)
    (hM : ∀ i j, (M i j).natDegree ≤ d j) : M.det.natDegree ≤ ∑ j, d j := by
  sorry

/-- Multiplication by `X^k` restores the degree lost after `k` derivatives. -/
theorem polynomial_weighted_derivative_natDegree_le (q : Polynomial ℂ) (k : ℕ) :
    ((Polynomial.X ^ k) * Polynomial.derivative^[k] q).natDegree ≤ q.natDegree := by
  sorry

theorem polynomial_weighted_derivative_coeff (q : Polynomial ℂ) (k d : ℕ) :
    ((Polynomial.X ^ k) * Polynomial.derivative^[k] q).coeff d =
      (Nat.descFactorial d k : ℂ) * q.coeff d := by
  sorry

/-- The row-weighted derivative matrix keeps a common degree bound within each column. -/
def weightedPolynomialWronskianMatrix {m : ℕ} (p : Fin m → Polynomial ℂ) :
    Matrix (Fin m) (Fin m) (Polynomial ℂ) :=
  fun k j => Polynomial.X ^ k.val * Polynomial.derivative^[k.val] (p j)

theorem weightedPolynomialWronskianMatrix_det {m : ℕ} (p : Fin m → Polynomial ℂ) :
    (weightedPolynomialWronskianMatrix p).det =
      Polynomial.X ^ (∑ k : Fin m, k.val) * polynomialWronskian p := by
  sorry

/-- The top coefficient is the leading-coefficient product times the degree Vandermonde. -/
theorem weightedPolynomialWronskianMatrix_top_coeff {m : ℕ}
    (p : Fin m → Polynomial ℂ) :
    (weightedPolynomialWronskianMatrix p).det.coeff (∑ j, (p j).natDegree) =
      (∏ j, (p j).leadingCoeff) *
        (Matrix.vandermonde (fun j => ((p j).natDegree : ℂ))).det := by
  sorry

/-- Nonzero polynomials of pairwise distinct degrees have a nonzero Wronskian. -/
theorem polynomialWronskian_ne_zero_of_injective_natDegree {m : ℕ}
    (p : Fin m → Polynomial ℂ) (hp : ∀ i, p i ≠ 0)
    (hdegree : Function.Injective (fun i => (p i).natDegree)) :
    polynomialWronskian p ≠ 0 := by
  sorry

/-- The degree formula first appears as an additive identity, without natural subtraction. -/
theorem polynomialWronskian_natDegree_add {m : ℕ}
    (p : Fin m → Polynomial ℂ) (hp : ∀ i, p i ≠ 0)
    (hdegree : Function.Injective (fun i => (p i).natDegree)) :
    (polynomialWronskian p).natDegree + (∑ k : Fin m, k.val) = ∑ j, (p j).natDegree := by
  sorry

/-- The degree formula for a family with pairwise distinct degrees. -/
theorem polynomialWronskian_natDegree {m : ℕ}
    (p : Fin m → Polynomial ℂ) (hp : ∀ i, p i ≠ 0)
    (hdegree : Function.Injective (fun i => (p i).natDegree)) :
    (polynomialWronskian p).natDegree =
      (∑ j, (p j).natDegree) - m * (m - 1) / 2 := by
  sorry

/-- The exact leading coefficient in the manuscript's degree computation. -/
theorem polynomialWronskian_leadingCoeff {m : ℕ}
    (p : Fin m → Polynomial ℂ) (hp : ∀ i, p i ≠ 0)
    (hdegree : Function.Injective (fun i => (p i).natDegree)) :
    (polynomialWronskian p).leadingCoeff = (∏ j, (p j).leadingCoeff) *
      (Matrix.vandermonde (fun j => ((p j).natDegree : ℂ))).det := by
  sorry

/-- Adding a constant multiple of one family member to a different member preserves the Wronskian. -/
theorem polynomialWronskian_update_add_smul {m : ℕ} (p : Fin m → Polynomial ℂ)
    {i j : Fin m} (hij : i ≠ j) (c : ℂ) :
    polynomialWronskian (Function.update p i (p i + c • p j)) = polynomialWronskian p := by
  sorry

/-- Every finite linearly independent family of complex polynomials has a nonzero Wronskian.
The induction cancels a pair of equal leading degrees, strictly decreasing their total. -/
theorem polynomialWronskian_ne_zero_of_linearIndependent {m : ℕ}
    (p : Fin m → Polynomial ℂ) (hp : LinearIndependent ℂ p) : polynomialWronskian p ≠ 0 := by
  sorry

theorem polynomialWronskian_basis_ne_zero {m : ℕ} (V : Submodule ℂ (Polynomial ℂ))
    (b : Module.Basis (Fin m) ℂ V) :
    polynomialWronskian (fun i => (b i : Polynomial ℂ)) ≠ 0 := by
  sorry

theorem polynomialWronskian_basis_degree_eq {m : ℕ} (V : Submodule ℂ (Polynomial ℂ))
    (b b' : Module.Basis (Fin m) ℂ V) :
    (polynomialWronskian (fun i => (b' i : Polynomial ℂ))).degree =
      (polynomialWronskian (fun i => (b i : Polynomial ℂ))).degree := by
  sorry

theorem polynomialWronskian_basis_eval_eq_zero_iff {m : ℕ}
    (V : Submodule ℂ (Polynomial ℂ)) (b b' : Module.Basis (Fin m) ℂ V) (a : ℂ) :
    (polynomialWronskian (fun i => (b' i : Polynomial ℂ))).eval a = 0 ↔
      (polynomialWronskian (fun i => (b i : Polynomial ℂ))).eval a = 0 := by
  sorry

end

end KungTraub
