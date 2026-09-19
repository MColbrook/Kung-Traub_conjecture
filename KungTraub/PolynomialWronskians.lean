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
  simp [polynomialWronskian]

theorem polynomialWronskian_eval {m : ℕ} (p : Fin m → Polynomial ℂ) (a : ℂ) :
    (polynomialWronskian p).eval a = (polynomialJetMatrix p a).det := by
  exact (Polynomial.evalRingHom a).map_det (polynomialWronskianMatrix p)

theorem polynomialCombination_iterate_derivative {m : ℕ}
    (p : Fin m → Polynomial ℂ) (c : Fin m → ℂ) (k : ℕ) :
    Polynomial.derivative^[k] (polynomialCombination p c) =
      ∑ i, c i • Polynomial.derivative^[k] (p i) := by
  simp [polynomialCombination, Polynomial.iterate_derivative_sum]

theorem polynomialJetMatrix_mulVec {m : ℕ} (p : Fin m → Polynomial ℂ)
    (c : Fin m → ℂ) (a : ℂ) (k : Fin m) :
    (Matrix.mulVec (polynomialJetMatrix p a) c) k =
      (Polynomial.derivative^[k.val] (polynomialCombination p c)).eval a := by
  rw [polynomialCombination_iterate_derivative]
  simp [polynomialJetMatrix, Matrix.mulVec, dotProduct, Polynomial.eval_finsetSum,
    Polynomial.eval_smul, mul_comm]

theorem polynomialWronskianMatrix_familyChange {m : ℕ}
    (p : Fin m → Polynomial ℂ) (A : Matrix (Fin m) (Fin m) ℂ) :
    polynomialWronskianMatrix (polynomialFamilyChange p A) =
      polynomialWronskianMatrix p * Polynomial.C.mapMatrix A := by
  ext k j
  simp [polynomialWronskianMatrix, polynomialFamilyChange,
    polynomialCombination_iterate_derivative, Matrix.mul_apply,
    Polynomial.smul_eq_C_mul, mul_comm]

/-- Constant changes of family multiply the Wronskian by the matrix determinant. -/
theorem polynomialWronskian_familyChange {m : ℕ}
    (p : Fin m → Polynomial ℂ) (A : Matrix (Fin m) (Fin m) ℂ) :
    polynomialWronskian (polynomialFamilyChange p A) =
      Polynomial.C A.det * polynomialWronskian p := by
  rw [polynomialWronskian, polynomialWronskianMatrix_familyChange, Matrix.det_mul,
    ← Polynomial.C.map_det]
  exact mul_comm _ _

theorem polynomialWronskian_familyChange_eval_eq_zero_iff {m : ℕ}
    (p : Fin m → Polynomial ℂ) (A : Matrix (Fin m) (Fin m) ℂ)
    (hA : A.det ≠ 0) (a : ℂ) :
    (polynomialWronskian (polynomialFamilyChange p A)).eval a = 0 ↔
      (polynomialWronskian p).eval a = 0 := by
  simp [polynomialWronskian_familyChange, hA]

theorem polynomialWronskian_familyChange_degree {m : ℕ}
    (p : Fin m → Polynomial ℂ) (A : Matrix (Fin m) (Fin m) ℂ)
    (hA : A.det ≠ 0) :
    (polynomialWronskian (polynomialFamilyChange p A)).degree =
      (polynomialWronskian p).degree := by
  rw [polynomialWronskian_familyChange, Polynomial.degree_C_mul hA]

/-- Two bases of the same polynomial subspace differ by a nonzero constant factor. -/
theorem polynomialWronskian_basis_change {m : ℕ} (V : Submodule ℂ (Polynomial ℂ))
    (b b' : Module.Basis (Fin m) ℂ V) :
    ∃ c : ℂ, c ≠ 0 ∧
      polynomialWronskian (fun i => (b' i : Polynomial ℂ)) =
        Polynomial.C c * polynomialWronskian (fun i => (b i : Polynomial ℂ)) := by
  have hchange : polynomialFamilyChange (fun i => (b i : Polynomial ℂ)) (b.toMatrix b') =
      fun i => (b' i : Polynomial ℂ) := by
    funext j
    have h := congrArg (fun q : V => (q : Polynomial ℂ)) (b.sum_toMatrix_smul_self b' j)
    simpa only [polynomialFamilyChange, polynomialCombination,
      Submodule.coe_sum, Submodule.coe_smul] using h
  refine ⟨(b.toMatrix b').det,
    Matrix.det_ne_zero_of_right_inverse (b.toMatrix_mul_toMatrix_flip b'), ?_⟩
  rw [← hchange, polynomialWronskian_familyChange]

/-- A zero Wronskian value is precisely a nontrivial kernel of the derivative-value matrix. -/
theorem polynomialWronskian_eval_eq_zero_iff_coefficients {m : ℕ}
    (p : Fin m → Polynomial ℂ) (a : ℂ) :
    (polynomialWronskian p).eval a = 0 ↔
      ∃ c : Fin m → ℂ, c ≠ 0 ∧ ∀ k : Fin m,
        (Polynomial.derivative^[k.val] (polynomialCombination p c)).eval a = 0 := by
  rw [polynomialWronskian_eval, ← Matrix.exists_mulVec_eq_zero_iff]
  constructor
  · rintro ⟨c, hc, hzero⟩
    refine ⟨c, hc, fun k => ?_⟩
    rw [← polynomialJetMatrix_mulVec, hzero]
    rfl
  · rintro ⟨c, hc, hzero⟩
    refine ⟨c, hc, funext fun k => ?_⟩
    exact (polynomialJetMatrix_mulVec p c a k).trans (hzero k)

theorem polynomialCombination_ne_zero {m : ℕ} (p : Fin m → Polynomial ℂ)
    (hp : LinearIndependent ℂ p) (c : Fin m → ℂ) (hc : c ≠ 0) :
    polynomialCombination p c ≠ 0 := by
  intro hzero
  apply hc
  funext i
  exact linearIndependent_iff'.mp hp Finset.univ c hzero i (Finset.mem_univ _)

/-- The vanishing-derivative criterion expressed intrinsically in the family's span. -/
theorem polynomialWronskian_eval_eq_zero_iff_span {m : ℕ}
    (p : Fin m → Polynomial ℂ) (hp : LinearIndependent ℂ p) (a : ℂ) :
    (polynomialWronskian p).eval a = 0 ↔
      ∃ q ∈ Submodule.span ℂ (Set.range p), q ≠ 0 ∧ ∀ k : Fin m,
        (Polynomial.derivative^[k.val] q).eval a = 0 := by
  rw [polynomialWronskian_eval_eq_zero_iff_coefficients]
  constructor
  · rintro ⟨c, hc, hzero⟩
    exact ⟨polynomialCombination p c,
      (Submodule.mem_span_range_iff_exists_fun ℂ).mpr ⟨c, rfl⟩,
      polynomialCombination_ne_zero p hp c hc, hzero⟩
  · rintro ⟨q, hq, hqzero, hzero⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hq
    have hcp : polynomialCombination p c = q := hc
    refine ⟨c, ?_, ?_⟩
    · intro hc0
      apply hqzero
      rw [← hcp, hc0]
      simp [polynomialCombination]
    · simpa [hcp] using hzero

/-- The jet criterion retains actual root multiplicity, with the nonzero hypothesis explicit. -/
theorem polynomial_jets_vanish_iff_multiplicity {m : ℕ} (hm : 0 < m)
    (q : Polynomial ℂ) (hq : q ≠ 0) (a : ℂ) :
    (∀ k : Fin m, (Polynomial.derivative^[k.val] q).eval a = 0) ↔
      m ≤ q.rootMultiplicity a := by
  constructor
  · intro h
    have hr : m - 1 < q.rootMultiplicity a :=
      Polynomial.lt_rootMultiplicity_of_isRoot_iterate_derivative hq (by
        intro k hk
        exact h ⟨k, by omega⟩)
    omega
  · intro h k
    exact Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity (k.isLt.trans_le h)

/-- The manuscript's pointwise Wronskian criterion for every nonempty independent family. -/
theorem polynomialWronskian_eval_eq_zero_iff_multiplicity {m : ℕ} (hm : 0 < m)
    (p : Fin m → Polynomial ℂ) (hp : LinearIndependent ℂ p) (a : ℂ) :
    (polynomialWronskian p).eval a = 0 ↔
      ∃ q ∈ Submodule.span ℂ (Set.range p), q ≠ 0 ∧ m ≤ q.rootMultiplicity a := by
  rw [polynomialWronskian_eval_eq_zero_iff_span p hp a]
  apply exists_congr
  intro q
  apply and_congr_right
  intro _
  apply and_congr_right
  intro hq
  exact polynomial_jets_vanish_iff_multiplicity hm q hq a

/-- The standard monomials have the nonzero constant Wronskian used for the full space. -/
theorem polynomialWronskian_monomials (m : ℕ) :
    polynomialWronskian (fun i : Fin m => (Polynomial.X : Polynomial ℂ) ^ i.val) =
      Polynomial.C (∏ i : Fin m, (i.val.factorial : ℂ)) := by
  have htri : (polynomialWronskianMatrix
      (fun i : Fin m => (Polynomial.X : Polynomial ℂ) ^ i.val)).IsUpperTriangular := by
    intro i j hij
    apply Polynomial.iterate_derivative_eq_zero
    change j.val < i.val at hij
    simpa only [Polynomial.natDegree_X_pow] using hij
  rw [polynomialWronskian, Matrix.det_of_isUpperTriangular htri]
  simp [polynomialWronskianMatrix, Polynomial.iterate_derivative_X_pow_eq_C_mul,
    Nat.descFactorial_self, map_prod]

theorem polynomialWronskian_monomials_ne_zero (m : ℕ) :
    polynomialWronskian (fun i : Fin m => (Polynomial.X : Polynomial ℂ) ^ i.val) ≠ 0 := by
  rw [polynomialWronskian_monomials]
  apply Polynomial.C_ne_zero.mpr
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))

/-- Invertible changes of the monomial family still have a nonzero constant Wronskian. -/
theorem polynomialWronskian_changed_monomials {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) :
    polynomialWronskian (polynomialFamilyChange
      (fun i : Fin m => (Polynomial.X : Polynomial ℂ) ^ i.val) A) =
      Polynomial.C (A.det * ∏ i : Fin m, (i.val.factorial : ℂ)) := by
  rw [polynomialWronskian_familyChange, polynomialWronskian_monomials, Polynomial.C_mul]

theorem polynomialWronskian_changed_monomials_ne_zero {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℂ) (hA : A.det ≠ 0) :
    polynomialWronskian (polynomialFamilyChange
      (fun i : Fin m => (Polynomial.X : Polynomial ℂ) ^ i.val) A) ≠ 0 := by
  rw [polynomialWronskian_familyChange]
  exact mul_ne_zero (Polynomial.C_ne_zero.mpr hA) (polynomialWronskian_monomials_ne_zero m)

/-- The falling-factorial determinant is the Vandermonde determinant, without a sign change.
This uses Mathlib's determinant theorem for evaluations of monic polynomial sequences. -/
theorem fallingFactorial_det_eq_vandermonde {m : ℕ} (d : Fin m → ℕ) :
    (Matrix.of (fun k j : Fin m => (Nat.descFactorial (d j) k.val : ℂ))).det =
      (Matrix.vandermonde (fun j => (d j : ℂ))).det := by
  have h := Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde
    (fun j : Fin m => (d j : ℂ))
    (fun k : Fin m => descPochhammer ℂ k.val)
    (fun k => descPochhammer_natDegree ℂ k.val)
    (fun k => monic_descPochhammer ℂ k.val)
  rw [← Matrix.det_transpose]
  rw [show (Matrix.of (fun k j : Fin m => (Nat.descFactorial (d j) k.val : ℂ))).transpose =
      Matrix.of (fun i j : Fin m => (Nat.descFactorial (d i) j.val : ℂ)) by ext i j; rfl]
  simpa only [descPochhammer_eval_eq_descFactorial, Matrix.transpose_apply,
    Matrix.of_apply] using h.symm

theorem fallingFactorial_det_ne_zero {m : ℕ} (d : Fin m → ℕ)
    (hd : Function.Injective d) :
    (Matrix.of (fun k j : Fin m => (Nat.descFactorial (d j) k.val : ℂ))).det ≠ 0 := by
  rw [fallingFactorial_det_eq_vandermonde]
  apply Matrix.det_vandermonde_ne_zero_iff.mpr
  intro i j hij
  exact hd (Nat.cast_injective hij)

/-- The coefficient at the sum of individual degree bounds in a finite product. -/
theorem polynomial_coeff_prod_degreeBounds {ι : Type*} (s : Finset ι)
    (q : ι → Polynomial ℂ) (d : ι → ℕ)
    (hq : ∀ i ∈ s, (q i).natDegree ≤ d i) :
    (∏ i ∈ s, q i).coeff (∑ i ∈ s, d i) = ∏ i ∈ s, (q i).coeff (d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hiq := hq i (Finset.mem_insert_self _ _)
    have hsq : ∀ j ∈ s, (q j).natDegree ≤ d j :=
      fun j hj => hq j (Finset.mem_insert_of_mem hj)
    have hsdegree : (∏ j ∈ s, q j).natDegree ≤ ∑ j ∈ s, d j :=
      (Polynomial.natDegree_prod_le _ _).trans (Finset.sum_le_sum hsq)
    rw [Finset.prod_insert hi, Finset.sum_insert hi, Finset.prod_insert hi,
      Polynomial.coeff_mul_add_eq_of_natDegree_le hiq hsdegree, ih hsq]

/-- A determinant with a separate degree bound on each column has the expected top coefficient. -/
theorem polynomial_det_coeff_degreeBounds {m : ℕ}
    (M : Matrix (Fin m) (Fin m) (Polynomial ℂ)) (d : Fin m → ℕ)
    (hM : ∀ i j, (M i j).natDegree ≤ d j) :
    M.det.coeff (∑ j, d j) = (Matrix.of (fun i j => (M i j).coeff (d j))).det := by
  simp only [Matrix.det_apply, Polynomial.finsetSum_coeff, Polynomial.coeff_smul]
  apply Finset.sum_congr rfl
  intro σ _
  rw [polynomial_coeff_prod_degreeBounds Finset.univ (fun i => M (σ i) i) d
    (fun i _ => hM (σ i) i)]
  rfl

theorem polynomial_det_natDegree_le_degreeBounds {m : ℕ}
    (M : Matrix (Fin m) (Fin m) (Polynomial ℂ)) (d : Fin m → ℕ)
    (hM : ∀ i j, (M i j).natDegree ≤ d j) : M.det.natDegree ≤ ∑ j, d j := by
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ _
  exact (Polynomial.natDegree_smul_le _ _).trans
    ((Polynomial.natDegree_prod_le _ _).trans (Finset.sum_le_sum (fun i _ => hM (σ i) i)))

/-- Multiplication by `X^k` restores the degree lost after `k` derivatives. -/
theorem polynomial_weighted_derivative_natDegree_le (q : Polynomial ℂ) (k : ℕ) :
    ((Polynomial.X ^ k) * Polynomial.derivative^[k] q).natDegree ≤ q.natDegree := by
  by_cases hk : k ≤ q.natDegree
  · calc
      _ ≤ (Polynomial.X ^ k : Polynomial ℂ).natDegree +
          (Polynomial.derivative^[k] q).natDegree := Polynomial.natDegree_mul_le
      _ ≤ k + (q.natDegree - k) := by
        rw [Polynomial.natDegree_X_pow]
        exact Nat.add_le_add_left (Polynomial.natDegree_iterate_derivative q k) k
      _ = q.natDegree := Nat.add_sub_of_le hk
  · rw [Polynomial.iterate_derivative_eq_zero (Nat.lt_of_not_ge hk)]
    simp

theorem polynomial_weighted_derivative_coeff (q : Polynomial ℂ) (k d : ℕ) :
    ((Polynomial.X ^ k) * Polynomial.derivative^[k] q).coeff d =
      (Nat.descFactorial d k : ℂ) * q.coeff d := by
  rw [Polynomial.coeff_X_pow_mul']
  by_cases hk : k ≤ d
  · rw [if_pos hk, Polynomial.coeff_iterate_derivative, Nat.sub_add_cancel hk, nsmul_eq_mul]
  · rw [if_neg hk, Nat.descFactorial_eq_zero_iff_lt.mpr (Nat.lt_of_not_ge hk)]
    simp

/-- The row-weighted derivative matrix keeps a common degree bound within each column. -/
def weightedPolynomialWronskianMatrix {m : ℕ} (p : Fin m → Polynomial ℂ) :
    Matrix (Fin m) (Fin m) (Polynomial ℂ) :=
  fun k j => Polynomial.X ^ k.val * Polynomial.derivative^[k.val] (p j)

theorem weightedPolynomialWronskianMatrix_det {m : ℕ} (p : Fin m → Polynomial ℂ) :
    (weightedPolynomialWronskianMatrix p).det =
      Polynomial.X ^ (∑ k : Fin m, k.val) * polynomialWronskian p := by
  change (Matrix.of (fun k j : Fin m =>
    (Polynomial.X : Polynomial ℂ) ^ k.val * polynomialWronskianMatrix p k j)).det = _
  rw [Matrix.det_mul_column]
  rw [Finset.prod_pow_eq_pow_sum]
  rfl

/-- The top coefficient is the leading-coefficient product times the degree Vandermonde. -/
theorem weightedPolynomialWronskianMatrix_top_coeff {m : ℕ}
    (p : Fin m → Polynomial ℂ) :
    (weightedPolynomialWronskianMatrix p).det.coeff (∑ j, (p j).natDegree) =
      (∏ j, (p j).leadingCoeff) *
        (Matrix.vandermonde (fun j => ((p j).natDegree : ℂ))).det := by
  rw [polynomial_det_coeff_degreeBounds (weightedPolynomialWronskianMatrix p) (fun j => (p j).natDegree)
    (fun k j => polynomial_weighted_derivative_natDegree_le (p j) k.val)]
  simp only [weightedPolynomialWronskianMatrix, polynomial_weighted_derivative_coeff,
    Polynomial.coeff_natDegree]
  rw [show (Matrix.of (fun i j : Fin m =>
      (((p j).natDegree.descFactorial i.val : ℕ) : ℂ) * (p j).leadingCoeff)) =
      Matrix.of (fun i j : Fin m => (p j).leadingCoeff *
        (((p j).natDegree.descFactorial i.val : ℕ) : ℂ)) by ext i j; exact mul_comm _ _]
  calc
    _ = (∏ j, (p j).leadingCoeff) *
        (Matrix.of (fun i j : Fin m => (((p j).natDegree.descFactorial i.val : ℕ) : ℂ))).det := by
      simpa only [Matrix.of_apply] using Matrix.det_mul_row (fun j : Fin m => (p j).leadingCoeff)
        (Matrix.of (fun i j : Fin m => (((p j).natDegree.descFactorial i.val : ℕ) : ℂ)))
    _ = _ := by rw [fallingFactorial_det_eq_vandermonde]

/-- Nonzero polynomials of pairwise distinct degrees have a nonzero Wronskian. -/
theorem polynomialWronskian_ne_zero_of_injective_natDegree {m : ℕ}
    (p : Fin m → Polynomial ℂ) (hp : ∀ i, p i ≠ 0)
    (hdegree : Function.Injective (fun i => (p i).natDegree)) :
    polynomialWronskian p ≠ 0 := by
  have htop : (weightedPolynomialWronskianMatrix p).det.coeff
      (∑ j, (p j).natDegree) ≠ 0 := by
    rw [weightedPolynomialWronskianMatrix_top_coeff]
    apply mul_ne_zero
    · exact Finset.prod_ne_zero_iff.mpr (fun i _ => Polynomial.leadingCoeff_ne_zero.mpr (hp i))
    · apply Matrix.det_vandermonde_ne_zero_iff.mpr
      intro i j hij
      exact hdegree (Nat.cast_injective hij)
  intro hzero
  rw [weightedPolynomialWronskianMatrix_det, hzero, mul_zero, Polynomial.coeff_zero] at htop
  exact htop rfl

/-- The degree formula first appears as an additive identity, without natural subtraction. -/
theorem polynomialWronskian_natDegree_add {m : ℕ}
    (p : Fin m → Polynomial ℂ) (hp : ∀ i, p i ≠ 0)
    (hdegree : Function.Injective (fun i => (p i).natDegree)) :
    (polynomialWronskian p).natDegree + (∑ k : Fin m, k.val) = ∑ j, (p j).natDegree := by
  have htop : (weightedPolynomialWronskianMatrix p).det.coeff
      (∑ j, (p j).natDegree) ≠ 0 := by
    rw [weightedPolynomialWronskianMatrix_top_coeff]
    apply mul_ne_zero
    · exact Finset.prod_ne_zero_iff.mpr (fun i _ => Polynomial.leadingCoeff_ne_zero.mpr (hp i))
    · apply Matrix.det_vandermonde_ne_zero_iff.mpr
      intro i j hij
      exact hdegree (Nat.cast_injective hij)
  have hdeg : (weightedPolynomialWronskianMatrix p).det.natDegree =
      ∑ j, (p j).natDegree :=
    le_antisymm (polynomial_det_natDegree_le_degreeBounds _ _
      (fun k j => polynomial_weighted_derivative_natDegree_le (p j) k.val))
      (Polynomial.le_natDegree_of_ne_zero htop)
  rw [weightedPolynomialWronskianMatrix_det, Polynomial.natDegree_mul
    (pow_ne_zero _ Polynomial.X_ne_zero)
    (polynomialWronskian_ne_zero_of_injective_natDegree p hp hdegree),
    Polynomial.natDegree_X_pow] at hdeg
  omega

/-- The degree formula for a family with pairwise distinct degrees. -/
theorem polynomialWronskian_natDegree {m : ℕ}
    (p : Fin m → Polynomial ℂ) (hp : ∀ i, p i ≠ 0)
    (hdegree : Function.Injective (fun i => (p i).natDegree)) :
    (polynomialWronskian p).natDegree =
      (∑ j, (p j).natDegree) - m * (m - 1) / 2 := by
  have h := polynomialWronskian_natDegree_add p hp hdegree
  have hsum : (∑ k : Fin m, k.val) = m * (m - 1) / 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun k => k), Finset.sum_range_id]
  rw [hsum] at h
  omega

/-- The exact leading coefficient in the manuscript's degree computation. -/
theorem polynomialWronskian_leadingCoeff {m : ℕ}
    (p : Fin m → Polynomial ℂ) (hp : ∀ i, p i ≠ 0)
    (hdegree : Function.Injective (fun i => (p i).natDegree)) :
    (polynomialWronskian p).leadingCoeff = (∏ j, (p j).leadingCoeff) *
      (Matrix.vandermonde (fun j => ((p j).natDegree : ℂ))).det := by
  have hdegreeAdd := polynomialWronskian_natDegree_add p hp hdegree
  have htop := weightedPolynomialWronskianMatrix_top_coeff p
  rw [weightedPolynomialWronskianMatrix_det, Polynomial.coeff_X_pow_mul',
    if_pos (show (∑ k : Fin m, k.val) ≤ ∑ j, (p j).natDegree by omega)] at htop
  have hindex : (∑ j, (p j).natDegree) - (∑ k : Fin m, k.val) =
      (polynomialWronskian p).natDegree := by omega
  rw [hindex, Polynomial.coeff_natDegree] at htop
  exact htop

/-- Adding a constant multiple of one family member to a different member preserves the Wronskian. -/
theorem polynomialWronskian_update_add_smul {m : ℕ} (p : Fin m → Polynomial ℂ)
    {i j : Fin m} (hij : i ≠ j) (c : ℂ) :
    polynomialWronskian (Function.update p i (p i + c • p j)) = polynomialWronskian p := by
  have hmatrix : polynomialWronskianMatrix (Function.update p i (p i + c • p j)) =
      Matrix.updateCol (polynomialWronskianMatrix p) i
        (fun k => polynomialWronskianMatrix p k i +
          Polynomial.C c • polynomialWronskianMatrix p k j) := by
    ext k t
    by_cases ht : t = i
    · subst t
      simp [polynomialWronskianMatrix, Matrix.updateCol, iterate_map_add,
        Polynomial.smul_eq_C_mul, smul_eq_mul]
    · simp [polynomialWronskianMatrix, Matrix.updateCol, ht]
  rw [polynomialWronskian, hmatrix]
  exact Matrix.det_updateCol_add_smul_self (polynomialWronskianMatrix p) hij (Polynomial.C c)

/-- Every finite linearly independent family of complex polynomials has a nonzero Wronskian.
The induction cancels a pair of equal leading degrees, strictly decreasing their total. -/
theorem polynomialWronskian_ne_zero_of_linearIndependent {m : ℕ}
    (p : Fin m → Polynomial ℂ) (hp : LinearIndependent ℂ p) : polynomialWronskian p ≠ 0 := by
  classical
  generalize hn : (∑ i, (p i).natDegree) = N
  induction N using Nat.strong_induction_on generalizing p with
  | h N ih =>
    by_cases hd : Function.Injective (fun i => (p i).natDegree)
    · exact polynomialWronskian_ne_zero_of_injective_natDegree p (fun i => hp.ne_zero i) hd
    · simp only [Function.Injective] at hd
      push Not at hd
      obtain ⟨i, j, hdegree, hij⟩ := hd
      let c : ℂ := (p i).leadingCoeff / (p j).leadingCoeff
      let q := Function.update p i (p i - c • p j)
      have hci : (p i).leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr (hp.ne_zero i)
      have hcj : (p j).leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr (hp.ne_zero j)
      have hc : c ≠ 0 := div_ne_zero hci hcj
      have hz : (Pi.single i (-c) : Fin m → ℂ) j = 0 := by simp [hij.symm]
      have hqeq : q = p + (fun t => (Pi.single i (-c) : Fin m → ℂ) t • p j) := by
        funext t
        by_cases ht : t = i
        · subst t
          simp [q, sub_eq_add_neg]
        · simp [q, ht, Pi.single_apply]
      have hq : LinearIndependent ℂ q := by
        rw [hqeq]
        exact (linearIndependent_add_smul_iff hz).mpr hp
      have hqine : p i - c • p j ≠ 0 := by simpa [q] using hq.ne_zero i
      have hdrop : (p i - c • p j).degree < (p i).degree := by
        apply Polynomial.degree_sub_lt_left
        · rw [Polynomial.smul_eq_C_mul, Polynomial.degree_C_mul hc,
            Polynomial.degree_eq_natDegree (hp.ne_zero i),
            Polynomial.degree_eq_natDegree (hp.ne_zero j), hdegree]
        · exact hp.ne_zero i
        · rw [Polynomial.smul_eq_C_mul, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
          exact (div_mul_cancel₀ (p i).leadingCoeff hcj).symm
      have hdropNat : (q i).natDegree < (p i).natDegree := by
        rw [Polynomial.degree_eq_natDegree hqine,
          Polynomial.degree_eq_natDegree (hp.ne_zero i)] at hdrop
        simpa [q] using hdrop
      have hsum : ∑ t, (q t).natDegree < N := by
        rw [← hn]
        apply Finset.sum_lt_sum
        · intro t _
          by_cases ht : t = i
          · subst t; exact hdropNat.le
          · simp [q, ht]
        · exact ⟨i, Finset.mem_univ _, hdropNat⟩
      have hwq := ih (∑ t, (q t).natDegree) hsum q hq rfl
      have hw : polynomialWronskian q = polynomialWronskian p := by
        simpa [q, sub_eq_add_neg] using polynomialWronskian_update_add_smul p hij (-c)
      rwa [hw] at hwq

theorem polynomialWronskian_basis_ne_zero {m : ℕ} (V : Submodule ℂ (Polynomial ℂ))
    (b : Module.Basis (Fin m) ℂ V) :
    polynomialWronskian (fun i => (b i : Polynomial ℂ)) ≠ 0 := by
  exact polynomialWronskian_ne_zero_of_linearIndependent _
    (b.linearIndependent.map' V.subtype (by simp))

theorem polynomialWronskian_basis_degree_eq {m : ℕ} (V : Submodule ℂ (Polynomial ℂ))
    (b b' : Module.Basis (Fin m) ℂ V) :
    (polynomialWronskian (fun i => (b' i : Polynomial ℂ))).degree =
      (polynomialWronskian (fun i => (b i : Polynomial ℂ))).degree := by
  obtain ⟨c, hc, heq⟩ := polynomialWronskian_basis_change V b b'
  rw [heq, Polynomial.degree_C_mul hc]

theorem polynomialWronskian_basis_eval_eq_zero_iff {m : ℕ}
    (V : Submodule ℂ (Polynomial ℂ)) (b b' : Module.Basis (Fin m) ℂ V) (a : ℂ) :
    (polynomialWronskian (fun i => (b' i : Polynomial ℂ))).eval a = 0 ↔
      (polynomialWronskian (fun i => (b i : Polynomial ℂ))).eval a = 0 := by
  obtain ⟨c, hc, heq⟩ := polynomialWronskian_basis_change V b b'
  simp [heq, hc]

end

end KungTraub
