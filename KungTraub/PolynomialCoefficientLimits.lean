import KungTraub.PolynomialWronskians
import KungTraub.PolynomialRootLimits

/-!
# Coefficientwise limits of finite polynomial constructions

This module supplies the coefficientwise continuity used for converging bases in the
Wronskian localisation proof. Every coefficient of a product is a finite convolution, and
the determinant is a finite sum of finite products. Thus these statements do not require
the degrees or leading coefficients to remain fixed.

The implementation uses Mathlib's polynomial coefficient identities, derivative formula,
finite-sum limit theorem, and permutation expansion `Matrix.det_apply`. The Wronskian
definition is the finite-family definition in `KungTraub.PolynomialWronskians`.
-/

noncomputable section

open Filter Polynomial
open scoped BigOperators Topology

namespace KungTraub

/-- Addition preserves coefficientwise convergence. -/
theorem polynomial_coeff_tendsto_add {P Q : ℕ → Polynomial ℂ} {p q : Polynomial ℂ}
    (hP : ∀ k, Tendsto (fun n => (P n).coeff k) atTop (𝓝 (p.coeff k)))
    (hQ : ∀ k, Tendsto (fun n => (Q n).coeff k) atTop (𝓝 (q.coeff k))) (k : ℕ) :
    Tendsto (fun n => (P n + Q n).coeff k) atTop (𝓝 ((p + q).coeff k)) := by
  simpa only [Polynomial.coeff_add] using (hP k).add (hQ k)

/-- Polynomial multiplication preserves coefficientwise convergence, without a degree
bound, because each target coefficient is a finite convolution. -/
theorem polynomial_coeff_tendsto_mul {P Q : ℕ → Polynomial ℂ} {p q : Polynomial ℂ}
    (hP : ∀ k, Tendsto (fun n => (P n).coeff k) atTop (𝓝 (p.coeff k)))
    (hQ : ∀ k, Tendsto (fun n => (Q n).coeff k) atTop (𝓝 (q.coeff k))) (k : ℕ) :
    Tendsto (fun n => (P n * Q n).coeff k) atTop (𝓝 ((p * q).coeff k)) := by
  simp only [Polynomial.coeff_mul]
  exact tendsto_finsetSum _ fun ij _ => (hP ij.1).mul (hQ ij.2)

/-- A convergent complex scalar and a coefficientwise convergent polynomial give a
coefficientwise convergent scalar multiple. -/
theorem polynomial_coeff_tendsto_smul {P : ℕ → Polynomial ℂ} {p : Polynomial ℂ}
    {c : ℕ → ℂ} {a : ℂ}
    (hc : Tendsto c atTop (𝓝 a))
    (hP : ∀ k, Tendsto (fun n => (P n).coeff k) atTop (𝓝 (p.coeff k))) (k : ℕ) :
    Tendsto (fun n => (c n • P n).coeff k) atTop (𝓝 ((a • p).coeff k)) := by
  simpa only [Polynomial.coeff_smul, smul_eq_mul] using hc.mul (hP k)

/-- Finite sums preserve coefficientwise convergence. -/
theorem polynomial_coeff_tendsto_finsetSum {ι : Type*} (s : Finset ι)
    {P : ℕ → ι → Polynomial ℂ} {p : ι → Polynomial ℂ}
    (hP : ∀ i ∈ s, ∀ k, Tendsto (fun n => (P n i).coeff k) atTop (𝓝 ((p i).coeff k)))
    (k : ℕ) : Tendsto (fun n => (∑ i ∈ s, P n i).coeff k) atTop
      (𝓝 ((∑ i ∈ s, p i).coeff k)) := by
  simpa only [Polynomial.finsetSum_coeff] using tendsto_finsetSum s (fun i hi => hP i hi k)

/-- Finite products preserve coefficientwise convergence. -/
theorem polynomial_coeff_tendsto_finsetProd {ι : Type*} (s : Finset ι)
    {P : ℕ → ι → Polynomial ℂ} {p : ι → Polynomial ℂ}
    (hP : ∀ i ∈ s, ∀ k, Tendsto (fun n => (P n i).coeff k) atTop (𝓝 ((p i).coeff k))) :
    ∀ k, Tendsto (fun n => (∏ i ∈ s, P n i).coeff k) atTop
      (𝓝 ((∏ i ∈ s, p i).coeff k)) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro k; simp only [Finset.prod_empty]; exact tendsto_const_nhds
  | @insert i s hi ih =>
    have hiP := hP i (Finset.mem_insert_self i s)
    have hsP := ih (fun j hj => hP j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.prod_insert hi] using polynomial_coeff_tendsto_mul hiP hsP

/-- Formal polynomial differentiation preserves coefficientwise convergence. -/
theorem polynomial_coeff_tendsto_derivative {P : ℕ → Polynomial ℂ} {p : Polynomial ℂ}
    (hP : ∀ k, Tendsto (fun n => (P n).coeff k) atTop (𝓝 (p.coeff k))) (k : ℕ) :
    Tendsto (fun n => (Polynomial.derivative (P n)).coeff k) atTop
      (𝓝 ((Polynomial.derivative p).coeff k)) := by
  simpa only [Polynomial.coeff_derivative] using (hP (k + 1)).mul_const (k + 1 : ℂ)

/-- Every fixed iterated polynomial derivative preserves coefficientwise convergence. -/
theorem polynomial_coeff_tendsto_iterate_derivative {P : ℕ → Polynomial ℂ}
    {p : Polynomial ℂ}
    (hP : ∀ k, Tendsto (fun n => (P n).coeff k) atTop (𝓝 (p.coeff k))) (j : ℕ) :
    ∀ k, Tendsto (fun n => (Polynomial.derivative^[j] (P n)).coeff k) atTop
      (𝓝 ((Polynomial.derivative^[j] p).coeff k)) := by
  induction j with
  | zero => simpa only [Function.iterate_zero_apply] using hP
  | succ j ih =>
    simpa only [Function.iterate_succ_apply'] using polynomial_coeff_tendsto_derivative ih

/-- The determinant of a fixed finite polynomial matrix respects coefficientwise limits. -/
theorem polynomial_coeff_tendsto_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ℕ → Matrix ι ι (Polynomial ℂ)} {a : Matrix ι ι (Polynomial ℂ)}
    (hA : ∀ i j k, Tendsto (fun n => (A n i j).coeff k) atTop (𝓝 ((a i j).coeff k)))
    (k : ℕ) : Tendsto (fun n => (A n).det.coeff k) atTop (𝓝 (a.det.coeff k)) := by
  simp only [Matrix.det_apply]
  apply polynomial_coeff_tendsto_finsetSum
  intro σ _ l
  have hprod := polynomial_coeff_tendsto_finsetProd Finset.univ
    (fun i _ j => hA (σ i) i j) l
  simpa only [Polynomial.coeff_smul] using hprod.const_smul (Equiv.Perm.sign σ)

/-- The Wronskians of coefficientwise convergent finite polynomial families converge
coefficientwise. Independence is unnecessary for continuity and is imposed separately
when the limiting Wronskian is required to be nonzero. -/
theorem polynomialWronskian_coeff_tendsto {m : ℕ}
    {P : ℕ → Fin m → Polynomial ℂ} {p : Fin m → Polynomial ℂ}
    (hP : ∀ i k, Tendsto (fun n => (P n i).coeff k) atTop (𝓝 ((p i).coeff k))) (k : ℕ) :
    Tendsto (fun n => (polynomialWronskian (P n)).coeff k) atTop
      (𝓝 ((polynomialWronskian p).coeff k)) := by
  apply polynomial_coeff_tendsto_det
  intro i j l
  exact polynomial_coeff_tendsto_iterate_derivative (hP j) i.val l

/-- Finite linear combinations respect simultaneous convergence of their polynomial
families and their complex coefficient vectors. -/
theorem polynomialCombination_coeff_tendsto {m : ℕ}
    {P : ℕ → Fin m → Polynomial ℂ} {p : Fin m → Polynomial ℂ}
    {c : ℕ → Fin m → ℂ} {a : Fin m → ℂ}
    (hP : ∀ i k, Tendsto (fun n => (P n i).coeff k) atTop (𝓝 ((p i).coeff k)))
    (hc : ∀ i, Tendsto (fun n => c n i) atTop (𝓝 (a i))) (k : ℕ) :
    Tendsto (fun n => (polynomialCombination (P n) (c n)).coeff k) atTop
      (𝓝 ((polynomialCombination p a).coeff k)) := by
  apply polynomial_coeff_tendsto_finsetSum
  intro i _ l
  exact polynomial_coeff_tendsto_smul (hc i) (hP i) l

end KungTraub
