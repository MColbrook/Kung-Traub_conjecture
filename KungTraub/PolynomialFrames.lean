import KungTraub.Coefficients
import KungTraub.PolynomialCoefficientLimits
import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
# Compactness of orthonormal polynomial coefficient frames

The localisation argument takes a subsequence of orthonormal frames in a fixed finite
Euclidean coefficient space. Compactness below comes from finite products of closed unit
balls. Orthonormality follows at the limit by continuity of inner products.
A simultaneously selected unit member stays in the limiting
span by its finite orthonormal expansion, and remains nonzero.

The proofs reuse Mathlib's finite-dimensional compactness and inner-product continuity,
and its orthonormal expansion and independence facts from the module by Zhouhang Zhou,
Sébastien Gouëzel and Frédéric Dupuis.
-/

noncomputable section

open Filter Polynomial
open scoped BigOperators Topology ComplexInnerProductSpace

namespace KungTraub

/-- Pointwise norm limits of orthonormal frames are orthonormal. -/
theorem orthonormal_of_pointwise_tendsto {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {ι : Type*} {V : ℕ → ι → E} {v : ι → E}
    (hV : ∀ n, Orthonormal ℂ (V n))
    (hlim : ∀ i, Tendsto (fun n => V n i) atTop (𝓝 (v i))) : Orthonormal ℂ v := by
  classical
  apply orthonormal_iff_ite.mpr
  intro i j
  have hinner : Tendsto (fun n => ⟪V n i, V n j⟫) atTop (𝓝 ⟪v i, v j⟫) :=
    (hlim i).inner (hlim j)
  have hconst : Tendsto (fun n => ⟪V n i, V n j⟫) atTop
      (𝓝 (if i = j then (1 : ℂ) else 0)) := by
    simpa only [fun n => orthonormal_iff_ite.mp (hV n) i j] using
      (tendsto_const_nhds : Tendsto
        (fun _ : ℕ => if i = j then (1 : ℂ) else 0) atTop
        (𝓝 (if i = j then (1 : ℂ) else 0)))
  exact tendsto_nhds_unique hinner hconst

/-- A member of a finite orthonormal span has its usual finite inner-product expansion. -/
theorem finite_orthonormal_sum_inner_of_mem_span {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {ι : Type*} [Fintype ι] {v : ι → E}
    (hv : Orthonormal ℂ v) {w : E} (hw : w ∈ Submodule.span ℂ (Set.range v)) :
    ∑ i, ⟪v i, w⟫ • v i = w := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hw
  simp only [hv.inner_right_fintype]

/-- Simultaneous limits of orthonormal frames and members retain span membership.
The varying spans are handled by their explicit finite orthonormal expansions. -/
theorem mem_span_of_orthonormal_limits {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {ι : Type*} [Fintype ι]
    {V : ℕ → ι → E} {v : ι → E} {W : ℕ → E} {w : E}
    (hV : ∀ n, Orthonormal ℂ (V n))
    (hVlim : ∀ i, Tendsto (fun n => V n i) atTop (𝓝 (v i)))
    (hWlim : Tendsto W atTop (𝓝 w))
    (hmem : ∀ n, W n ∈ Submodule.span ℂ (Set.range (V n))) :
    w ∈ Submodule.span ℂ (Set.range v) := by
  have hsum : Tendsto (fun n => ∑ i, ⟪V n i, W n⟫ • V n i) atTop
      (𝓝 (∑ i, ⟪v i, w⟫ • v i)) :=
    tendsto_finsetSum _ (fun i _ => ((hVlim i).inner hWlim).smul (hVlim i))
  have heq : ∀ n, (∑ i, ⟪V n i, W n⟫ • V n i) = W n :=
    fun n => finite_orthonormal_sum_inner_of_mem_span (hV n) (hmem n)
  have hlimit : (∑ i, ⟪v i, w⟫ • v i) = w := by
    apply tendsto_nhds_unique hsum
    simpa only [heq] using hWlim
  exact (Submodule.mem_span_range_iff_exists_fun ℂ).mpr ⟨fun i => ⟪v i, w⟫, hlimit⟩

/-- Orthonormal frames in a fixed finite Euclidean coefficient space have an orthonormal
subsequence limit. Independence and the exact dimension of the limiting span are explicit. -/
theorem exists_orthonormal_coefficient_frame_subseq {m d : ℕ}
    (V : ℕ → Fin m → EuclideanSpace ℂ (Fin (d + 1)))
    (hV : ∀ n, Orthonormal ℂ (V n)) :
    ∃ v : Fin m → EuclideanSpace ℂ (Fin (d + 1)),
      Orthonormal ℂ v ∧ LinearIndependent ℂ v ∧
      Module.finrank ℂ (Submodule.span ℂ (Set.range v)) = m ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ i, Tendsto (fun n => V (φ n) i) atTop (𝓝 (v i)) := by
  have hcompact : IsCompact {v : Fin m → EuclideanSpace ℂ (Fin (d + 1)) |
      ∀ i, v i ∈ Metric.closedBall 0 1} :=
    isCompact_pi_infinite fun _ => isCompact_closedBall 0 1
  have hmem : ∀ n, V n ∈ {v : Fin m → EuclideanSpace ℂ (Fin (d + 1)) |
      ∀ i, v i ∈ Metric.closedBall 0 1} := by
    intro n i
    simpa only [Metric.mem_closedBall, dist_zero_right, (hV n).norm_eq_one i] using
      (le_refl (1 : ℝ))
  obtain ⟨v, _, φ, hφ, hlim⟩ := hcompact.tendsto_subseq hmem
  have hpoint (i : Fin m) : Tendsto (fun n => V (φ n) i) atTop (𝓝 (v i)) :=
    (continuous_apply i).continuousAt.tendsto.comp hlim
  have hv := orthonormal_of_pointwise_tendsto (fun n => hV (φ n)) hpoint
  exact ⟨v, hv, hv.linearIndependent, by simpa using finrank_span_eq_card hv.linearIndependent,
    φ, hφ, hpoint⟩

/-- A normalized member can converge along the same subsequence as the frame. Its unit
norm, nonvanishing, and membership in the limiting `m`-dimensional span are retained. -/
theorem exists_orthonormal_coefficient_frame_member_subseq {m d : ℕ}
    (V : ℕ → Fin m → EuclideanSpace ℂ (Fin (d + 1)))
    (W : ℕ → EuclideanSpace ℂ (Fin (d + 1)))
    (hV : ∀ n, Orthonormal ℂ (V n)) (hW : ∀ n, ‖W n‖ = 1)
    (hmem : ∀ n, W n ∈ Submodule.span ℂ (Set.range (V n))) :
    ∃ v : Fin m → EuclideanSpace ℂ (Fin (d + 1)),
      ∃ w : EuclideanSpace ℂ (Fin (d + 1)),
      Orthonormal ℂ v ∧ LinearIndependent ℂ v ∧
      Module.finrank ℂ (Submodule.span ℂ (Set.range v)) = m ∧
      ‖w‖ = 1 ∧ w ≠ 0 ∧ w ∈ Submodule.span ℂ (Set.range v) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        (∀ i, Tendsto (fun n => V (φ n) i) atTop (𝓝 (v i))) ∧
        Tendsto (W ∘ φ) atTop (𝓝 w) := by
  obtain ⟨v, hv, hvi, hvdim, φ, hφ, hlim⟩ := exists_orthonormal_coefficient_frame_subseq V hV
  have hWin : ∀ n, W (φ n) ∈ Metric.closedBall (0 : EuclideanSpace ℂ (Fin (d + 1))) 1 := by
    intro n
    simpa only [Metric.mem_closedBall, dist_zero_right, hW (φ n)] using (le_refl (1 : ℝ))
  have hcompactW := isCompact_closedBall (0 : EuclideanSpace ℂ (Fin (d + 1))) 1
  obtain ⟨w, _, ψ, hψ, hWlim⟩ := hcompactW.tendsto_subseq hWin
  have hVlim (i : Fin m) : Tendsto (fun n => V (φ (ψ n)) i) atTop (𝓝 (v i)) :=
    (hlim i).comp hψ.tendsto_atTop
  have hw : ‖w‖ = 1 := by
    apply tendsto_nhds_unique hWlim.norm
    simpa only [Function.comp_apply, hW] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
  have hwzero : w ≠ 0 := by
    intro hw0
    rw [hw0, norm_zero] at hw
    exact zero_ne_one hw
  have hwmem : w ∈ Submodule.span ℂ (Set.range v) :=
    mem_span_of_orthonormal_limits (fun n => hV (φ (ψ n))) hVlim hWlim
      (fun n => hmem (φ (ψ n)))
  exact ⟨v, w, hv, hvi, hvdim, hw, hwzero, hwmem, φ ∘ ψ, hφ.comp hψ, hVlim, hWlim⟩

/-- Reconstruct a degree-bounded polynomial from its Euclidean coefficient vector. -/
def polynomialOfCoefficients {d : ℕ} (v : EuclideanSpace ℂ (Fin (d + 1))) : Polynomial ℂ :=
  ∑ i, Polynomial.monomial i.val (v i)

/-- The reconstruction has the specified coefficients and zero coefficients above `d`. -/
theorem polynomialOfCoefficients_coeff {d : ℕ}
    (v : EuclideanSpace ℂ (Fin (d + 1))) (k : ℕ) :
    (polynomialOfCoefficients v).coeff k =
      if h : k < d + 1 then v ⟨k, h⟩ else 0 := by
  classical
  by_cases hk : k < d + 1
  · simp only [polynomialOfCoefficients, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
      dif_pos hk]
    rw [Finset.sum_eq_single (⟨k, hk⟩ : Fin (d + 1))]
    · simp
    · intro i _ hi
      have hival : i.val ≠ k := by intro h; apply hi; exact Fin.ext h
      simp [hival]
    · simp
  · simp only [polynomialOfCoefficients, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
      dif_neg hk]
    apply Finset.sum_eq_zero
    intro i _
    have hival : i.val ≠ k := by intro h; exact hk (h ▸ i.isLt)
    simp [hival]

theorem polynomialOfCoefficients_natDegree_le {d : ℕ}
    (v : EuclideanSpace ℂ (Fin (d + 1))) : (polynomialOfCoefficients v).natDegree ≤ d := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [polynomialOfCoefficients_coeff, dif_neg (by omega)]

@[simp] theorem coefficientVector_polynomialOfCoefficients {d : ℕ}
    (v : EuclideanSpace ℂ (Fin (d + 1))) :
    coefficientVector d (polynomialOfCoefficients v) = v := by
  ext i
  change (polynomialOfCoefficients v).coeff i.val = v i
  simp [polynomialOfCoefficients_coeff, i.isLt]

@[simp] theorem polynomialOfCoefficients_coefficientVector {d : ℕ} (p : Polynomial ℂ)
    (hp : p.natDegree ≤ d) : polynomialOfCoefficients (coefficientVector d p) = p := by
  ext k
  rw [polynomialOfCoefficients_coeff]
  split_ifs with hk
  · rfl
  · exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)).symm

/-- Coefficient extraction is linear even for polynomials of degree larger than the
chosen coefficient space; reconstruction is its inverse on the bounded-degree subspace. -/
def polynomialCoefficientLinearMap (d : ℕ) :
    Polynomial ℂ →ₗ[ℂ] EuclideanSpace ℂ (Fin (d + 1)) where
  toFun := coefficientVector d
  map_add' p q := by ext i; simp [coefficientVector]
  map_smul' c p := by ext i; simp [coefficientVector]

/-- Reconstruction is a linear map from coefficient vectors to polynomials. -/
def polynomialOfCoefficientsLinearMap (d : ℕ) :
    EuclideanSpace ℂ (Fin (d + 1)) →ₗ[ℂ] Polynomial ℂ where
  toFun := polynomialOfCoefficients
  map_add' v w := by
    ext k
    by_cases hk : k < d + 1 <;> simp [polynomialOfCoefficients_coeff, hk]
  map_smul' c v := by
    ext k
    by_cases hk : k < d + 1 <;> simp [polynomialOfCoefficients_coeff, hk]

@[simp] theorem polynomialCoefficientLinearMap_apply (d : ℕ) (p : Polynomial ℂ) :
    polynomialCoefficientLinearMap d p = coefficientVector d p := rfl

@[simp] theorem polynomialOfCoefficientsLinearMap_apply (d : ℕ)
    (v : EuclideanSpace ℂ (Fin (d + 1))) :
    polynomialOfCoefficientsLinearMap d v = polynomialOfCoefficients v := rfl

/-- Convergence in the finite Euclidean coefficient space gives convergence of every
coefficient of degree-bounded polynomials, including the identically zero tail. -/
theorem polynomial_coeff_tendsto_of_coefficientVector_tendsto {d : ℕ}
    {P : ℕ → Polynomial ℂ} {v : EuclideanSpace ℂ (Fin (d + 1))}
    (hdeg : ∀ n, (P n).natDegree ≤ d)
    (hlim : Tendsto (fun n => coefficientVector d (P n)) atTop (𝓝 v)) (k : ℕ) :
    Tendsto (fun n => (P n).coeff k) atTop (𝓝 ((polynomialOfCoefficients v).coeff k)) := by
  rw [polynomialOfCoefficients_coeff]
  by_cases hk : k < d + 1
  · rw [dif_pos hk]
    exact (PiLp.continuous_apply 2 (fun _ : Fin (d + 1) => ℂ)
      (⟨k, hk⟩ : Fin (d + 1))).continuousAt.tendsto.comp hlim
  · rw [dif_neg hk]
    have hzero : ∀ n, (P n).coeff k = 0 := fun n =>
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hdeg n) (by omega))
    simpa only [hzero] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))

/-- The polynomial form of frame compactness used in Wronskian localisation. One
subsequence preserves all frame coefficients and a normalized member, with exact limiting
span dimension and a nonzero limiting member. -/
theorem exists_polynomial_frame_member_subseq {m d : ℕ}
    (P : ℕ → Fin m → Polynomial ℂ) (Q : ℕ → Polynomial ℂ)
    (hPdeg : ∀ n i, (P n i).natDegree ≤ d) (hQdeg : ∀ n, (Q n).natDegree ≤ d)
    (hP : ∀ n, Orthonormal ℂ (fun i => coefficientVector d (P n i)))
    (hQ : ∀ n, ‖coefficientVector d (Q n)‖ = 1)
    (hmem : ∀ n, Q n ∈ Submodule.span ℂ (Set.range (P n))) :
    ∃ p : Fin m → Polynomial ℂ, ∃ q : Polynomial ℂ,
      (∀ i, (p i).natDegree ≤ d) ∧ q.natDegree ≤ d ∧
      Orthonormal ℂ (fun i => coefficientVector d (p i)) ∧
      LinearIndependent ℂ p ∧ Module.finrank ℂ (Submodule.span ℂ (Set.range p)) = m ∧
      ‖coefficientVector d q‖ = 1 ∧ q ≠ 0 ∧ q ∈ Submodule.span ℂ (Set.range p) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        (∀ i k, Tendsto (fun n => (P (φ n) i).coeff k) atTop (𝓝 ((p i).coeff k))) ∧
        (∀ k, Tendsto (fun n => (Q (φ n)).coeff k) atTop (𝓝 (q.coeff k))) := by
  have hcoeffmem (n : ℕ) : coefficientVector d (Q n) ∈
      Submodule.span ℂ (Set.range (fun i => coefficientVector d (P n i))) := by
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hmem n)
    apply (Submodule.mem_span_range_iff_exists_fun ℂ).mpr
    refine ⟨c, ?_⟩
    simpa only [map_sum, map_smul, polynomialCoefficientLinearMap_apply] using
      congrArg (polynomialCoefficientLinearMap d) hc
  obtain ⟨v, w, hv, hvi, _, hw, hwzero, hwmem, φ, hφ, hVlim, hWlim⟩ :=
    exists_orthonormal_coefficient_frame_member_subseq
      (fun n i => coefficientVector d (P n i)) (fun n => coefficientVector d (Q n))
      hP hQ hcoeffmem
  let p : Fin m → Polynomial ℂ := fun i => polynomialOfCoefficients (v i)
  let q : Polynomial ℂ := polynomialOfCoefficients w
  have hpind : LinearIndependent ℂ p := by
    apply LinearIndependent.of_comp (polynomialCoefficientLinearMap d)
    change LinearIndependent ℂ (fun i => coefficientVector d (p i))
    simpa only [p, coefficientVector_polynomialOfCoefficients] using hvi
  have hqnorm : ‖coefficientVector d q‖ = 1 := by
    simpa only [q, coefficientVector_polynomialOfCoefficients] using hw
  have hqzero : q ≠ 0 := by
    intro hzero
    have hveczero : coefficientVector d (0 : Polynomial ℂ) = 0 := by
      ext i
      simp [coefficientVector]
    have hnormzero : ‖coefficientVector d q‖ = 0 := by rw [hzero, hveczero, norm_zero]
    rw [hnormzero] at hqnorm
    exact zero_ne_one hqnorm
  have hqmem : q ∈ Submodule.span ℂ (Set.range p) := by
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hwmem
    apply (Submodule.mem_span_range_iff_exists_fun ℂ).mpr
    refine ⟨c, ?_⟩
    simpa only [map_sum, map_smul, polynomialOfCoefficientsLinearMap_apply, p, q] using
      congrArg (polynomialOfCoefficientsLinearMap d) hc
  refine ⟨p, q, fun i => polynomialOfCoefficients_natDegree_le (v i),
    polynomialOfCoefficients_natDegree_le w, ?_, hpind, ?_, hqnorm, hqzero, hqmem,
    φ, hφ, ?_, ?_⟩
  · simpa only [p, coefficientVector_polynomialOfCoefficients] using hv
  · simpa using finrank_span_eq_card hpind
  · intro i k
    exact polynomial_coeff_tendsto_of_coefficientVector_tendsto
      (fun n => hPdeg (φ n) i) (hVlim i) k
  · intro k
    exact polynomial_coeff_tendsto_of_coefficientVector_tendsto
      (fun n => hQdeg (φ n)) hWlim k

end KungTraub
