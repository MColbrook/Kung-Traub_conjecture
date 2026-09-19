import KungTraub.PolynomialWronskians
import Mathlib.RingTheory.Polynomial.DegreeLT

/-!
# Degree-adapted polynomial families

The degree reduction follows the manuscript's cancellation of equal leading degrees.
The elementary column operations, finite-set ordering and dimension APIs are from mathlib.
-/

noncomputable section
namespace KungTraub
open scoped BigOperators

/-- An independent finite family admits another family with the same span and Wronskian,
pairwise distinct degrees, and no increase in any labelled degree. -/
theorem exists_polynomial_family_distinct_degrees {m : ℕ}
    (p : Fin m → Polynomial ℂ) (hp : LinearIndependent ℂ p) :
    ∃ q : Fin m → Polynomial ℂ, LinearIndependent ℂ q ∧
      Function.Injective (fun i => (q i).natDegree) ∧
      Submodule.span ℂ (Set.range q) = Submodule.span ℂ (Set.range p) ∧
      polynomialWronskian q = polynomialWronskian p ∧
      (∀ i, (q i).natDegree ≤ (p i).natDegree) := by
  classical
  generalize hn : (∑ i, (p i).natDegree) = N
  induction N using Nat.strong_induction_on generalizing p with
  | h N ih =>
    by_cases hd : Function.Injective (fun i => (p i).natDegree)
    · exact ⟨p, hp, hd, rfl, rfl, fun _ => le_rfl⟩
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
      obtain ⟨r, hr, hdr, hspanr, hwr, hboundr⟩ := ih (∑ t, (q t).natDegree) hsum q hq rfl
      have hw : polynomialWronskian q = polynomialWronskian p := by
        simpa [q, sub_eq_add_neg] using polynomialWronskian_update_add_smul p hij (-c)
      refine ⟨r, hr, hdr, hspanr.trans ?_, hwr.trans hw, ?_⟩
      · exact Submodule.span_range_update_sub_smul hij.symm p c
      · intro t
        apply (hboundr t).trans
        by_cases ht : t = i
        · subst t; exact hdropNat.le
        · simp [q, ht]


/-- Among `m` distinct natural numbers the minimum sum is `0 + ... + (m-1)`;
equality forces all numbers to be less than `m`. -/
theorem injective_nat_sum_minimum {m : ℕ} (d : Fin m → ℕ)
    (hd : Function.Injective d) :
    (∑ i : Fin m, i.val) ≤ ∑ i, d i ∧
      ((∑ i, d i) = ∑ i : Fin m, i.val → ∀ i, d i < m) := by
  classical
  let s := Finset.univ.image d
  have hcard : s.card = m := by
    simp only [s, Finset.card_image_of_injective _ hd, Finset.card_univ, Fintype.card_fin]
  let g := s.orderEmbOfFin hcard
  have hg : StrictMono g := g.strictMono
  have hsum : (∑ i, g i) = ∑ i, d i := by
    calc
      (∑ i, g i) = ∑ i : s, (i : ℕ) :=
        (s.orderIsoOfFin hcard).toEquiv.sum_comp (fun i : s => (i : ℕ))
      _ = ∑ i ∈ s, i := Finset.sum_coe_sort s (fun i : ℕ => i)
      _ = ∑ i, d i := Finset.sum_image (fun i _ j _ hij => hd hij)
  have hindex : ∀ k (hk : k < m), k ≤ g ⟨k, hk⟩ := by
    intro k
    induction k with
    | zero => intro hk; exact Nat.zero_le _
    | succ k ih =>
      intro hk
      have hprev := ih (by omega)
      have hlt := hg (show (⟨k, by omega⟩ : Fin m) < ⟨k + 1, hk⟩ from Nat.lt_succ_self k)
      omega
  have hle : ∀ i : Fin m, i.val ≤ g i := fun i => hindex i.val i.isLt
  refine ⟨hsum ▸ Finset.sum_le_sum (fun i _ => hle i), ?_⟩
  intro heq i
  have hpoint : ∀ j : Fin m, g j = j.val := by
    intro j
    by_contra hj
    have hlt : j.val < g j := lt_of_le_of_ne (hle j) (Ne.symm hj)
    have hstrict := Finset.sum_lt_sum (fun t (_ : t ∈ Finset.univ) => hle t)
      ⟨j, Finset.mem_univ _, hlt⟩
    omega
  have hdi : d i ∈ s := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  obtain ⟨j, hj⟩ := (s.orderIsoOfFin hcard).surjective ⟨d i, hdi⟩
  have hgj : g j = d i := congrArg Subtype.val hj
  rw [← hgj, hpoint]
  exact j.isLt

/-- The sharp upper bound for the degree of a nonempty polynomial Wronskian. -/
theorem polynomialWronskian_natDegree_le {m D : ℕ} (hm : 0 < m) (hmD : m ≤ D + 1)
    (p : Fin m → Polynomial ℂ) (hp : LinearIndependent ℂ p)
    (hD : ∀ i, (p i).natDegree ≤ D) :
    (polynomialWronskian p).natDegree ≤ m * (D + 1 - m) := by
  obtain ⟨q, hq, hd, _, hw, hbound⟩ := exists_polynomial_family_distinct_degrees p hp
  have hqD : ∀ i, (q i).natDegree ≤ D := fun i => (hbound i).trans (hD i)
  have hcomp : Function.Injective (fun i => D - (q i).natDegree) := by
    intro i j hij
    apply hd
    change D - (q i).natDegree = D - (q j).natDegree at hij
    change (q i).natDegree = (q j).natDegree
    have := hqD i
    have := hqD j
    omega
  have hmin := (injective_nat_sum_minimum _ hcomp).1
  have hsum : (∑ i, (q i).natDegree) + (∑ i, (D - (q i).natDegree)) = m * D := by
    rw [← Finset.sum_add_distrib]
    simp only [Nat.add_sub_of_le (hqD _), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
  have hdegree := polynomialWronskian_natDegree_add q (fun i => hq.ne_zero i) hd
  rw [hw] at hdegree
  have hdouble : (∑ i : Fin m, i.val) * 2 = m * (m - 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun k => k)]
    exact Finset.sum_range_id_mul_two m
  have hsub : D + 1 - m + m = D + 1 := Nat.sub_add_cancel hmD
  have hmone : m - 1 + 1 = m := Nat.sub_add_cancel hm
  nlinarith

/-- A constant Wronskian characterizes the full space of polynomials of degree less than `m`. -/
theorem polynomialWronskian_natDegree_eq_zero_iff_span {m : ℕ}
    (p : Fin m → Polynomial ℂ) (hp : LinearIndependent ℂ p) :
    (polynomialWronskian p).natDegree = 0 ↔
      Submodule.span ℂ (Set.range p) = Polynomial.degreeLT ℂ m := by
  classical
  obtain ⟨q, hq, hd, hspan, hw, _⟩ := exists_polynomial_family_distinct_degrees p hp
  have hdegree := polynomialWronskian_natDegree_add q (fun i => hq.ne_zero i) hd
  constructor
  · intro hz
    rw [hw, hz, zero_add] at hdegree
    have hlt := (injective_nat_sum_minimum _ hd).2 hdegree.symm
    have hle : Submodule.span ℂ (Set.range q) ≤ Polynomial.degreeLT ℂ m := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      apply Polynomial.mem_degreeLT.mpr
      rw [Polynomial.degree_eq_natDegree (hq.ne_zero i)]
      exact WithBot.coe_lt_coe.mpr (hlt i)
    rw [← hspan]
    apply Submodule.eq_of_le_of_finrank_eq hle
    rw [Module.finrank_eq_card_basis (Module.Basis.span hq),
      Module.finrank_eq_card_basis (Polynomial.degreeLT.basis ℂ m)]
  · intro hspace
    have hlt : ∀ i, (q i).natDegree < m := by
      intro i
      have hmem : q i ∈ Polynomial.degreeLT ℂ m := by
        rw [← hspace, ← hspan]
        exact Submodule.subset_span (Set.mem_range_self i)
      have hh := Polynomial.mem_degreeLT.mp hmem
      rw [Polynomial.degree_eq_natDegree (hq.ne_zero i)] at hh
      exact WithBot.coe_lt_coe.mp hh
    let e : Fin m ≃ Fin m := Equiv.ofBijective (fun i => ⟨(q i).natDegree, hlt i⟩)
      ((Finite.injective_iff_bijective).mp (fun i j hij => hd (congrArg Fin.val hij)))
    have hsum : (∑ i, (q i).natDegree) = ∑ i : Fin m, i.val :=
      e.sum_comp (fun i : Fin m => i.val)
    rw [hw, hsum] at hdegree
    omega

/-- The constant Wronskian in the characterization is nonzero. -/
theorem polynomialWronskian_eq_nonzero_constant_iff_span {m : ℕ}
    (p : Fin m → Polynomial ℂ) (hp : LinearIndependent ℂ p) :
    (∃ c : ℂ, c ≠ 0 ∧ polynomialWronskian p = Polynomial.C c) ↔
      Submodule.span ℂ (Set.range p) = Polynomial.degreeLT ℂ m := by
  rw [← polynomialWronskian_natDegree_eq_zero_iff_span p hp]
  constructor
  · rintro ⟨c, _, hc⟩
    rw [hc, Polynomial.natDegree_C]
  · intro hz
    refine ⟨(polynomialWronskian p).coeff 0, ?_, Polynomial.eq_C_of_natDegree_eq_zero hz⟩
    intro hc
    have hh := Polynomial.eq_C_of_natDegree_eq_zero hz
    rw [hc, Polynomial.C_0] at hh
    exact polynomialWronskian_ne_zero_of_linearIndependent p hp hh

/-- A basis can be chosen with pairwise distinct polynomial degrees. -/
theorem exists_polynomial_basis_distinct_degrees {m : ℕ}
    (V : Submodule ℂ (Polynomial ℂ)) (b : Module.Basis (Fin m) ℂ V) :
    ∃ b' : Module.Basis (Fin m) ℂ V,
      Function.Injective (fun i => (b' i : Polynomial ℂ).natDegree) := by
  classical
  let p : Fin m → Polynomial ℂ := fun i => b i
  have hp : LinearIndependent ℂ p := b.linearIndependent.map' V.subtype (by simp)
  obtain ⟨q, hq, hd, hspan, _, _⟩ := exists_polynomial_family_distinct_degrees p hp
  have hspanp : Submodule.span ℂ (Set.range p) = V := by
    change Submodule.span ℂ (Set.range (V.subtype ∘ b)) = V
    rw [Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  let b' := (Module.Basis.span hq).map (LinearEquiv.ofEq _ V (hspan.trans hspanp))
  refine ⟨b', ?_⟩
  have hval : ∀ i, (b' i : Polynomial ℂ) = q i := by
    intro i
    simp [b']
  simpa only [hval] using hd

/-- Outside the full space of degree less than `m`, an independent family's Wronskian has a root. -/
theorem polynomialWronskian_has_root_iff_span_ne_degreeLT {m : ℕ}
    (p : Fin m → Polynomial ℂ) (hp : LinearIndependent ℂ p) :
    (∃ a : ℂ, (polynomialWronskian p).eval a = 0) ↔
      Submodule.span ℂ (Set.range p) ≠ Polynomial.degreeLT ℂ m := by
  constructor
  · rintro ⟨a, ha⟩ hspace
    obtain ⟨c, hc, heq⟩ := (polynomialWronskian_eq_nonzero_constant_iff_span p hp).mpr hspace
    rw [heq, Polynomial.eval_C] at ha
    exact hc ha
  · intro hspace
    apply IsAlgClosed.exists_root
    intro hz
    apply hspace
    apply (polynomialWronskian_natDegree_eq_zero_iff_span p hp).mp
    exact Polynomial.natDegree_eq_zero_iff_degree_le_zero.mpr hz.le

end KungTraub

