import KungTraubAppendices.ComplexAffineOracle
import KungTraub.EntireLimit

/-! Exact adaptive complex transcripts at a locally uniform entire limit. -/

noncomputable section
open Filter
namespace KungTraubAppendices

/-- Agreement at the queries selected by one execution preserves every
prefix of that execution, without continuity assumptions on the rules. -/
theorem ComplexAlgorithm.prefix_eq_of_actual_answers {n : ℕ} (A : ComplexAlgorithm n)
    {f g : ℂ → ℂ} {x : ℂ}
    (hanswers : ∀ j : Fin n, (A.actualQuery f x j).answer g = (A.actualQuery f x j).answer f)
    (k : ℕ) (hk : k ≤ n) : A.prefix g x k hk = A.prefix f x k hk := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hkn : k < n := by omega
    have hp := ih hkn.le
    simp only [ComplexAlgorithm.prefix]
    rw [hp]
    exact Fin.snoc_inj.mpr ⟨rfl, hanswers ⟨k, hkn⟩⟩

/-- Exact query agreement gives the identical final complex output. -/
theorem ComplexAlgorithm.run_eq_of_actual_answers {n : ℕ} (A : ComplexAlgorithm n)
    {f g : ℂ → ℂ} {x : ℂ}
    (hanswers : ∀ j : Fin n, (A.actualQuery f x j).answer g = (A.actualQuery f x j).answer f) :
    A.run g x = A.run f x :=
  congrArg (A.output x) (A.prefix_eq_of_actual_answers hanswers n le_rfl)

/-- Locally uniform limits preserve an entire execution when each of its
saved derivative observations is eventually exact. Derivative orders and
locations remain unrestricted complex queries. -/
theorem ComplexAlgorithm.run_eq_entire_limit {n : ℕ} (A : ComplexAlgorithm n)
    {F : ℕ → ℂ → ℂ} {f g : ℂ → ℂ} {x : ℂ}
    (hF : ∀ k, Differentiable ℂ (F k))
    (hlim : TendstoLocallyUniformly F g atTop)
    (hanswers : ∀ j : Fin n, ∀ᶠ k in atTop,
      (A.actualQuery f x j).answer (F k) = (A.actualQuery f x j).answer f) :
    A.run g x = A.run f x := by
  apply A.run_eq_of_actual_answers
  intro j
  have hj := hanswers j
  cases hq : A.actualQuery f x j with
  | idle => rfl
  | derivative z nu =>
    simp only [hq, ComplexQuery.answer] at hj ⊢
    exact KungTraub.iteratedDeriv_limit_eq_of_eventually_eq hF hlim nu z
      (iteratedDeriv nu f z) hj

end KungTraubAppendices
