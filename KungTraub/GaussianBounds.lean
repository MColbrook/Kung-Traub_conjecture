import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Analytic
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Tactic

/-!
# Gaussian times polynomial corrections

Bounds for the correction functions in Section 4 of Matthew J. Colbrook's
*Adversarial Wronskians: A proof of the Kung–Traub conjecture*.

The Gaussian decay theorem is due to David Loeffler in mathlib's Gaussian Poisson
summation module. Boundedness of continuous functions vanishing at infinity uses
Jireh Loreaux's `ZeroAtInftyContinuousMap.isBounded_range`. The derivative formula
uses the polynomial differentiation API of Sébastien Gouëzel and Eric Wieser; jet
vanishing uses Michail Karatarakis's `iteratedDeriv_mul_pow_sub_of_analytic`.
The remaining algebra, shift estimates and uniform scaling assemble those results
for the manuscript's precise domains.
-/

noncomputable section

open Filter Topology

namespace KungTraub

def gaussianPolynomial (p : Polynomial ℝ) (t : ℝ) : ℝ :=
  Real.exp (-(t ^ 2)) * p.eval t

def complexGaussianPolynomial (p : Polynomial ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-(z ^ 2)) * (p.map Complex.ofRealHom).eval z

/-- Every Gaussian times a real polynomial tends to zero at both ends of the real line. -/
theorem gaussianPolynomial_tendsto_zero (p : Polynomial ℝ) :
    Tendsto (gaussianPolynomial p) (cocompact ℝ) (𝓝 0) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    change Tendsto (fun t => Real.exp (-(t ^ 2)) * (p + q).eval t) _ _
    simpa only [gaussianPolynomial, Polynomial.eval_add, mul_add, add_zero] using hp.add hq
  | monomial n a =>
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have h := (tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact (by norm_num : (0 : ℝ) < 1)
      (n : ℝ)).const_mul |a|
    simpa [gaussianPolynomial, Polynomial.eval_monomial, norm_mul, Real.norm_eq_abs,
      abs_pow, Real.rpow_natCast, mul_assoc, mul_comm, mul_left_comm] using h

/-- Gaussian times polynomial is continuously defined on the full real line. -/
theorem gaussianPolynomial_continuous (p : Polynomial ℝ) :
    Continuous (gaussianPolynomial p) := by
  unfold gaussianPolynomial
  fun_prop

/-- There is a positive global bound; no bounded real domain is imposed. -/
theorem gaussianPolynomial_exists_bound (p : Polynomial ℝ) :
    ∃ C > 0, ∀ t : ℝ, |gaussianPolynomial p t| ≤ C := by
  let f : ZeroAtInftyContinuousMap ℝ ℝ :=
    { toFun := gaussianPolynomial p
      continuous_toFun := gaussianPolynomial_continuous p
      zero_at_infty' := gaussianPolynomial_tendsto_zero p }
  obtain ⟨C, hC, hbound⟩ := f.isBounded_range.exists_pos_norm_le
  exact ⟨C, hC, fun t => by simpa [f, Real.norm_eq_abs] using hbound (f t) ⟨t, rfl⟩⟩

/-- Differentiation preserves the Gaussian times polynomial form. -/
theorem gaussianPolynomial_hasDerivAt (p : Polynomial ℝ) (t : ℝ) :
    HasDerivAt (gaussianPolynomial p)
      (gaussianPolynomial (p.derivative - Polynomial.C 2 * Polynomial.X * p) t) t := by
  have h := (((hasDerivAt_id t).pow 2).neg.exp).mul (p.hasDerivAt t)
  apply h.congr_deriv
  simp [gaussianPolynomial, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]
  ring

/-- The first derivative also vanishes at both ends of the real line. -/
theorem gaussianPolynomial_deriv_tendsto_zero (p : Polynomial ℝ) :
    Tendsto (deriv (gaussianPolynomial p)) (cocompact ℝ) (𝓝 0) := by
  have heq : deriv (gaussianPolynomial p) =
      gaussianPolynomial (p.derivative - Polynomial.C 2 * Polynomial.X * p) :=
    funext fun t => (gaussianPolynomial_hasDerivAt p t).deriv
  rw [heq]
  exact gaussianPolynomial_tendsto_zero _

/-- One positive constant bounds the sum of the function and its derivative globally. -/
theorem gaussianPolynomial_exists_C1_bound (p : Polynomial ℝ) :
    ∃ C > 0, ∀ t : ℝ, |gaussianPolynomial p t| + |deriv (gaussianPolynomial p) t| ≤ C := by
  obtain ⟨C, hC, hf⟩ := gaussianPolynomial_exists_bound p
  obtain ⟨D, hD, hd⟩ :=
    gaussianPolynomial_exists_bound (p.derivative - Polynomial.C 2 * Polynomial.X * p)
  refine ⟨C + D, add_pos hC hD, fun t => ?_⟩
  rw [(gaussianPolynomial_hasDerivAt p t).deriv]
  exact add_le_add (hf t) (hd t)

/-- The complex extension is entire. -/
theorem complexGaussianPolynomial_differentiable (p : Polynomial ℝ) :
    Differentiable ℂ (complexGaussianPolynomial p) := by
  unfold complexGaussianPolynomial
  fun_prop

/-- Every fixed closed complex disc admits a finite positive bound. -/
theorem complexGaussianPolynomial_exists_disc_bound (p : Polynomial ℝ) (R : ℝ) :
    ∃ C > 0, ∀ z : ℂ, ‖z‖ ≤ R → ‖complexGaussianPolynomial p z‖ ≤ C := by
  have hc := (complexGaussianPolynomial_differentiable p).continuous
  obtain ⟨C, hC, hb⟩ :=
    ((isCompact_closedBall (0 : ℂ) R).image hc).isBounded.exists_pos_norm_le
  refine ⟨C, hC, fun z hz => hb _ ?_⟩
  exact ⟨z, by simpa using hz, rfl⟩

/-- The entire extension agrees with the real function on the real axis. -/
theorem complexGaussianPolynomial_ofReal (p : Polynomial ℝ) (t : ℝ) :
    complexGaussianPolynomial p (t : ℂ) = (gaussianPolynomial p t : ℂ) := by
  simp only [complexGaussianPolynomial, gaussianPolynomial, Complex.ofReal_mul,
    Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_pow, Polynomial.eval_map]
  congr 1
  exact p.eval₂_at_apply Complex.ofRealHom t

/-- A prescribed linear factor of multiplicity `k + 1` annihilates the `k`th observation. -/
theorem gaussianPolynomial_iteratedDeriv_eq_zero {p : Polynomial ℝ} {a : ℝ} {k : ℕ}
    (hdiv : (Polynomial.X - Polynomial.C a) ^ (k + 1) ∣ p) :
    iteratedDeriv k (gaussianPolynomial p) a = 0 := by
  obtain ⟨q, rfl⟩ := hdiv
  have ha : ∀ t, AnalyticAt ℝ (gaussianPolynomial q) t := by
    intro t
    have hq : AnalyticAt ℝ (fun y => q.eval y) t := by
      induction q using Polynomial.induction_on' with
      | add p q hp hq => simpa only [Polynomial.eval_add] using hp.fun_add hq
      | monomial n a => simp only [Polynomial.eval_monomial]; fun_prop
    exact (show AnalyticAt ℝ (fun y => Real.exp (-(y ^ 2))) t by fun_prop).mul hq
  obtain ⟨r, _, hr⟩ := iteratedDeriv_mul_pow_sub_of_analytic (k := k) (t := 1)
    (z₀ := a) ha (R := gaussianPolynomial ((Polynomial.X - Polynomial.C a) ^ (k + 1) * q))
    (by intro t; simp [gaussianPolynomial]; ring)
  simpa using hr a

/-- A positive scalar reduces all three relevant bounds simultaneously. The two real
arguments are independent, as required for a sum of separate supremum bounds. -/
theorem gaussianPolynomial_exists_small_scaling (p : Polynomial ℝ) (R : ℝ)
    {b : ℝ} (hb : 0 < b) :
    ∃ lam > 0, ∀ t v : ℝ, ∀ z : ℂ, ‖z‖ ≤ R →
      |lam * gaussianPolynomial p t| +
        |deriv (fun y => lam * gaussianPolynomial p y) v| +
        ‖(lam : ℂ) * complexGaussianPolynomial p z‖ ≤ b := by
  obtain ⟨C, hC, hf⟩ := gaussianPolynomial_exists_bound p
  obtain ⟨D, hD, hd⟩ :=
    gaussianPolynomial_exists_bound (p.derivative - Polynomial.C 2 * Polynomial.X * p)
  obtain ⟨E, hE, he⟩ := complexGaussianPolynomial_exists_disc_bound p R
  let lam := b / (C + D + E)
  have htotal : 0 < C + D + E := by positivity
  have hlam : 0 < lam := div_pos hb htotal
  refine ⟨lam, hlam, fun t v z hz => ?_⟩
  rw [((gaussianPolynomial_hasDerivAt p v).const_mul lam).deriv,
    abs_mul, abs_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam]
  calc
    lam * |gaussianPolynomial p t| +
        lam * |gaussianPolynomial (p.derivative - Polynomial.C 2 * Polynomial.X * p) v| +
        lam * ‖complexGaussianPolynomial p z‖ ≤ lam * C + lam * D + lam * E :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left (hf t) hlam.le)
        (mul_le_mul_of_nonneg_left (hd v) hlam.le))
        (mul_le_mul_of_nonneg_left (he z hz) hlam.le)
    _ = b := by dsimp [lam]; field_simp

/-- The three estimates attached to one polynomial, with independent real arguments. -/
def GaussianBound (p : Polynomial ℝ) (R C : ℝ) : Prop :=
  (∀ t : ℝ, |gaussianPolynomial p t| ≤ C) ∧
  (∀ t : ℝ, |deriv (gaussianPolynomial p) t| ≤ C) ∧
  (∀ z : ℂ, ‖z‖ ≤ R → ‖complexGaussianPolynomial p z‖ ≤ C)

theorem gaussianPolynomial_exists_common_bound (p : Polynomial ℝ) (R : ℝ) :
    ∃ C > 0, GaussianBound p R C := by
  obtain ⟨C, hC, hf⟩ := gaussianPolynomial_exists_C1_bound p
  obtain ⟨D, hD, hd⟩ := complexGaussianPolynomial_exists_disc_bound p R
  refine ⟨C + D, add_pos hC hD, ?_, ?_, ?_⟩
  · intro t
    have := hf t
    have := abs_nonneg (deriv (gaussianPolynomial p) t)
    linarith
  · intro t
    have := hf t
    have := abs_nonneg (gaussianPolynomial p t)
    linarith
  · intro z hz
    exact (hd z hz).trans (by linarith)

theorem gaussianBound_add {p q : Polynomial ℝ} {R C D : ℝ}
    (hp : GaussianBound p R C) (hq : GaussianBound q R D) :
    GaussianBound (p + q) R (C + D) := by
  have hf : gaussianPolynomial (p + q) = fun t => gaussianPolynomial p t + gaussianPolynomial q t := by
    ext t
    simp [gaussianPolynomial, mul_add]
  have hc : complexGaussianPolynomial (p + q) =
      fun z => complexGaussianPolynomial p z + complexGaussianPolynomial q z := by
    ext z
    simp [complexGaussianPolynomial, mul_add]
  refine ⟨fun t => ?_, fun t => ?_, fun z hz => ?_⟩
  · rw [hf]
    exact (abs_add_le _ _).trans (add_le_add (hp.1 t) (hq.1 t))
  · rw [hf, ((gaussianPolynomial_hasDerivAt p t).fun_add (gaussianPolynomial_hasDerivAt q t)).deriv]
    have hp' := hp.2.1 t
    have hq' := hq.2.1 t
    rw [(gaussianPolynomial_hasDerivAt p t).deriv] at hp'
    rw [(gaussianPolynomial_hasDerivAt q t).deriv] at hq'
    exact (abs_add_le _ _).trans (add_le_add hp' hq')
  · rw [hc]
    exact (norm_add_le _ _).trans (add_le_add (hp.2.2 z hz) (hq.2.2 z hz))

theorem gaussianBound_C_mul {p : Polynomial ℝ} {R C a : ℝ}
    (hp : GaussianBound p R C) (ha : |a| ≤ 1) :
    GaussianBound (Polynomial.C a * p) R C := by
  have hf : gaussianPolynomial (Polynomial.C a * p) = fun t => a * gaussianPolynomial p t := by
    ext t
    simp [gaussianPolynomial]
    ring
  have hc : complexGaussianPolynomial (Polynomial.C a * p) =
      fun z => (a : ℂ) * complexGaussianPolynomial p z := by
    ext z
    simp [complexGaussianPolynomial]
    ring
  have hC : 0 ≤ C := (abs_nonneg _).trans (hp.1 0)
  refine ⟨fun t => ?_, fun t => ?_, fun z hz => ?_⟩
  · rw [hf, abs_mul]
    exact (mul_le_mul ha (hp.1 t) (abs_nonneg _) zero_le_one).trans_eq (one_mul C)
  · rw [hf, ((gaussianPolynomial_hasDerivAt p t).const_mul a).deriv, abs_mul]
    have hp' := hp.2.1 t
    rw [(gaussianPolynomial_hasDerivAt p t).deriv] at hp'
    exact (mul_le_mul ha hp' (abs_nonneg _) zero_le_one).trans_eq (one_mul C)
  · rw [hc, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (mul_le_mul ha (hp.2.2 z hz) (norm_nonneg _) zero_le_one).trans_eq (one_mul C)

/-- Shifting a bounded-degree polynomial factor through every centre in `[-1,1]`
admits one bound on the whole real line and the chosen complex disc. -/
theorem gaussianPolynomial_exists_shift_bound (p : Polynomial ℝ) (R : ℝ) (k : ℕ) :
    ∃ C > 0, ∀ x : ℝ, |x| ≤ 1 →
      GaussianBound (p * (Polynomial.X - Polynomial.C x) ^ k) R C := by
  induction k generalizing p with
  | zero =>
    obtain ⟨C, hC, hp⟩ := gaussianPolynomial_exists_common_bound p R
    exact ⟨C, hC, fun _ _ => by simpa using hp⟩
  | succ k ih =>
    obtain ⟨C, hC, hfirst⟩ := ih (Polynomial.X * p)
    obtain ⟨D, hD, hsecond⟩ := ih p
    refine ⟨C + D, add_pos hC hD, fun x hx => ?_⟩
    have h := gaussianBound_add (hfirst x hx)
      (gaussianBound_C_mul (hsecond x hx) (by simpa using hx : |(-x)| ≤ 1))
    have heq : Polynomial.X * p * (Polynomial.X - Polynomial.C x) ^ k +
        Polynomial.C (-x) * (p * (Polynomial.X - Polynomial.C x) ^ k) =
        p * (Polynomial.X - Polynomial.C x) ^ (k + 1) := by
      rw [Polynomial.C_neg, pow_succ]
      ring
    rwa [heq] at h

theorem gaussianBound_sum {ι : Type*} (s : Finset ι) (p : ι → Polynomial ℝ)
    (C : ι → ℝ) (R : ℝ) (h : ∀ i ∈ s, GaussianBound (p i) R (C i)) :
    GaussianBound (∑ i ∈ s, p i) R (∑ i ∈ s, C i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    refine ⟨?_, ?_, ?_⟩
    · simp [gaussianPolynomial]
    · intro t
      rw [(gaussianPolynomial_hasDerivAt 0 t).deriv]
      simp [gaussianPolynomial]
    · simp [complexGaussianPolynomial]
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using
      gaussianBound_add (h i (Finset.mem_insert_self i s))
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

/-- The polynomial part of the manuscript's real correction, before the common scalar.
Only the coefficient `u 0` is multiplied by the scale `ε`. -/
def gaussianCorrectionPolynomial (p : Polynomial ℝ) (n : ℕ) (ε x : ℝ)
    (u : Fin (n + 1) → ℝ) : Polynomial ℝ :=
  ∑ i : Fin (n + 1), Polynomial.C (if i = 0 then ε * u i else u i) *
    (p * (Polynomial.X - Polynomial.C x) ^ i.val)

/-- Evaluation gives exactly the correction family used in Section 4. -/
theorem gaussianCorrectionPolynomial_eval (p : Polynomial ℝ) (n : ℕ) (ε x : ℝ)
    (u : Fin (n + 1) → ℝ) (t : ℝ) :
    gaussianPolynomial (gaussianCorrectionPolynomial p n ε x u) t =
      Real.exp (-(t ^ 2)) * p.eval t *
        (ε * u 0 + ∑ i : Fin n, u i.succ * (t - x) ^ (i.val + 1)) := by
  simp only [gaussianPolynomial, gaussianCorrectionPolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_X, Fin.sum_univ_succ, ↓reduceIte, pow_zero, mul_one, Fin.succ_ne_zero,
    Fin.val_succ, Fin.val_zero]
  simp only [mul_add, Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro i _
    ring

/-- The coefficient box contains the Euclidean unit ball and gives one bound for all
scales and all starting points in the manuscript's specified intervals. -/
theorem gaussianCorrectionPolynomial_exists_uniform_bound (p : Polynomial ℝ) (n : ℕ)
    (R : ℝ) :
    ∃ C > 0, ∀ ε x : ℝ, 0 ≤ ε → ε ≤ 1 → |x| ≤ 1 →
      ∀ u : Fin (n + 1) → ℝ, (∀ i, |u i| ≤ 1) →
        GaussianBound (gaussianCorrectionPolynomial p n ε x u) R C := by
  classical
  choose C hC hbound using fun i : Fin (n + 1) =>
    gaussianPolynomial_exists_shift_bound p R i.val
  have hsum : 0 < ∑ i, C i := Finset.sum_pos (fun i _ => hC i) Finset.univ_nonempty
  refine ⟨∑ i, C i, hsum, fun ε x hε0 hε1 hx u hu => ?_⟩
  apply gaussianBound_sum
  intro i _
  apply gaussianBound_C_mul (hbound i x hx)
  split_ifs
  · rw [abs_mul, abs_of_nonneg hε0]
    exact (mul_le_mul hε1 (hu i) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
  · exact hu i

/-- The common bound implies a bound after multiplying by any nonnegative scalar. -/
theorem gaussianBound_scaled_estimate {p : Polynomial ℝ} {R C lam : ℝ}
    (hp : GaussianBound p R C) (hlam : 0 ≤ lam)
    (t v : ℝ) (z : ℂ) (hz : ‖z‖ ≤ R) :
    |lam * gaussianPolynomial p t| +
      |deriv (fun y => lam * gaussianPolynomial p y) v| +
      ‖(lam : ℂ) * complexGaussianPolynomial p z‖ ≤ 3 * lam * C := by
  rw [((gaussianPolynomial_hasDerivAt p v).const_mul lam).deriv,
    abs_mul, abs_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlam]
  have hd := hp.2.1 v
  rw [(gaussianPolynomial_hasDerivAt p v).deriv] at hd
  have h := add_le_add (add_le_add (mul_le_mul_of_nonneg_left (hp.1 t) hlam)
    (mul_le_mul_of_nonneg_left hd hlam))
    (mul_le_mul_of_nonneg_left (hp.2.2 z hz) hlam)
  exact h.trans_eq (by ring)

/-- One positive multiplier works for every scale, centre and Euclidean unit coefficient
vector. The real line is unrestricted and the complex-disc radius is arbitrary. -/
theorem gaussianCorrectionPolynomial_exists_small_scaling (p : Polynomial ℝ) (n : ℕ)
    (R : ℝ) {b : ℝ} (hb : 0 < b) :
    ∃ lam > 0, ∀ ε x : ℝ, 0 ≤ ε → ε ≤ 1 → |x| ≤ 1 →
      ∀ u : EuclideanSpace ℝ (Fin (n + 1)), ‖u‖ ≤ 1 →
        ∀ t v : ℝ, ∀ z : ℂ, ‖z‖ ≤ R →
          |lam * gaussianPolynomial (gaussianCorrectionPolynomial p n ε x u) t| +
          |deriv (fun y => lam * gaussianPolynomial
            (gaussianCorrectionPolynomial p n ε x u) y) v| +
          ‖(lam : ℂ) * complexGaussianPolynomial
            (gaussianCorrectionPolynomial p n ε x u) z‖ ≤ b := by
  obtain ⟨C, hC, hbound⟩ := gaussianCorrectionPolynomial_exists_uniform_bound p n R
  let lam := b / (3 * C)
  have hlam : 0 < lam := div_pos hb (by positivity)
  refine ⟨lam, hlam, fun ε x hε0 hε1 hx u hu t v z hz => ?_⟩
  have hcoeff : ∀ i, |u i| ≤ 1 := by
    intro i
    have hh : |u i| ≤ ‖u‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le u i
    exact hh.trans hu
  have h := gaussianBound_scaled_estimate (hbound ε x hε0 hε1 hx u hcoeff) hlam.le t v z hz
  have heq : 3 * lam * C = b := by
    dsimp [lam]
    field_simp
  simpa only [heq] using h

/-- The Gaussian introduces no additional real zero. -/
theorem gaussianPolynomial_ne_zero {p : Polynomial ℝ} {t : ℝ} (hp : p.eval t ≠ 0) :
    gaussianPolynomial p t ≠ 0 :=
  mul_ne_zero (Real.exp_ne_zero _) hp

/-- Every correction retains the polynomial factor prescribing earlier observations. -/
theorem gaussianCorrectionPolynomial_dvd (p : Polynomial ℝ) (n : ℕ) (ε x : ℝ)
    (u : Fin (n + 1) → ℝ) : p ∣ gaussianCorrectionPolynomial p n ε x u := by
  classical
  refine ⟨∑ i : Fin (n + 1), Polynomial.C (if i = 0 then ε * u i else u i) *
    (Polynomial.X - Polynomial.C x) ^ i.val, ?_⟩
  simp only [gaussianCorrectionPolynomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- All requested orders up to the prescribed multiplicity vanish, for every choice
of the correction parameters and every real scalar. -/
theorem gaussianCorrectionPolynomial_iteratedDeriv_eq_zero {p : Polynomial ℝ}
    {a : ℝ} {m k : ℕ} (hdiv : (Polynomial.X - Polynomial.C a) ^ (m + 1) ∣ p)
    (hk : k ≤ m) (n : ℕ) (ε x lam : ℝ) (u : Fin (n + 1) → ℝ) :
    iteratedDeriv k (fun t => lam * gaussianPolynomial
      (gaussianCorrectionPolynomial p n ε x u) t) a = 0 := by
  have hf : gaussianPolynomial (Polynomial.C lam * gaussianCorrectionPolynomial p n ε x u) =
      fun t => lam * gaussianPolynomial (gaussianCorrectionPolynomial p n ε x u) t := by
    ext t
    simp [gaussianPolynomial]
    ring
  rw [← hf]
  apply gaussianPolynomial_iteratedDeriv_eq_zero
  exact ((pow_dvd_pow _ (Nat.add_le_add_right hk 1)).trans hdiv).trans
    ((gaussianCorrectionPolynomial_dvd p n ε x u).trans (dvd_mul_left _ _))

end KungTraub
