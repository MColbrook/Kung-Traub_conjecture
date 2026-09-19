import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Entire limits and preservation of derivative observations

The limiting argument in Matthew J. Colbrook's *Adversarial Wronskians: A proof of the Kung–Traub conjecture*,
Section 4, uses summable corrections whose bounds hold eventually on each fixed complex
disc. This file supplies the analytic passages from those bounds to an entire limit,
and from eventual equality of derivative data to exact equality at the limit.

The analytic input is Mathlib's `tendstoUniformlyOn_tsum_nat_eventually` and
`TendstoLocallyUniformlyOn.deriv`, by Vincent Beffara and other Mathlib contributors.
The restriction to the real line uses `HasDerivAt.real_of_complex`, by Sébastien Gouëzel
and Yourong Zang.
-/

noncomputable section

open Filter Set Metric
open scoped BigOperators Topology

namespace KungTraub

/-- Summable bounds which hold eventually on every fixed disc imply locally uniform
convergence of the partial sums. No bound is required on the finitely many initial terms
excluded by the eventual condition for that disc. -/
theorem tendstoLocallyUniformly_sum_of_disc_bounds
    {g : ℕ → ℂ → ℂ} {b : ℕ → ℝ} (hb : Summable b)
    (hbound : ∀ R : ℝ, 0 < R → ∀ᶠ n in atTop,
      ∀ z : ℂ, ‖z‖ ≤ R → ‖g n z‖ ≤ b n) :
    TendstoLocallyUniformly
      (fun N z => ∑ n ∈ Finset.range N, g n z) (fun z => ∑' n, g n z) atTop := by
  apply tendstoLocallyUniformly_of_forall_exists_nhds
  intro z
  refine ⟨ball 0 (‖z‖ + 1), isOpen_ball.mem_nhds ?_, ?_⟩
  · simpa only [mem_ball, dist_zero_right] using lt_add_one ‖z‖
  · apply tendstoUniformlyOn_tsum_nat_eventually hb
    filter_upwards [hbound (‖z‖ + 1)
      (add_pos_of_nonneg_of_pos (norm_nonneg z) zero_lt_one)] with n hn
    intro w hw
    exact hn w (le_of_lt (by simpa only [mem_ball, dist_zero_right] using hw))

/-- A series of entire corrections with summable eventual bounds on every fixed disc
has an entire sum. The eventual bound may start at a different index for each disc. -/
theorem differentiable_tsum_of_disc_bounds
    {g : ℕ → ℂ → ℂ} {b : ℕ → ℝ} (hg : ∀ n, Differentiable ℂ (g n))
    (hb : Summable b)
    (hbound : ∀ R : ℝ, 0 < R → ∀ᶠ n in atTop,
      ∀ z : ℂ, ‖z‖ ≤ R → ‖g n z‖ ≤ b n) :
    Differentiable ℂ (fun z => ∑' n, g n z) := by
  have hlim := tendstoLocallyUniformly_sum_of_disc_bounds hb hbound
  apply differentiableOn_univ.mp
  apply hlim.tendstoLocallyUniformlyOn.differentiableOn ?_ isOpen_univ
  exact Eventually.of_forall fun N =>
    DifferentiableOn.fun_sum fun n _ => (hg n).differentiableOn

/-- Every fixed complex derivative order respects locally uniform convergence of entire
functions. There is no uniform upper bound on the derivative order in this statement. -/
theorem tendstoLocallyUniformly_iteratedDeriv
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ n, Differentiable ℂ (F n))
    (hlim : TendstoLocallyUniformly F f atTop) (k : ℕ) :
    TendstoLocallyUniformly (fun n => iteratedDeriv k (F n)) (iteratedDeriv k f) atTop := by
  induction k with
  | zero => simpa only [iteratedDeriv_zero] using hlim
  | succ k ih =>
    have hdiff : ∀ n, Differentiable ℂ (iteratedDeriv k (F n)) := fun n =>
      (hF n).contDiff.differentiable_iteratedDeriv' k
    have hderiv := ih.tendstoLocallyUniformlyOn.deriv
      (Eventually.of_forall fun n => (hdiff n).differentiableOn) isOpen_univ
    simpa only [iteratedDeriv_succ, Function.comp_def] using
      tendstoLocallyUniformlyOn_univ.mp hderiv

/-- An eventually constant derivative observation on an entire sequence agrees exactly
with that derivative of its locally uniform limit. -/
theorem iteratedDeriv_limit_eq_of_eventually_eq
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ n, Differentiable ℂ (F n))
    (hlim : TendstoLocallyUniformly F f atTop)
    (k : ℕ) (z c : ℂ)
    (hdata : ∀ᶠ n in atTop, iteratedDeriv k (F n) z = c) :
    iteratedDeriv k f z = c := by
  have hvalue := (tendstoLocallyUniformly_iteratedDeriv hF hlim k).tendstoLocallyUniformlyOn.tendsto_at
    (mem_univ z)
  have hconstant : Tendsto (fun n => iteratedDeriv k (F n) z) atTop (𝓝 c) :=
    tendsto_const_nhds.congr' (hdata.mono fun _ hn => hn.symm)
  exact tendsto_nhds_unique hvalue hconstant

/-- Locally uniform limits preserve the condition of taking real values on the real line. -/
theorem im_limit_eq_zero_on_real
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hlim : TendstoLocallyUniformly F f atTop)
    (hreal : ∀ n (x : ℝ), (F n x).im = 0) (x : ℝ) :
    (f x).im = 0 := by
  have hvalue := hlim.tendstoLocallyUniformlyOn.tendsto_at (mem_univ (x : ℂ))
  have him : Tendsto (fun n => (F n x).im) atTop (𝓝 (f x).im) :=
    Complex.continuous_im.continuousAt.tendsto.comp hvalue
  have hzero : Tendsto (fun n => (F n x).im) atTop (𝓝 0) := by
    simpa only [hreal] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ))
      atTop (𝓝 0))
  exact tendsto_nhds_unique him hzero

/-- For an entire function, each iterated real derivative of its real restriction is the
real part of the corresponding complex derivative. Real-valuedness is not required. -/
theorem iteratedDeriv_real_restriction
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (k : ℕ) :
    iteratedDeriv k (fun x : ℝ => (f x).re) =
      fun x : ℝ => (iteratedDeriv k f x).re := by
  induction k with
  | zero => simp only [iteratedDeriv_zero]
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    rw [iteratedDeriv_succ]
    have hdiff : Differentiable ℂ (iteratedDeriv k f) :=
      hf.contDiff.differentiable_iteratedDeriv' k
    exact (hdiff (x : ℂ)).hasDerivAt.real_of_complex.deriv

/-- Each fixed real derivative of the restrictions converges pointwise when the entire
functions converge locally uniformly on the complex plane. -/
theorem tendsto_real_iteratedDeriv
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ n, Differentiable ℂ (F n))
    (hlim : TendstoLocallyUniformly F f atTop)
    (k : ℕ) (x : ℝ) :
    Tendsto (fun n => iteratedDeriv k (fun t : ℝ => (F n t).re) x) atTop
      (𝓝 (iteratedDeriv k (fun t : ℝ => (f t).re) x)) := by
  have hf : Differentiable ℂ f := differentiableOn_univ.mp <|
    hlim.tendstoLocallyUniformlyOn.differentiableOn
      (Eventually.of_forall fun n => (hF n).differentiableOn) isOpen_univ
  have hvalue := (tendstoLocallyUniformly_iteratedDeriv hF hlim k).tendstoLocallyUniformlyOn.tendsto_at
    (mem_univ (x : ℂ))
  have hre : Tendsto (fun n => (iteratedDeriv k (F n) x).re) atTop
      (𝓝 (iteratedDeriv k f x).re) :=
    Complex.continuous_re.continuousAt.tendsto.comp hvalue
  have hseq (n : ℕ) : iteratedDeriv k (fun t : ℝ => (F n t).re) x =
      (iteratedDeriv k (F n) x).re :=
    congrFun (iteratedDeriv_real_restriction (hF n) k) x
  simpa only [iteratedDeriv_real_restriction hf, hseq] using hre

/-- Eventual equality of real derivative observations is retained by a locally uniform
limit of entire functions. This is the analytic step in preserving an exact transcript. -/
theorem real_iteratedDeriv_limit_eq_of_eventually_eq
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ n, Differentiable ℂ (F n))
    (hlim : TendstoLocallyUniformly F f atTop)
    (k : ℕ) (x c : ℝ)
    (hdata : ∀ᶠ n in atTop, iteratedDeriv k (fun t : ℝ => (F n t).re) x = c) :
    iteratedDeriv k (fun t : ℝ => (f t).re) x = c := by
  exact tendsto_nhds_unique (tendsto_real_iteratedDeriv hF hlim k x)
    (tendsto_const_nhds.congr' (hdata.mono fun _ hn => hn.symm))

/-- Closed bounds on real derivatives of the approximating entire functions pass to the
locally uniform limit. Applied at order one, this preserves the global derivative bounds. -/
theorem real_iteratedDeriv_limit_mem_Icc
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hF : ∀ n, Differentiable ℂ (F n))
    (hlim : TendstoLocallyUniformly F f atTop)
    (k : ℕ) (x lower upper : ℝ)
    (hbound : ∀ᶠ n in atTop,
      iteratedDeriv k (fun t : ℝ => (F n t).re) x ∈ Icc lower upper) :
    iteratedDeriv k (fun t : ℝ => (f t).re) x ∈ Icc lower upper := by
  exact isClosed_Icc.mem_of_tendsto (tendsto_real_iteratedDeriv hF hlim k x) hbound

end KungTraub
