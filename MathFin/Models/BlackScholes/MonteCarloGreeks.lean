/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.Models.BlackScholes.Call
public import MathFin.Models.BlackScholes.GBMLogMoments
public import MathFin.Models.BlackScholes.Market
public import MathFin.Models.BlackScholes.PDE
public import MathFin.Probability.Gaussian.GaussianCDFDeriv
public import MathFin.Probability.Gaussian.GaussianMoments
public import MathFin.Probability.Gaussian.GaussianPartialMoments
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Probability.HasLaw

/-!
# Monte Carlo Greeks and the Euler step

The two delta estimators of Monte Carlo sensitivity analysis, in the lognormal setting
`BSCallHyp`, both have mean the Black–Scholes delta `Φ(d₁)`:

* **The pathwise estimator** `e^{-rT}·1{S_T > K}·S_T/S₀`
  (`pathwiseDeltaPayoff`): differentiating the call payoff where it is smooth (on the
  exercise region, by `bsTerminal_gt_K_iff`) and integrating by the completing-the-square
  tail integral gives `pathwiseDeltaPayoff_mean`. The payoff's kink at `K` needs no separate
  treatment: `pathwiseDelta_deriv` shows the discounted expected payoff
  `S ↦ e^{-rT}·𝒩[(S_T − K)⁺]` is differentiable in the spot, with the pathwise estimator's
  mean as its derivative, by transferring along `hasDerivAt_bsV_S`.
* **The likelihood-ratio estimator** `e^{-rT}·(S_T − K)⁺·(log(S_T/S₀) − (r−σ²/2)T)/(S₀σ²T)`
  (`likelihoodRatioDeltaPayoff`), the payoff times the score of the terminal's lognormal
  density: the completing-the-square shift turns the weight into the `N(σ√T, 1)` density,
  whose centered truncated first moment splits into the shifted mass and the density value
  (`integral_sub_id_mul_gaussianPDFReal_Ioi`,
  `integral_exp_mul_gaussianPDFReal_id_Ioi`), and the residual
  `(S₀ϕ(d₁) − Ke^{-rT}ϕ(d₂))/(S₀σ√T)` vanishes by the magic identity `bs_identity`
  (`likelihoodRatioDeltaPayoff_mean`).
* **The market bridge.** `hasDerivAt_marketPrice_S`: the Black–Scholes market's call price
  under the Girsanov pricing measure is differentiable in the initial spot, with derivative
  `Φ(d₁)` — through `price_europeanCall_constGirsanovMeasure` and `hasDerivAt_bsV_S`. This is
  the derivative both estimators estimate.

The one-step Euler–Maruyama scheme for the GBM
`dS = r·S dt + σ·S dW` discretizes one step of length `Δ` to
`S₀(1 + rΔ + σ√Δ·z)` (`eulerGbmStep`): its mean is the linearization `S₀(1 + rΔ)` and its
variance `σ²S₀²Δ` (module-internal lemmas), and both underestimate the exact GBM step's
mean `S₀e^{rΔ}` and variance `S₀²e^{2rΔ}(e^{σ²Δ} − 1)` for a nonnegative rate times step
(`eulerGbmStep_mean_le_exact`, `eulerGbmStep_variance_le_exact`) — the bias every
Euler-scheme price carries at the first step.

## Main definitions

* `eulerGbmStep`: the one-step Euler–Maruyama terminal for GBM.
* `pathwiseDeltaPayoff`: the pathwise delta estimator's integrand.
* `likelihoodRatioDeltaPayoff`: the likelihood-ratio delta estimator's integrand.

## Main results

* `pathwiseDeltaPayoff_mean`, `likelihoodRatioDeltaPayoff_mean`: both estimator means are
  `Φ(d₁)`.
* `pathwiseDelta_deriv`: the derivative under the expectation is the pathwise estimator's
  mean.
* `hasDerivAt_marketPrice_S`: the market price's spot-derivative is `Φ(d₁)`.
* `eulerGbmStep_mean_le_exact`, `eulerGbmStep_variance_le_exact`: the Euler step's mean and
  variance underestimate the exact GBM step's.

## References

* [S. Burgos and M. B. Giles, *The computation of Greeks with multilevel Monte
  Carlo*][BurgosGiles2010], §1.2; §2.1
* [P. Glasserman, *Monte Carlo Methods in Financial Engineering*][Glasserman2003]
* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], ch. 21

## Tags

Monte Carlo, Greeks, pathwise sensitivity, likelihood ratio, delta, Euler-Maruyama scheme,
geometric Brownian motion, simulation bias, MSC 91G60, MSC 65C05, JEL C63
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real Filter
open scoped NNReal ENNReal

/-! ### The one-step Euler–Maruyama scheme for geometric Brownian motion -/

/-- **The one-step Euler–Maruyama terminal** for geometric Brownian motion
`dS = r·S dt + σ·S dW`: one step of length `Δ` from `S₀` gives `S₀·(1 + r·Δ + σ·√Δ·z)`
for a standard-normal sample `z` (the Brownian increment `ΔW = √Δ·z`). -/
noncomputable def eulerGbmStep (S_0 r σ Δ z : ℝ) : ℝ :=
  S_0 * (1 + r * Δ + σ * Real.sqrt Δ * z)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} [IsProbabilityMeasure Q]
  {S r σ Δ : ℝ} {Z : Ω → ℝ}

/-- The Euler step is an affine function of the standard normal. -/
private lemma eulerGbmStep_affine (S r σ Δ z : ℝ) :
    eulerGbmStep S r σ Δ z = S * (1 + r * Δ) + (σ * S * Real.sqrt Δ) * z := by
  unfold eulerGbmStep
  ring

omit [IsProbabilityMeasure Q] in
/-- The Euler step is Gaussian: an affine image of the standard normal. -/
private lemma eulerGbmStep_hasLaw (hZ : HasLaw Z (gaussianReal 0 1) Q) :
    HasLaw (fun ω ↦ eulerGbmStep S r σ Δ (Z ω))
      (gaussianReal (S * (1 + r * Δ))
        (NNReal.mk ((σ * S * Real.sqrt Δ) ^ 2) (sq_nonneg _) * 1)) Q := by
  have hfun : (fun ω ↦ eulerGbmStep S r σ Δ (Z ω))
      = (fun ω ↦ S * (1 + r * Δ) + (σ * S * Real.sqrt Δ) * Z ω) := by
    funext ω; rw [eulerGbmStep_affine]
  rw [hfun]
  have hL := gaussianReal_const_add (gaussianReal_const_mul hZ (σ * S * Real.sqrt Δ))
    (S * (1 + r * Δ))
  rw [mul_zero, zero_add] at hL
  exact hL

omit [IsProbabilityMeasure Q] in
/-- The Euler step's mean is the linearized drift `S₀(1 + rΔ)`. -/
private lemma eulerGbmStep_mean_eq (hZ : HasLaw Z (gaussianReal 0 1) Q) :
    ∫ ω, eulerGbmStep S r σ Δ (Z ω) ∂Q = S * (1 + r * Δ) := by
  rw [(eulerGbmStep_hasLaw hZ).integral_eq, integral_id_gaussianReal]

omit [IsProbabilityMeasure Q] in
/-- The Euler step's variance is `σ²S₀²Δ` for a nonnegative step, in the second-moment form
`𝔼[X²] − 𝔼[X]²`. -/
private lemma eulerGbmStep_variance_eq (hZ : HasLaw Z (gaussianReal 0 1) Q) (hΔ : 0 ≤ Δ) :
    ∫ ω, eulerGbmStep S r σ Δ (Z ω) ^ 2 ∂Q
        - (∫ ω, eulerGbmStep S r σ Δ (Z ω) ∂Q) ^ 2
      = σ ^ 2 * S ^ 2 * Δ := by
  have hsq : (σ * S * Real.sqrt Δ) ^ 2 = σ ^ 2 * S ^ 2 * Δ := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hΔ]
  rw [integral_sq_of_hasLaw_gaussianReal (eulerGbmStep_hasLaw hZ), eulerGbmStep_mean_eq hZ,
    NNReal.coe_mul, NNReal.coe_one, mul_one, NNReal.coe_mk, hsq]
  ring

omit [IsProbabilityMeasure Q] in
/-- The exact GBM step's mean is `S₀e^{rΔ}` (the MGF of the lognormal step). -/
private lemma bsTerminal_mean_eq (hZ : HasLaw Z (gaussianReal 0 1) Q) (hΔ : 0 ≤ Δ) :
    ∫ ω, bsTerminal S r σ Δ (Z ω) ∂Q = S * Real.exp (r * Δ) := by
  have hmeas : AEStronglyMeasurable (fun z : ℝ ↦ bsTerminal S r σ Δ z) (gaussianReal 0 1) := by
    unfold bsTerminal
    exact (by fun_prop : Measurable fun z : ℝ ↦
      S * Real.exp ((r - σ ^ 2 / 2) * Δ + σ * Real.sqrt Δ * z)).aestronglyMeasurable
  have hkey : (r - σ ^ 2 / 2) * Δ + (σ * Real.sqrt Δ) ^ 2 / 2 = r * Δ := by
    have hsq : (σ * Real.sqrt Δ) ^ 2 = σ ^ 2 * Δ := by
      rw [mul_pow, Real.sq_sqrt hΔ]
    rw [hsq]; ring
  rw [show (fun ω : Ω ↦ bsTerminal S r σ Δ (Z ω))
        = (fun z : ℝ ↦ bsTerminal S r σ Δ z) ∘ Z from rfl,
    hZ.integral_comp hmeas]
  simp only [bsTerminal]
  rw [integral_const_mul,
    integral_gaussianReal_eq_integral_smul (one_ne_zero : (1 : ℝ≥0) ≠ 0),
    show (fun x : ℝ ↦ gaussianPDFReal 0 1 x •
        Real.exp ((r - σ ^ 2 / 2) * Δ + σ * Real.sqrt Δ * x))
      = fun x : ℝ ↦ Real.exp ((r - σ ^ 2 / 2) * Δ)
          * (Real.exp (σ * Real.sqrt Δ * x) * gaussianPDFReal 0 1 x) from
      funext fun x ↦ by rw [smul_eq_mul, Real.exp_add]; ring,
    integral_const_mul, integral_exp_mul_gaussianPDFReal_univ,
    ← Real.exp_add, hkey]

omit [IsProbabilityMeasure Q] in
/-- The exact GBM step's variance is `S₀²e^{2rΔ}(e^{σ²Δ} − 1)` for a nonnegative step, in the
second-moment form `𝔼[X²] − 𝔼[X]²` (`variance_terminal`'s form). -/
private lemma bsTerminal_variance_eq (hZ : HasLaw Z (gaussianReal 0 1) Q) (hΔ : 0 ≤ Δ) :
    ∫ ω, bsTerminal S r σ Δ (Z ω) ^ 2 ∂Q
        - (∫ ω, bsTerminal S r σ Δ (Z ω) ∂Q) ^ 2
      = S ^ 2 * Real.exp (2 * r * Δ) * (Real.exp (σ ^ 2 * Δ) - 1) := by
  have hmeas2 : AEStronglyMeasurable (fun z : ℝ ↦ bsTerminal S r σ Δ z ^ 2)
      (gaussianReal 0 1) := by
    unfold bsTerminal
    exact (by fun_prop : Measurable fun z : ℝ ↦
      (S * Real.exp ((r - σ ^ 2 / 2) * Δ + σ * Real.sqrt Δ * z)) ^ 2).aestronglyMeasurable
  have hkey2 : (r - σ ^ 2 / 2) * Δ * 2 + (σ * Real.sqrt Δ * 2) ^ 2 / 2
      = 2 * r * Δ + σ ^ 2 * Δ := by
    have hsq : (σ * Real.sqrt Δ * 2) ^ 2 = σ ^ 2 * Δ * 4 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hΔ]; ring
    rw [hsq]; ring
  have hsplit2int : ∀ x : ℝ,
      gaussianPDFReal 0 1 x * ((S * Real.exp ((r - σ ^ 2 / 2) * Δ + σ * Real.sqrt Δ * x)) ^ 2)
        = (S * Real.exp ((r - σ ^ 2 / 2) * Δ)) ^ 2
            * (Real.exp ((σ * Real.sqrt Δ * 2) * x) * gaussianPDFReal 0 1 x) := by
    intro x
    have hsq : Real.exp ((r - σ ^ 2 / 2) * Δ + σ * Real.sqrt Δ * x) ^ 2
        = Real.exp ((r - σ ^ 2 / 2) * Δ * 2) * Real.exp ((σ * Real.sqrt Δ * 2) * x) := by
      conv_lhs => rw [pow_two, ← Real.exp_add]
      rw [show ((r - σ ^ 2 / 2) * Δ + σ * Real.sqrt Δ * x)
          + ((r - σ ^ 2 / 2) * Δ + σ * Real.sqrt Δ * x)
        = (r - σ ^ 2 / 2) * Δ * 2 + σ * Real.sqrt Δ * 2 * x from by ring]
      exact Real.exp_add _ _
    have hsq2 : Real.exp ((r - σ ^ 2 / 2) * Δ) ^ 2 = Real.exp ((r - σ ^ 2 / 2) * Δ * 2) := by
      conv_lhs => rw [pow_two, ← Real.exp_add]
      rw [show ((r - σ ^ 2 / 2) * Δ) + ((r - σ ^ 2 / 2) * Δ)
        = (r - σ ^ 2 / 2) * Δ * 2 from by ring]
    rw [mul_pow, mul_pow, hsq, hsq2]
    ring
  have hsquare (A : ℝ) : (S * Real.exp A) ^ 2 = S ^ 2 * Real.exp (A * 2) := by
    conv_lhs => rw [mul_pow, pow_two, pow_two, ← Real.exp_add]
    rw [show A + A = A * 2 from by ring, ← pow_two]
  rw [show (fun ω : Ω ↦ bsTerminal S r σ Δ (Z ω) ^ 2)
        = (fun z : ℝ ↦ bsTerminal S r σ Δ z ^ 2) ∘ Z from rfl,
    hZ.integral_comp hmeas2,
    integral_gaussianReal_eq_integral_smul (one_ne_zero : (1 : ℝ≥0) ≠ 0),
    show (fun x : ℝ ↦ gaussianPDFReal 0 1 x • bsTerminal S r σ Δ x ^ 2)
        = fun x : ℝ ↦ (S * Real.exp ((r - σ ^ 2 / 2) * Δ)) ^ 2
            * (Real.exp ((σ * Real.sqrt Δ * 2) * x) * gaussianPDFReal 0 1 x) from
      funext fun x ↦ by rw [smul_eq_mul]; exact hsplit2int x,
    integral_const_mul, integral_exp_mul_gaussianPDFReal_univ,
    hsquare ((r - σ ^ 2 / 2) * Δ), mul_assoc,
    ← Real.exp_add, hkey2]
  rw [bsTerminal_mean_eq hZ hΔ, hsquare (r * Δ)]
  have hexp : r * Δ * 2 = 2 * r * Δ := by ring
  rw [hexp, Real.exp_add]
  ring

/-! ### The Euler step against the exact step -/

omit [IsProbabilityMeasure Q] in
/-- **The Euler step's mean underestimates the exact GBM step's mean.** The one-step
Euler–Maruyama terminal has mean `S₀(1 + rΔ)` — the linearization of the exact step's mean
`𝔼[S_Δ] = S₀e^{rΔ}` — so it underestimates it for a nonnegative spot and step. (The measure
`Q` carries the standard-normal law of `Z`, so it is a probability measure.) -/
theorem eulerGbmStep_mean_le_exact (hZ : HasLaw Z (gaussianReal 0 1) Q) (hS : 0 ≤ S)
    (hΔ : 0 ≤ Δ) :
    ∫ ω, eulerGbmStep S r σ Δ (Z ω) ∂Q
      ≤ ∫ ω, bsTerminal S r σ Δ (Z ω) ∂Q := by
  rw [eulerGbmStep_mean_eq hZ, bsTerminal_mean_eq hZ hΔ]
  have h1 : 1 + r * Δ ≤ Real.exp (r * Δ) := by linarith [Real.add_one_le_exp (r * Δ)]
  exact mul_le_mul_of_nonneg_left h1 hS

omit [IsProbabilityMeasure Q] in
/-- **The Euler step's variance underestimates the exact GBM step's variance** for a
nonnegative rate times step, in the second-moment form `𝔼[X²] − 𝔼[X]²`: the Euler step's
variance `σ²S₀²Δ` is at most the exact step's `S₀²e^{2rΔ}(e^{σ²Δ} − 1)`, since
`σ²Δ ≤ e^{σ²Δ} − 1` and `1 ≤ e^{2rΔ}`. (The measure `Q` carries the standard-normal law of
`Z`, so it is a probability measure.) -/
theorem eulerGbmStep_variance_le_exact (hZ : HasLaw Z (gaussianReal 0 1) Q) (hrΔ : 0 ≤ r * Δ)
    (hΔ : 0 ≤ Δ) :
    ∫ ω, eulerGbmStep S r σ Δ (Z ω) ^ 2 ∂Q
        - (∫ ω, eulerGbmStep S r σ Δ (Z ω) ∂Q) ^ 2
      ≤ ∫ ω, bsTerminal S r σ Δ (Z ω) ^ 2 ∂Q
        - (∫ ω, bsTerminal S r σ Δ (Z ω) ∂Q) ^ 2 := by
  rw [eulerGbmStep_variance_eq hZ hΔ, bsTerminal_variance_eq hZ hΔ]
  have h1 : σ ^ 2 * Δ ≤ Real.exp (σ ^ 2 * Δ) - 1 := by
    have := Real.add_one_le_exp (σ ^ 2 * Δ)
    linarith
  have h2 : (1 : ℝ) ≤ Real.exp (2 * r * Δ) := by
    have := Real.add_one_le_exp (2 * r * Δ)
    linarith
  calc σ ^ 2 * S ^ 2 * Δ
      = S ^ 2 * (σ ^ 2 * Δ) := by ring
    _ ≤ S ^ 2 * (Real.exp (σ ^ 2 * Δ) - 1) :=
      mul_le_mul_of_nonneg_left h1 (sq_nonneg S)
    _ ≤ S ^ 2 * Real.exp (2 * r * Δ) * (Real.exp (σ ^ 2 * Δ) - 1) := by
      have hstep : S ^ 2 ≤ S ^ 2 * Real.exp (2 * r * Δ) := by
        have h1' := mul_le_mul_of_nonneg_left h2 (sq_nonneg S)
        rwa [mul_one] at h1'
      exact mul_le_mul_of_nonneg_right hstep
        (by linarith [mul_nonneg (sq_nonneg σ) hΔ])

/-! ### The pathwise delta -/

variable {K T : ℝ}

/-- The discounted expected call payoff as a function of the spot (the integrand of
`bs_call_formula`'s left-hand side). -/
private lemma integral_discountedPayoff_eq_bsV {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S K r σ T : ℝ} {Z : Ω → ℝ} (hZ : HasLaw Z (gaussianReal 0 1) Q) (hS : 0 < S)
    (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < T) :
    ∫ ω, Real.exp (-r * T) * max (bsTerminal S r σ T (Z ω) - K) 0 ∂Q = bsV K r σ S T :=
  integral_bsCall_payoff_eq_bsV ⟨hS, hK, hσ, hT, hZ⟩

omit [IsProbabilityMeasure Q] in
/-- The exercise-region bound in the delta computations: `σ√T − (−d₂) = d₁`. -/
private lemma sqrtT_add_bsd2_eq_bsd1 (S K r σ T : ℝ) :
    σ * Real.sqrt T - -bsd2 S K r σ T = bsd1 S K r σ T := by
  simp only [bsd2]
  ring

omit [IsProbabilityMeasure Q] in
/-- The pathwise delta integrand on the exercise region: the discounted terminal-to-spot
ratio times the standard-normal density. -/
private lemma pathwise_integrand_congr (S r σ T : ℝ) (hS : 0 < S) (x : ℝ) :
    bsTerminal S r σ T x / S * gaussianPDFReal 0 1 x
      = Real.exp ((r - σ ^ 2 / 2) * T)
          * (Real.exp (σ * Real.sqrt T * x) * gaussianPDFReal 0 1 x) := by
  unfold bsTerminal
  rw [Real.exp_add, mul_div_cancel_left₀ _ hS.ne']
  ring

/-- **The pathwise delta estimator's integrand**: the discounted payoff-derivative
`e^{−rT}·1{S_T > K}·S_T/S₀`, as a function of the standard-normal sample — on the exercise
region `{z > −d₂}` (where `S_T(z) > K`, `bsTerminal_gt_K_iff`) it is the differentiated
payoff, off it zero. -/
noncomputable def pathwiseDeltaPayoff (S K r σ T z : ℝ) : ℝ :=
  Real.exp (-r * T) *
    (Set.Ioi (-bsd2 S K r σ T)).indicator (fun z' ↦ bsTerminal S r σ T z' / S) z

omit [IsProbabilityMeasure Q] in
/-- The pathwise delta integrand is measurable. -/
private lemma measurable_pathwiseDeltaPayoff (S K r σ T : ℝ) :
    Measurable (fun z : ℝ ↦ pathwiseDeltaPayoff S K r σ T z) := by
  have hf : Measurable (fun z' : ℝ ↦ bsTerminal S r σ T z' / S) := by
    unfold bsTerminal; fun_prop
  unfold pathwiseDeltaPayoff
  exact (Measurable.const_mul (Measurable.indicator hf measurableSet_Ioi) (Real.exp (-r * T)))

/-- **The pathwise delta.** The mean of the pathwise estimator is the Black–Scholes delta
`Φ(d₁)`: the derivative-under-the-expectation value, computed on the exercise region by the
completing-the-square tail integral. -/
theorem pathwiseDeltaPayoff_mean {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S K r σ T : ℝ} {Z : Ω → ℝ} (h : BSCallHyp Q S K r σ T Z) :
    ∫ ω, pathwiseDeltaPayoff S K r σ T (Z ω) ∂Q = Phi (bsd1 S K r σ T) := by
  obtain ⟨hS, hK, hσ, hT, hZ⟩ := h
  have hmeas : AEStronglyMeasurable (fun z : ℝ ↦ pathwiseDeltaPayoff S K r σ T z)
      (gaussianReal 0 1) := (measurable_pathwiseDeltaPayoff S K r σ T).aestronglyMeasurable
  have hsplit : (fun x : ℝ ↦ gaussianPDFReal 0 1 x • pathwiseDeltaPayoff S K r σ T x)
      = fun x : ℝ ↦ (Set.Ioi (-bsd2 S K r σ T)).indicator
          (fun x' ↦ Real.exp (-r * T) *
            (bsTerminal S r σ T x' / S * gaussianPDFReal 0 1 x')) x := by
    funext x
    rw [smul_eq_mul, pathwiseDeltaPayoff]
    by_cases hx : x ∈ Set.Ioi (-bsd2 S K r σ T)
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]; ring
    · simp only [Set.indicator_of_notMem hx, mul_zero]
  rw [show (fun ω : Ω ↦ pathwiseDeltaPayoff S K r σ T (Z ω))
        = (fun z : ℝ ↦ pathwiseDeltaPayoff S K r σ T z) ∘ Z from rfl,
    hZ.integral_comp hmeas,
    integral_gaussianReal_eq_integral_smul (one_ne_zero : (1 : ℝ≥0) ≠ 0), hsplit,
    integral_indicator measurableSet_Ioi,
    setIntegral_congr_fun measurableSet_Ioi
      (fun x (_ : x ∈ Set.Ioi (-bsd2 S K r σ T)) ↦ by
        rw [pathwise_integrand_congr S r σ T hS x]),
    integral_const_mul, integral_const_mul, integral_exp_mul_gaussianPDFReal_Ioi,
    sqrtT_add_bsd2_eq_bsd1]
  have hcomb : Real.exp (-r * T) * Real.exp ((r - σ ^ 2 / 2) * T)
      * Real.exp ((σ * Real.sqrt T) ^ 2 / 2) = 1 := by
    rw [mul_assoc, ← Real.exp_add, ← Real.exp_add,
      show (σ * Real.sqrt T) ^ 2 = σ ^ 2 * T from by
        rw [mul_pow, Real.sq_sqrt hT.le],
      show -r * T + ((r - σ ^ 2 / 2) * T + σ ^ 2 * T / 2) = 0 from by ring]
    exact Real.exp_zero
  linear_combination
    (Phi (bsd1 S K r σ T)) * hcomb

/-- **The pathwise delta as a derivative under the expectation.** The discounted expected
payoff `S ↦ e^{−rT}·𝔼[(S_T − K)⁺]` is differentiable in the spot, and its derivative at `S`
is the pathwise estimator's mean — the differentiated payoff does not need the kink at `K`
handled separately. -/
theorem pathwiseDelta_deriv {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S K r σ T : ℝ} {Z : Ω → ℝ} (h : BSCallHyp Q S K r σ T Z) :
    HasDerivAt (fun S' : ℝ ↦ ∫ ω, Real.exp (-r * T) * max (bsTerminal S' r σ T (Z ω) - K) 0 ∂Q)
      (∫ ω, pathwiseDeltaPayoff S K r σ T (Z ω) ∂Q) S := by
  obtain ⟨hS, hK, hσ, hT, hZ⟩ := h
  have hEq : (fun S' : ℝ ↦ ∫ ω, Real.exp (-r * T) * max (bsTerminal S' r σ T (Z ω) - K) 0 ∂Q)
      =ᶠ[nhds S] (fun S' : ℝ ↦ bsV K r σ S' T) := by
    filter_upwards [(eventually_gt_nhds hS)] with S' hS'
    exact integral_discountedPayoff_eq_bsV hZ hS' hK hσ hT
  exact (hasDerivAt_bsV_S hK hσ hS hT).congr_of_eventuallyEq hEq |>.congr_deriv
    (pathwiseDeltaPayoff_mean ⟨hS, hK, hσ, hT, hZ⟩).symm

/-! ### The likelihood-ratio delta -/

omit [IsProbabilityMeasure Q] in
/-- The tail mass of `N(m,1)`: `∫_(a,∞) ϕ(m,1,z) dz = Φ(m − a)`. -/
private lemma integral_gaussianPDFReal_m_Ioi (m a : ℝ) :
    ∫ z in Set.Ioi a, gaussianPDFReal m 1 z = Phi (m - a) := by
  rw [setIntegral_gaussianPDFReal_eq_toReal measurableSet_Ioi m]
  have hshift : gaussianReal m (1 : ℝ≥0) (Set.Ioi a)
      = gaussianReal (0 : ℝ) 1 (Set.Ioi (a - m)) := by
    have hmap : (gaussianReal (0 : ℝ) 1).map (fun y ↦ y + m) = gaussianReal m 1 := by
      rw [gaussianReal_map_add_const, zero_add]
    rw [← hmap, Measure.map_apply (by fun_prop) measurableSet_Ioi]
    congr 1
    ext y
    simp [Set.mem_Ioi, sub_lt_iff_lt_add, add_comm]
  rw [hshift, gaussianReal_Ioi_toReal, neg_sub]

omit [IsProbabilityMeasure Q] in
/-- The truncated first moment of `N(m,1)`: `∫_(a,∞) z·ϕ(m,1,z) dz = m·Φ(m−a) + ϕ(m,1,a)` —
the centered moment plus the shifted mass. -/
private lemma integral_id_mul_gaussianPDFReal_m_Ioi (m a : ℝ) :
    ∫ z in Set.Ioi a, z * gaussianPDFReal m 1 z
      = m * Phi (m - a) + gaussianPDFReal m 1 a := by
  have hint1 : IntegrableOn (fun z : ℝ ↦ (z - m) * gaussianPDFReal m 1 z) (Set.Ioi a)
      volume := by
    have h1 : Integrable (fun z : ℝ ↦ z * gaussianPDFReal m 1 z) volume :=
      integrable_id_mul_gaussianPDFReal_m_volume m
    have h2 : Integrable (fun z : ℝ ↦ m * gaussianPDFReal m 1 z) volume :=
      (integrable_gaussianPDFReal m 1).const_mul m
    exact (h1.sub h2).congr (Filter.Eventually.of_forall fun z ↦ by
      simp only [Pi.sub_apply]; ring) |>.integrableOn
  have hint2 : IntegrableOn (fun z : ℝ ↦ m * gaussianPDFReal m 1 z) (Set.Ioi a) volume :=
    ((integrable_gaussianPDFReal m 1).const_mul m).integrableOn
  rw [show (fun z : ℝ ↦ z * gaussianPDFReal m 1 z)
        = fun z : ℝ ↦ (z - m) * gaussianPDFReal m 1 z + m * gaussianPDFReal m 1 z from
      funext fun z ↦ by ring,
    integral_add hint1 hint2, integral_sub_id_mul_gaussianPDFReal_Ioi, add_comm]
  have hmass : ∫ z in Set.Ioi a, m * gaussianPDFReal m 1 z = m * Phi (m - a) := by
    rw [integral_const_mul, integral_gaussianPDFReal_m_Ioi]
  rw [hmass]

omit [IsProbabilityMeasure Q] in
/-- The exponentially weighted truncated first moment of the standard normal:
`∫_(a,∞) e^{cz}·z·ϕ(z) dz = e^{c²/2}·(c·Φ(c−a) + ϕ(c,1,a))` — completing the square turns
the weight into the `N(c,1)` density, and the truncated first moment of `N(c,1)` splits into
the centered moment plus the shifted mass. -/
private lemma integral_exp_mul_gaussianPDFReal_id_Ioi (a c : ℝ) :
    ∫ z in Set.Ioi a, Real.exp (c * z) * z * gaussianPDFReal 0 1 z
      = Real.exp (c ^ 2 / 2) * (c * Phi (c - a) + gaussianPDFReal c 1 a) := by
  have hint : IntegrableOn (fun z : ℝ ↦ z * gaussianPDFReal c 1 z) (Set.Ioi a) volume :=
    (integrable_id_mul_gaussianPDFReal_m_volume c).integrableOn
  rw [show (fun z : ℝ ↦ Real.exp (c * z) * z * gaussianPDFReal 0 1 z)
        = fun z : ℝ ↦ Real.exp (c ^ 2 / 2) * (z * gaussianPDFReal c 1 z) from
      funext fun z ↦ by
        rw [mul_comm (Real.exp (c * z)) z, mul_assoc, exp_mul_gaussianPDFReal_zero_one]
        ring,
    integral_const_mul, integral_id_mul_gaussianPDFReal_m_Ioi]

/-- **The likelihood-ratio delta estimator's integrand**: the discounted payoff times the
score of the terminal's lognormal density — the standardized log-return
`(log(S_T/S₀) − (r−σ²/2)T)/(S₀σ²T)` — on the exercise region, zero off it. -/
noncomputable def likelihoodRatioDeltaPayoff (S K r σ T z : ℝ) : ℝ :=
  Real.exp (-r * T) *
    (Set.Ioi (-bsd2 S K r σ T)).indicator
      (fun z' ↦ (bsTerminal S r σ T z' - K)
          * (bsLogReturn r σ T z' - (r - σ ^ 2 / 2) * T) / (S * σ ^ 2 * T)) z

/-- **The likelihood-ratio delta.** The mean of the likelihood-ratio estimator is the
Black–Scholes delta `Φ(d₁)`: the completing-the-square tail integral and the two truncated
first moments of `N(0,1)` and `N(σ√T,1)` reduce the discounted score-weighted payoff to
`Φ(d₁)`, with the residual `(S₀ϕ(d₁) − Ke^{-rT}ϕ(d₂))/(S₀σ√T)` vanishing by `bs_identity`. -/
theorem likelihoodRatioDeltaPayoff_mean {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S K r σ T : ℝ} {Z : Ω → ℝ} (h : BSCallHyp Q S K r σ T Z) :
    ∫ ω, likelihoodRatioDeltaPayoff S K r σ T (Z ω) ∂Q = Phi (bsd1 S K r σ T) := by
  obtain ⟨hS, hK, hσ, hT, hZ⟩ := h
  have hsq : (σ * Real.sqrt T) ^ 2 = σ ^ 2 * T := by rw [mul_pow, Real.sq_sqrt hT.le]
  have hmeas : AEStronglyMeasurable (fun z : ℝ ↦ likelihoodRatioDeltaPayoff S K r σ T z)
      (gaussianReal 0 1) := by
    have hf : Measurable (fun z' : ℝ ↦ (bsTerminal S r σ T z' - K)
        * (bsLogReturn r σ T z' - (r - σ ^ 2 / 2) * T) / (S * σ ^ 2 * T)) := by
      unfold bsTerminal bsLogReturn; fun_prop
    exact (Measurable.const_mul (Measurable.indicator hf measurableSet_Ioi)
      (Real.exp (-r * T))).aestronglyMeasurable
  have hsplit : (fun x : ℝ ↦ gaussianPDFReal 0 1 x • likelihoodRatioDeltaPayoff S K r σ T x)
      = fun x : ℝ ↦ (Set.Ioi (-bsd2 S K r σ T)).indicator
          (fun x' ↦ Real.exp (-r * T) / (S * σ ^ 2 * T) *
            (S * Real.exp ((r - σ ^ 2 / 2) * T) * (σ * Real.sqrt T) *
              (Real.exp (σ * Real.sqrt T * x') * x' * gaussianPDFReal 0 1 x')
            - K * (σ * Real.sqrt T) * (x' * gaussianPDFReal 0 1 x'))) x := by
    funext x
    rw [smul_eq_mul, likelihoodRatioDeltaPayoff]
    by_cases hx : x ∈ Set.Ioi (-bsd2 S K r σ T)
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      show gaussianPDFReal 0 1 x * (Real.exp (-r * T) *
            ((bsTerminal S r σ T x - K)
              * (bsLogReturn r σ T x - (r - σ ^ 2 / 2) * T) / (S * σ ^ 2 * T)))
        = Real.exp (-r * T) / (S * σ ^ 2 * T) *
          (S * Real.exp ((r - σ ^ 2 / 2) * T) * (σ * Real.sqrt T) *
              (Real.exp (σ * Real.sqrt T * x) * x * gaussianPDFReal 0 1 x)
            - K * (σ * Real.sqrt T) * (x * gaussianPDFReal 0 1 x))
      unfold bsTerminal bsLogReturn
      rw [Real.exp_add]
      have hne : S * σ ^ 2 * T ≠ 0 :=
        mul_ne_zero (mul_ne_zero hS.ne' (pow_ne_zero 2 hσ.ne')) hT.ne'
      field_simp
      ring
    · simp only [Set.indicator_of_notMem hx, mul_zero]
  have hintA : IntegrableOn (fun x : ℝ ↦ S * Real.exp ((r - σ ^ 2 / 2) * T) *
      (σ * Real.sqrt T) * (Real.exp (σ * Real.sqrt T * x) * x * gaussianPDFReal 0 1 x))
      (Set.Ioi (-bsd2 S K r σ T)) volume := by
    refine ((integrable_id_mul_gaussianPDFReal_m_volume (σ * Real.sqrt T)).const_mul
      (S * Real.exp ((r - σ ^ 2 / 2) * T) * (σ * Real.sqrt T) *
        Real.exp ((σ * Real.sqrt T) ^ 2 / 2))).integrableOn.congr_fun ?_ measurableSet_Ioi
    intro x _
    show S * Real.exp ((r - σ ^ 2 / 2) * T) * (σ * Real.sqrt T) *
        Real.exp ((σ * Real.sqrt T) ^ 2 / 2) * (x * gaussianPDFReal (σ * Real.sqrt T) 1 x)
      = S * Real.exp ((r - σ ^ 2 / 2) * T) * (σ * Real.sqrt T) *
        (Real.exp (σ * Real.sqrt T * x) * x * gaussianPDFReal 0 1 x)
    rw [mul_comm (Real.exp (σ * Real.sqrt T * x)) x,
      mul_assoc x (Real.exp (σ * Real.sqrt T * x)) (gaussianPDFReal 0 1 x),
      exp_mul_gaussianPDFReal_zero_one]
    ring
  have hintB : IntegrableOn (fun x : ℝ ↦ K * (σ * Real.sqrt T) *
      (x * gaussianPDFReal 0 1 x)) (Set.Ioi (-bsd2 S K r σ T)) volume :=
    (integrable_id_mul_gaussianPDFReal_volume.integrableOn.const_mul
      (K * (σ * Real.sqrt T)))
  rw [show (fun ω : Ω ↦ likelihoodRatioDeltaPayoff S K r σ T (Z ω))
        = (fun z : ℝ ↦ likelihoodRatioDeltaPayoff S K r σ T z) ∘ Z from rfl,
    hZ.integral_comp hmeas,
    integral_gaussianReal_eq_integral_smul (one_ne_zero : (1 : ℝ≥0) ≠ 0), hsplit,
    integral_indicator measurableSet_Ioi, integral_const_mul, integral_sub hintA hintB,
    integral_const_mul, integral_const_mul, integral_exp_mul_gaussianPDFReal_id_Ioi,
    integral_id_mul_gaussianPDFReal_Ioi,
    sqrtT_add_bsd2_eq_bsd1 S K r σ T,
    show (gaussianPDFReal (σ * Real.sqrt T) 1 (-bsd2 S K r σ T)
          = gaussianPDFReal 0 1 (-(bsd1 S K r σ T))) from by
      rw [gaussianPDFReal_sub_center]; congr 1; simp only [bsd2]; ring,
    gaussianPDFReal_zero_one_neg,
    show (gaussianPDFReal 0 1 (-bsd2 S K r σ T) = gaussianPDFReal 0 1 (bsd2 S K r σ T)) from
      gaussianPDFReal_zero_one_neg _]
  have hXYE : Real.exp (-r * T) * Real.exp ((r - σ ^ 2 / 2) * T)
      * Real.exp ((σ * Real.sqrt T) ^ 2 / 2) = 1 := by
    rw [mul_assoc, ← Real.exp_add, ← Real.exp_add,
      show (σ * Real.sqrt T) ^ 2 = σ ^ 2 * T from by
        rw [mul_pow, Real.sq_sqrt hT.le],
      show -r * T + ((r - σ ^ 2 / 2) * T + σ ^ 2 * T / 2) = 0 from by ring]
    exact Real.exp_zero
  have hMagic : S * gaussianPDFReal 0 1 (bsd1 S K r σ T)
      = Real.exp (-r * T) * K * gaussianPDFReal 0 1 (bsd2 S K r σ T) := by
    have hbi := bs_identity (r := r) hS hK hσ hT
    rw [show Real.exp (-(r * T)) = Real.exp (-r * T) from by rw [neg_mul]] at hbi
    rw [mul_comm K (Real.exp (-r * T))] at hbi
    exact hbi
  have hSD : S * (σ ^ 2 * T) ≠ 0 :=
    mul_ne_zero hS.ne' (mul_ne_zero (pow_ne_zero 2 hσ.ne') hT.ne')
  rw [mul_assoc S (σ ^ 2) T, div_mul_eq_mul_div, div_eq_iff hSD, ← hsq]
  linear_combination (S * (σ * Real.sqrt T) * (σ * Real.sqrt T) * Phi (bsd1 S K r σ T)
      + S * (σ * Real.sqrt T) * gaussianPDFReal 0 1 (bsd1 S K r σ T)) * hXYE
    + (σ * Real.sqrt T) * hMagic

/-! ### The delta of the Black–Scholes market price -/

/-- **The delta of the Black–Scholes market price.** The price of the European call in the
Black–Scholes market, as a function of the initial spot, is differentiable, and its
derivative is the Black–Scholes delta `Φ(d₁)` — the pathwise and likelihood-ratio estimators
of this module estimate exactly this derivative (`pathwiseDelta_deriv`,
`likelihoodRatioDeltaPayoff_mean`). -/
theorem hasDerivAt_marketPrice_S {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {W : ℝ≥0 → Ω → ℝ} (hW : IsPreBrownianReal W μ)
    (hWmeas : ∀ t, Measurable (W t)) {m r : ℝ} {K : ℝ} {T H : ℝ≥0}
    (hTH : T ≤ H) {S : ℝ} (hS : 0 < S) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < (T : ℝ)) :
    HasDerivAt (fun S' : ℝ ↦ (Contracts.BlackScholes.market μ hWmeas S' m r σ).price
        (Contracts.BlackScholes.constGirsanovMeasure hW hWmeas ((m - r) / σ) H)
        (Contracts.europeanCall K T))
      (Phi (bsd1 S K r σ T)) S := by
  have hEq : (fun S' : ℝ ↦ (Contracts.BlackScholes.market μ hWmeas S' m r σ).price
        (Contracts.BlackScholes.constGirsanovMeasure hW hWmeas ((m - r) / σ) H)
        (Contracts.europeanCall K T))
      =ᶠ[nhds S] (fun S' : ℝ ↦ bsV K r σ S' T) := by
    filter_upwards [(eventually_gt_nhds hS)] with S' hS'
    simp only [bsV]
    rw [show Real.exp (-(r * (T : ℝ))) = Real.exp (-r * (T : ℝ)) from by rw [neg_mul]]
    exact Contracts.BlackScholes.price_europeanCall_constGirsanovMeasure (m := m) (r := r)
      hW hWmeas hTH hS' hK hσ hT
  exact (hasDerivAt_bsV_S hK hσ hS hT).congr_of_eventuallyEq hEq

end MathFin

