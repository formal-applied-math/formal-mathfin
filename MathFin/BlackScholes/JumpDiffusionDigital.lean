/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.BlackScholes.JumpDiffusionDensity
public import MathFin.BlackScholes.JumpDiffusionBrownian
public import MathFin.BlackScholes.CallSpreadDigital
public import MathFin.BlackScholes.StrikeGreeks
public import MathFin.BlackScholes.BreedenLitzenberger
public import MathFin.BlackScholes.JumpDiffusionMerton
public import MathFin.BlackScholes.MertonStrikeGreeks

/-!
# Digital options in a jump-diffusion, and Breeden–Litzenberger with jumps

The cash-or-nothing digital pays `1` when the price ends above the strike. Its price function,
`D(S, K, τ) = e^{−rτ}P(Se^Y > K)` with `Y` the log-return over `τ`, is `jumpDiffusionDigitalPrice`.
With a Gaussian part (`σ ≠ 0`, `τ > 0`) the log-return law has a continuous density `f` and no
atoms (`BlackScholes/JumpDiffusionDensity.lean`). So, for a spot `S > 0`:

* `hasDerivAt_jumpDiffusionCallPrice_strike`: with a finite forward, the call price function is
  differentiable in the strike at every `K`, and `∂C/∂K = −D`. This is the general strike
  derivative `hasDerivAt_integral_call` (any law with no atom at the strike) for the price `Seʸ`.
* `hasDerivAt_jumpDiffusionDigitalPrice_strike`: at a strike `K > 0`,
  `∂D/∂K = −e^{−rτ}f(log(K/S))/K`. Here `f(log(K/S))/K` is minus the strike derivative of
  `P(Seʸ > K)`, the density of the price at `K`.
* `breedenLitzenberger_jumpDiffusion`: Breeden–Litzenberger with jumps. With a finite forward,
  `∂²C/∂K² = e^{−rτ}f(log(K/S))/K`, the discounted density of the price.
* `jumpDiffusionDigitalPrice_zero` and `jumpDiffusionDensity_div_eq_lognormalTerminalPDF`: without
  jumps, at the drift `r − σ²/2` and `σ > 0`, the digital price is `e^{−rτ}Φ(d₂)` and the density
  of the price is `lognormalTerminalPDF`. Both are read off derivatives of the Black–Scholes price
  (`hasDerivAt_bsV_K`, `breedenLitzenberger`) through the uniqueness of derivatives, not computed.
  The first agrees with `bs_cash_or_nothing_formula`, which computes it as a Gaussian integral; the
  second shows that the formula of `BreedenLitzenberger.lean` is the density of the price.
* `jumpDiffusionDigitalPrice_gaussian_eq_mertonDigitalPrice`: with log-jumps
  `N(log(1 + k) − δ²/2, δ²)` (`k > −1`) at the compensated drift `r − σ²/2 − Λk`, for `σ > 0` and
  `K > 0`, the digital price is Merton's series `mertonDigitalPrice` at the expected jump count
  `Λτ`, a Poisson mixture of Black–Scholes digitals.
* `jumpDiffusionDensity_gaussian_div_eq_mertonTerminalPDF`: with the same jumps and any drift `b`,
  the density of the price is `mertonTerminalPDF`, a Poisson mixture of lognormal density formulas,
  at the parameter `r = b + σ²/2 + Λk`. Both are read off the strike derivatives of Merton's call
  series (`MertonStrikeGreeks.lean`) through the uniqueness of derivatives.

Without a Gaussian part the law has an atom at `bτ`, the no-jump outcome, and the call price has a
kink there: `differentiableAt_jumpDiffusionCallPrice_strike_iff` (differentiable at `K` iff the law
has no atom at `log(K/S)`) and `not_differentiableAt_jumpDiffusionCallPrice_strike` (`σ = 0`, the
strike `Se^{bτ}`). The one-sided strike derivatives are those of `tendsto_call_spread` and
`tendsto_call_spread_left`.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real Filter Set
open scoped NNReal Topology

/-- **The digital price function** of a jump-diffusion: the cash-or-nothing digital paying `1`
when the price ends above the strike, discounted at the rate `r` and integrated against the
log-return law over `τ`, `D = ∫ e^{−rτ}1_{Seʸ > K} dμ_τ(y)`. -/
noncomputable def jumpDiffusionDigitalPrice (S K r b σ : ℝ) (Λ : ℝ≥0) (ν : Measure ℝ) (τ : ℝ≥0) :
    ℝ :=
  ∫ y, rexp (-r * τ) * (Ioi K).indicator (fun _ ↦ (1 : ℝ)) (S * rexp y)
    ∂(jumpDiffusionIncrementLaw b σ Λ ν τ)

/-- The digital price is the discounted probability that the price ends above the strike,
`D = e^{−rτ}P(Se^Y > K)`. -/
lemma jumpDiffusionDigitalPrice_eq (S K r b σ : ℝ) (Λ : ℝ≥0) (ν : Measure ℝ) (τ : ℝ≥0) :
    jumpDiffusionDigitalPrice S K r b σ Λ ν τ
      = rexp (-r * τ) * (jumpDiffusionIncrementLaw b σ Λ ν τ).real {y | K < S * rexp y} := by
  have hset : MeasurableSet {y : ℝ | K < S * rexp y} :=
    measurableSet_lt measurable_const (by fun_prop)
  rw [jumpDiffusionDigitalPrice, integral_const_mul, ← integral_indicator_one hset]
  -- the two indicators agree pointwise by definition
  congr 1

/-- **The strike derivative of the jump-diffusion call price is minus the digital price.** With a
Gaussian part (`σ ≠ 0`, `τ > 0`), a spot `S > 0` and a finite forward, the call price function is
differentiable in the strike at every `K`, and `∂C/∂K = −D`. The law has no atoms
(`nullSingletonClass_jumpDiffusionIncrementLaw`), so the general strike derivative
`hasDerivAt_integral_call` applies to the price `Seʸ`. -/
theorem hasDerivAt_jumpDiffusionCallPrice_strike {S r b σ : ℝ} (hS : 0 < S) (hσ : σ ≠ 0)
    {Λ : ℝ≥0} {ν : Measure ℝ} [IsProbabilityMeasure ν] {τ : ℝ≥0}
    (hY : Integrable rexp (jumpDiffusionIncrementLaw b σ Λ ν τ)) (hτ : 0 < τ) (K : ℝ) :
    HasDerivAt (fun k ↦ jumpDiffusionCallPrice S k r b σ Λ ν τ)
      (-jumpDiffusionDigitalPrice S K r b σ Λ ν τ) K := by
  have := nullSingletonClass_jumpDiffusionIncrementLaw b hσ Λ ν hτ
  -- the price `Seʸ` has no atom at `K`, since `y ↦ Seʸ` is injective
  have hK : jumpDiffusionIncrementLaw b σ Λ ν τ {y | S * rexp y = K} = 0 :=
    Set.Subsingleton.measure_zero (fun y₁ (h₁ : S * rexp y₁ = K) y₂ (h₂ : S * rexp y₂ = K) ↦
      Real.exp_injective (mul_left_cancel₀ hS.ne' (h₁.trans h₂.symm))) _
  have h := (hasDerivAt_integral_call (by fun_prop : Measurable fun y ↦ S * rexp y)
    (hY.const_mul S) hK).const_mul (rexp (-r * τ))
  have hC : (fun k ↦ jumpDiffusionCallPrice S k r b σ Λ ν τ)
      = fun k ↦ rexp (-r * τ)
          * ∫ y, max (S * rexp y - k) 0 ∂(jumpDiffusionIncrementLaw b σ Λ ν τ) := by
    funext k
    rw [jumpDiffusionCallPrice, integral_const_mul]
  rw [hC, jumpDiffusionDigitalPrice_eq, ← mul_neg]
  exact h

/-- Without jumps the log-return is Gaussian (`jumpDiffusionIncrementLaw_zero`), so its forward is
finite. -/
lemma integrable_exp_jumpDiffusionIncrementLaw_zero (b σ : ℝ) (ν : Measure ℝ)
    [IsProbabilityMeasure ν] (τ : ℝ≥0) : Integrable rexp (jumpDiffusionIncrementLaw b σ 0 ν τ) := by
  rw [jumpDiffusionIncrementLaw_zero]
  exact integrable_exp_gaussianReal _ _

/-- **Without jumps, at the drift `r − σ²/2`, the digital price is `e^{−rτ}Φ(d₂)`** (for `σ > 0`,
`S, K > 0` and `τ > 0`), read off the strike derivative of the call. The digital price is minus
the strike derivative of the call price
(`hasDerivAt_jumpDiffusionCallPrice_strike`). Near `K` the call price is the Black–Scholes price
(`jumpDiffusionCallPrice_zero`), whose strike derivative is `−e^{−rτ}Φ(d₂)` (`hasDerivAt_bsV_K`).
It agrees with `bs_cash_or_nothing_formula`, which computes the value as a Gaussian integral. -/
theorem jumpDiffusionDigitalPrice_zero {S K r σ : ℝ} (hS : 0 < S) (hK : 0 < K) (hσ : 0 < σ)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {τ : ℝ≥0} (hτ : 0 < τ) :
    jumpDiffusionDigitalPrice S K r (r - σ ^ 2 / 2) σ 0 ν τ
      = rexp (-r * τ) * Phi (bsd2 S K r σ τ) := by
  have hY := integrable_exp_jumpDiffusionIncrementLaw_zero (r - σ ^ 2 / 2) σ ν τ
  have h₂ : HasDerivAt (fun k ↦ jumpDiffusionCallPrice S k r (r - σ ^ 2 / 2) σ 0 ν τ)
      (-(rexp (-(r * τ)) * Phi (bsd2 S K r σ τ))) K :=
    (hasDerivAt_bsV_K hS hσ hK (NNReal.coe_pos.2 hτ)).congr_of_eventuallyEq
      (eventually_of_mem (Ioi_mem_nhds hK) fun k hk ↦ jumpDiffusionCallPrice_zero hS hk hσ ν hτ)
  rw [neg_mul]
  exact neg_injective ((hasDerivAt_jumpDiffusionCallPrice_strike hS hσ.ne' hY hτ K).unique h₂)

/-- **The strike derivative of the digital price is minus the discounted density of the price.**
With a Gaussian part (`σ ≠ 0`, `τ > 0`), a spot `S > 0` and a strike `K > 0`,
`∂D/∂K = −e^{−rτ}f(log(K/S))/K`, with `f` the density of the log-return. Here `f(log(K/S))/K` is
minus the strike derivative of `P(Seʸ > K) = P(Y > log(K/S))`, the density of the price at `K`:
the tail of a law with a continuous density (`hasDerivAt_measureReal_Ioi_withDensity`) composed
with `k ↦ log(k/S)`. -/
theorem hasDerivAt_jumpDiffusionDigitalPrice_strike {S r b σ : ℝ} (hS : 0 < S) (hσ : σ ≠ 0)
    {Λ : ℝ≥0} {ν : Measure ℝ} [IsProbabilityMeasure ν] {τ : ℝ≥0} (hτ : 0 < τ) {K : ℝ}
    (hK : 0 < K) :
    HasDerivAt (fun k ↦ jumpDiffusionDigitalPrice S k r b σ Λ ν τ)
      (-(rexp (-r * τ) * (jumpDiffusionDensity b σ Λ ν τ (Real.log (K / S)) / K))) K := by
  have hlaw := jumpDiffusionIncrementLaw_eq_withDensity b hσ Λ ν hτ
  have htail := hasDerivAt_measureReal_Ioi_withDensity
    (integrable_jumpDiffusionDensity b hσ Λ ν hτ) (jumpDiffusionDensity_nonneg b σ Λ ν τ)
    (a := Real.log (K / S)) (continuous_jumpDiffusionDensity b σ Λ ν τ).continuousAt
  have hlog : HasDerivAt (fun k ↦ Real.log (k / S)) (1 / K) K := by
    have h := ((hasDerivAt_id' K).div_const S).log (div_pos hK hS).ne'
    have hS' := hS.ne'
    have hK' := hK.ne'
    convert h using 1
    field_simp
  -- `P(Seʸ > k) = P(Y > log(k/S))` for `k > 0`
  have hset (k : ℝ) (hk : 0 < k) : {y | k < S * rexp y} = Ioi (Real.log (k / S)) := by
    ext y
    rw [mem_ofPred_eq, mem_Ioi, Real.log_lt_iff_lt_exp (div_pos hk hS), div_lt_iff₀ hS,
      mul_comm]
  have heq : ∀ᶠ k in 𝓝 K, jumpDiffusionDigitalPrice S k r b σ Λ ν τ
      = rexp (-r * τ) * (volume.withDensity fun y ↦
          ENNReal.ofReal (jumpDiffusionDensity b σ Λ ν τ y)).real (Ioi (Real.log (k / S))) := by
    filter_upwards [Ioi_mem_nhds hK] with k hk
    rw [jumpDiffusionDigitalPrice_eq, hset k hk, hlaw]
  exact (((htail.comp K hlog).const_mul (rexp (-r * τ))).congr_of_eventuallyEq heq).congr_deriv
    (by ring)

/-- **Breeden–Litzenberger with jumps.** With a Gaussian part (`σ ≠ 0`, `τ > 0`), a spot `S > 0`
and a finite forward, the second strike derivative of the call price at `K > 0` is the discounted
density of the price, `∂²C/∂K² = e^{−rτ}f(log(K/S))/K`. The first derivative is minus the digital
price (`hasDerivAt_jumpDiffusionCallPrice_strike`), and the digital's derivative is minus the
discounted density (`hasDerivAt_jumpDiffusionDigitalPrice_strike`). -/
theorem breedenLitzenberger_jumpDiffusion {S r b σ : ℝ} (hS : 0 < S) (hσ : σ ≠ 0)
    {Λ : ℝ≥0} {ν : Measure ℝ} [IsProbabilityMeasure ν] {τ : ℝ≥0}
    (hY : Integrable rexp (jumpDiffusionIncrementLaw b σ Λ ν τ)) (hτ : 0 < τ) {K : ℝ}
    (hK : 0 < K) :
    HasDerivAt (deriv fun k ↦ jumpDiffusionCallPrice S k r b σ Λ ν τ)
      (rexp (-r * τ) * (jumpDiffusionDensity b σ Λ ν τ (Real.log (K / S)) / K)) K :=
  hasDerivAt_deriv_of_eventually
    (Eventually.of_forall fun x ↦ hasDerivAt_jumpDiffusionCallPrice_strike (r := r) hS hσ hY hτ x)
    ((hasDerivAt_jumpDiffusionDigitalPrice_strike (r := r) (b := b) (Λ := Λ) (ν := ν) hS hσ hτ
      hK).fun_neg.congr_deriv (neg_neg _))

/-- **Without jumps, at the drift `r − σ²/2`, the density of the price is the lognormal density**
`lognormalTerminalPDF` (for `σ > 0`, `S, K > 0` and `τ > 0`). The second strike derivative of the
call price is `e^{−rτ}f(log(K/S))/K` (`breedenLitzenberger_jumpDiffusion`) and also
`e^{−rτ}·lognormalTerminalPDF` (`breedenLitzenberger`, the call price being `bsV` near `K`,
`jumpDiffusionCallPrice_zero`). So the lognormal formula of `BreedenLitzenberger.lean` is the
density of the price at `K`, read off the uniqueness of derivatives rather than computed. -/
theorem jumpDiffusionDensity_div_eq_lognormalTerminalPDF {S K r σ : ℝ} (hS : 0 < S)
    (hK : 0 < K) (hσ : 0 < σ) (ν : Measure ℝ) [IsProbabilityMeasure ν] {τ : ℝ≥0} (hτ : 0 < τ) :
    jumpDiffusionDensity (r - σ ^ 2 / 2) σ 0 ν τ (Real.log (K / S)) / K
      = lognormalTerminalPDF S r σ τ K := by
  have hY := integrable_exp_jumpDiffusionIncrementLaw_zero (r - σ ^ 2 / 2) σ ν τ
  have h₁ := breedenLitzenberger_jumpDiffusion (r := r) hS hσ.ne' hY hτ hK
  -- near `K` the call price function is `bsV`, so the two first derivatives agree near `K`
  have h₂ : HasDerivAt (deriv fun k ↦ jumpDiffusionCallPrice S k r (r - σ ^ 2 / 2) σ 0 ν τ)
      (rexp (-(r * τ)) * lognormalTerminalPDF S r σ τ K) K := by
    refine (breedenLitzenberger hS hσ hK (NNReal.coe_pos.2 hτ)).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hK] with k hk
    exact Filter.EventuallyEq.deriv_eq (eventually_of_mem (Ioi_mem_nhds hk) fun k' hk' ↦
      jumpDiffusionCallPrice_zero hS hk' hσ ν hτ)
  have h := h₁.unique h₂
  rw [neg_mul] at h
  exact mul_left_cancel₀ (Real.exp_pos _).ne' h

/-! ### Gaussian jumps: Merton's digital and Merton's density -/

/-- **Merton's digital formula.** With log-jumps `N(log(1 + k) − δ²/2, δ²)` and the compensated
drift `b = r − σ²/2 − Λk`, for `σ > 0`, `k > −1`, `S, K > 0` and `τ > 0`, the digital price is
Merton's series `mertonDigitalPrice` at the expected jump count `Λτ`, a Poisson mixture of
Black–Scholes digitals. It is read off the uniqueness of derivatives: the digital price is minus
the strike derivative of the call price (`hasDerivAt_jumpDiffusionCallPrice_strike`), and near `K`
the call price is Merton's series (`jumpDiffusionCallPrice_gaussian_eq_mertonCallPrice`), whose
strike derivative is minus Merton's digital series (`hasDerivAt_mertonCallPrice_strike`). -/
theorem jumpDiffusionDigitalPrice_gaussian_eq_mertonDigitalPrice {S K r b σ k δ : ℝ}
    (hS : 0 < S) (hK : 0 < K) (hσ : 0 < σ) (hk : -1 < k) {Λ : ℝ≥0}
    (hb : b = r - σ ^ 2 / 2 - Λ * k) {τ : ℝ≥0} (hτ : 0 < τ) :
    jumpDiffusionDigitalPrice S K r b σ Λ
        (gaussianReal (Real.log (1 + k) - δ ^ 2 / 2) (δ ^ 2).toNNReal) τ
      = mertonDigitalPrice S K r σ τ k δ (Λ * τ) := by
  have hY := integrable_exp_jumpDiffusionIncrementLaw b σ Λ
    (integrable_exp_gaussianReal (Real.log (1 + k) - δ ^ 2 / 2) (δ ^ 2).toNNReal) τ
  -- near `K` the call price function is Merton's series
  have h : HasDerivAt (fun x ↦ jumpDiffusionCallPrice S x r b σ Λ
        (gaussianReal (Real.log (1 + k) - δ ^ 2 / 2) (δ ^ 2).toNNReal) τ)
      (-mertonDigitalPrice S K r σ τ k δ (Λ * τ)) K :=
    (hasDerivAt_mertonCallPrice_strike (r := r) (δ := δ) (Λ := Λ * τ) hS hσ
      (NNReal.coe_pos.2 hτ) hk hK).congr_of_eventuallyEq
      (eventually_of_mem (Ioi_mem_nhds hK) fun x hx ↦
        jumpDiffusionCallPrice_gaussian_eq_mertonCallPrice (δ := δ) hS hx hσ hk hb hτ)
  exact neg_injective
    ((hasDerivAt_jumpDiffusionCallPrice_strike (r := r) hS hσ.ne' hY hτ K).unique h)

/-- **Merton's density.** With log-jumps `N(log(1 + k) − δ²/2, δ²)`, for `σ > 0`, `k > −1`,
`S, K > 0`, `τ > 0` and any drift `b`, the density of the price at `K`, `f(log(K/S))/K`, is
Merton's series `mertonTerminalPDF` at the expected jump count `Λτ` and the parameter
`r = b + σ²/2 + Λk`, a Poisson mixture of lognormal density formulas. At the compensated drift `r`
is the interest rate; the identity holds at every drift because `r` enters the series only through
`d₂`. It is read off the uniqueness of derivatives: the digital price discounted at `r` has strike
derivative `−e^{−rτ}f(log(K/S))/K` (`hasDerivAt_jumpDiffusionDigitalPrice_strike`), and near `K` it
is Merton's digital series (`jumpDiffusionDigitalPrice_gaussian_eq_mertonDigitalPrice`, `b` being
the compensated drift for this `r`), whose strike derivative is `−e^{−rτ}·mertonTerminalPDF`
(`hasDerivAt_mertonDigitalPrice_strike`). -/
theorem jumpDiffusionDensity_gaussian_div_eq_mertonTerminalPDF (b : ℝ) {S K σ k δ : ℝ}
    (hS : 0 < S) (hK : 0 < K) (hσ : 0 < σ) (hk : -1 < k) (Λ : ℝ≥0) {τ : ℝ≥0} (hτ : 0 < τ) :
    jumpDiffusionDensity b σ Λ (gaussianReal (Real.log (1 + k) - δ ^ 2 / 2) (δ ^ 2).toNNReal) τ
        (Real.log (K / S)) / K
      = mertonTerminalPDF S (b + σ ^ 2 / 2 + Λ * k) σ τ k δ (Λ * τ) K := by
  obtain ⟨r, hr⟩ : ∃ r, b + σ ^ 2 / 2 + Λ * k = r := ⟨_, rfl⟩
  rw [hr]
  have hb : b = r - σ ^ 2 / 2 - Λ * k := by rw [← hr]; ring
  have h₁ := hasDerivAt_jumpDiffusionDigitalPrice_strike (r := r) (b := b) (Λ := Λ)
    (ν := gaussianReal (Real.log (1 + k) - δ ^ 2 / 2) (δ ^ 2).toNNReal) hS hσ.ne' hτ hK
  -- near `K` the digital price function is Merton's digital series
  have h₂ : HasDerivAt (fun x ↦ jumpDiffusionDigitalPrice S x r b σ Λ
        (gaussianReal (Real.log (1 + k) - δ ^ 2 / 2) (δ ^ 2).toNNReal) τ)
      (-(rexp (-(r * τ)) * mertonTerminalPDF S r σ τ k δ (Λ * τ) K)) K :=
    (hasDerivAt_mertonDigitalPrice_strike (r := r) (δ := δ) (Λ := Λ * τ) hS hσ
      (NNReal.coe_pos.2 hτ) hk hK).congr_of_eventuallyEq
      (eventually_of_mem (Ioi_mem_nhds hK) fun x hx ↦
        jumpDiffusionDigitalPrice_gaussian_eq_mertonDigitalPrice (δ := δ) hS hx hσ hk hb hτ)
  have h := neg_injective (h₁.unique h₂)
  rw [neg_mul] at h
  exact mul_left_cancel₀ (Real.exp_pos _).ne' h

/-! ### Where the call price is not differentiable in the strike -/

/-- **The call price is differentiable in the strike exactly where the law has no atom.** For a
spot `S > 0`, a strike `K > 0` and a finite forward, the call price function of a jump-diffusion is
differentiable at `K` iff the log-return law has no atom at `log(K/S)`: this is
`differentiableAt_integral_call_iff` for the price `Seʸ`, which equals `K` only at `y = log(K/S)`.
With a Gaussian part there are no atoms (`hasDerivAt_jumpDiffusionCallPrice_strike`). -/
theorem differentiableAt_jumpDiffusionCallPrice_strike_iff {S K r b σ : ℝ} (hS : 0 < S)
    (hK : 0 < K) {Λ : ℝ≥0} {ν : Measure ℝ} [IsProbabilityMeasure ν] {τ : ℝ≥0}
    (hY : Integrable rexp (jumpDiffusionIncrementLaw b σ Λ ν τ)) :
    DifferentiableAt ℝ (fun k ↦ jumpDiffusionCallPrice S k r b σ Λ ν τ) K ↔
      jumpDiffusionIncrementLaw b σ Λ ν τ {Real.log (K / S)} = 0 := by
  -- the price `Seʸ` is `K` exactly at `y = log(K/S)`
  have hset : {y | S * rexp y = K} = {Real.log (K / S)} := by
    ext y
    rw [mem_setOf_eq, mem_singleton_iff]
    constructor
    · rintro rfl
      rw [mul_div_cancel_left₀ _ hS.ne', Real.log_exp]
    · rintro rfl
      have hS' := hS.ne'
      rw [Real.exp_log (div_pos hK hS)]
      field_simp
  have hC : (fun k ↦ jumpDiffusionCallPrice S k r b σ Λ ν τ)
      = fun k ↦ rexp (-r * τ)
          * ∫ y, max (S * rexp y - k) 0 ∂(jumpDiffusionIncrementLaw b σ Λ ν τ) := by
    funext k
    rw [jumpDiffusionCallPrice, integral_const_mul]
  rw [← hset, ← differentiableAt_integral_call_iff (by fun_prop : Measurable fun y ↦ S * rexp y)
    (hY.const_mul S) K, hC]
  -- a nonzero discount factor does not change differentiability
  refine ⟨fun hd ↦ (hd.const_mul (rexp (-r * τ))⁻¹).congr_of_eventuallyEq
    (Eventually.of_forall fun k ↦ ?_), fun hd ↦ hd.const_mul _⟩
  dsimp only
  rw [← mul_assoc, inv_mul_cancel₀ (Real.exp_pos _).ne', one_mul]

/-- **Without a Gaussian part the call price has a kink at the strike `Se^{bτ}`.** With `σ = 0`
and no jump, which has probability `e^{−Λτ} > 0`, the log-return is `bτ`
(`ofReal_exp_le_jumpDiffusionIncrementLaw_singleton`). So the law has an atom at `bτ`, and for a
spot `S > 0` and a finite forward the call price function is not differentiable in the strike at
`Se^{bτ}` (`differentiableAt_jumpDiffusionCallPrice_strike_iff`). -/
theorem not_differentiableAt_jumpDiffusionCallPrice_strike {S r b : ℝ} (hS : 0 < S) {Λ : ℝ≥0}
    {ν : Measure ℝ} [IsProbabilityMeasure ν] {τ : ℝ≥0}
    (hY : Integrable rexp (jumpDiffusionIncrementLaw b 0 Λ ν τ)) :
    ¬ DifferentiableAt ℝ (fun k ↦ jumpDiffusionCallPrice S k r b 0 Λ ν τ) (S * rexp (b * τ)) := by
  rw [differentiableAt_jumpDiffusionCallPrice_strike_iff hS (mul_pos hS (Real.exp_pos _)) hY,
    mul_div_cancel_left₀ _ hS.ne', Real.log_exp]
  exact ((ENNReal.ofReal_pos.2 (Real.exp_pos _)).trans_le
    (ofReal_exp_le_jumpDiffusionIncrementLaw_singleton b Λ ν τ)).ne'

end MathFin
