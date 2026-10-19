/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib
public import MathFin.FixedIncome.Vasicek
public import MathFin.FixedIncome.VasicekSDEGaussian

/-!
# Schwartz one-factor commodity futures

In the Schwartz (1997) one-factor model the log spot price of a commodity is
mean-reverting under the pricing measure:

  `d ln S_t = κ(θ − ln S_t) dt + σ dB_t`.

This is the Ornstein–Uhlenbeck dynamics of the Vasicek short rate, so, carrying
`ln S_T` in its Wiener representation (the SDE bridge is cited, not proven — see
`schwartzFuturesPrice_eq_integral`), it has the Gaussian law `N(m_T, v_T)` with
`m_T = vasicekSDEMean` and `v_T = vasicekSDEVariance` (`vasicekShortRate_hasLaw_gaussian`).
The futures
price is `F(0,T) = E[S_T] = E[e^{ln S_T}]`, the Gaussian moment-generating
function at `1`:

  `F(0,T) = exp(m_T + v_T / 2)`.

As `T → ∞` the futures curve flattens to `exp(θ + σ² / (4κ))`, independent of
the current spot.

This formalizes only the constant-parameter Schwartz (1997) model; Hull's
time-dependent level `q(t)` (the Hull-White-form drift calibrated to the
quoted futures curve, OFOD ch. 35) is out of scope.

## Main results

* `schwartzFuturesPrice` — the closed form `exp(m_T + v_T / 2)`.
* `schwartzFuturesPrice_eq_integral` — it equals `E[S_T]` for the log spot in its
  Wiener representation (the SDE bridge is cited, not proven).
* `schwartzFuturesPrice_tendsto` — the long-maturity flattening limit.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped NNReal
open WienerIntegralL2

/-- **Schwartz one-factor futures price** with initial log spot `x₀`, long-run
log level `θ`, mean-reversion speed `κ`, volatility `σ` and maturity `T`:
`exp(m_T + v_T / 2)`, the lognormal mean of the terminal spot. -/
noncomputable def schwartzFuturesPrice (x₀ θ κ σ T : ℝ) : ℝ :=
  Real.exp (vasicekSDEMean x₀ θ κ T + vasicekSDEVariance σ κ T / 2)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {B : ℝ≥0 → Ω → ℝ}

/-- **Schwartz futures price = expected terminal spot.** With the log spot
carried in its Wiener representation `ln S_T = m_T + σ ∫₀ᵀ e^{−κ(T−s)} dB_s`
(the OU solution representation, as in `mf-vasicek-sde-terminal-gaussian` —
the modelling bridge from the SDE is cited, not proven here), `E[S_T] =
schwartzFuturesPrice`. -/
theorem schwartzFuturesPrice_eq_integral (hB : IsPreBrownianReal B μ)
    (x₀ θ σ : ℝ) {κ : ℝ} (hκ : 0 < κ) (T : ℝ≥0) :
    ∫ ω, Real.exp (vasicekSDEMean x₀ θ κ (T : ℝ)
        + σ * (wienerIntegralLp B hB T (vasicekKernelLp κ hκ.le T) ω)) ∂μ
      = schwartzFuturesPrice x₀ θ κ σ T := by
  have h := mgf_gaussianReal (vasicekShortRate_hasLaw_gaussian hB x₀ θ σ hκ T).map_eq 1
  simp only [mgf, one_mul, mul_one, one_pow] at h
  rw [h, schwartzFuturesPrice, Real.coe_toNNReal _ (vasicekSDEVariance_nonneg σ hκ T.coe_nonneg)]

/-- **Long-maturity flattening**: as `T → ∞` the Schwartz futures price tends
to `exp(θ + σ² / (4κ))`, independent of the initial spot. -/
theorem schwartzFuturesPrice_tendsto (x₀ θ σ : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (schwartzFuturesPrice x₀ θ κ σ) atTop
      (𝓝 (Real.exp (θ + σ ^ 2 / (4 * κ)))) := by
  have hm : Tendsto (fun t ↦ vasicekSDEMean x₀ θ κ t) atTop (𝓝 θ) :=
    (vasicekDeterministic_tendsto_mean x₀ θ κ hκ).congr fun t ↦ by
      unfold vasicekDeterministic vasicekSDEMean; ring
  have he : Tendsto (fun t : ℝ ↦ Real.exp (-(2 * κ * t))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Tendsto.const_mul_atTop (by positivity) tendsto_id)
  have hv : Tendsto (fun t ↦ vasicekSDEVariance σ κ t) atTop (𝓝 (σ ^ 2 / (2 * κ))) := by
    unfold vasicekSDEVariance
    simpa using ((he.const_sub 1).const_mul (σ ^ 2)).div_const (2 * κ)
  have hlim : θ + σ ^ 2 / (2 * κ) / 2 = θ + σ ^ 2 / (4 * κ) := by ring
  rw [← hlim]
  exact Real.continuous_exp.tendsto _ |>.comp (hm.add (hv.div_const 2))

end MathFin
