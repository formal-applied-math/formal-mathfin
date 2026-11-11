/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Models.BlackScholes.Market
public import MathFin.Pricing.Market
public import MathFin.Probability.Martingales.TimeChange

/-!
# The Black–Scholes market with a deterministic volatility clock

The simplest local-volatility market, `σ(t, S) = σ(t)`: a deterministic term structure of
volatility, written through its **total variance** `v(t) = ∫₀ᵗ σ²` as a time change of the
Black–Scholes market of `Models/BlackScholes/Market.lean`. For a pre-Brownian motion `W` under the
physical measure `μ` and a monotone clock `v : ℝ≥0 → ℝ≥0`, the market (`TimeDepVol.market`) has the
information `𝓕 (v t)` that `W` generates up to the clock time `v t` (`Filtration.comp`), the money
market `e^{rt}` as numéraire, and the traded asset

  `S_t = e^{rt} · S₀ exp((θ − 1/2) v(t) + W_{v(t)})`.

When `v` has the derivative `σ²`, this is the diffusion `dS = S ((r + θ σ²) dt + σ dB)` with
`B = ∫ σ⁻¹ dW_v`, a market price of risk `θ σ(t)` proportional to the volatility, and the
Black–Scholes market is the clock `v(t) = σ² t`. That `S` solves this equation is not proved or
used: the market is *defined* as the clocked exponential above, and `v` is only asked to be
monotone (no differentiability, no `v 0 = 0`; with `v 0 = 0` the spot is `S₀`).

The Girsanov measure of the constant price of risk `θ` of `W` at a horizon `H`
(`BlackScholes.constGirsanovMeasure`) is a pricing measure at every horizon `T` with `v T ≤ H`
(`isPricingMeasure_constGirsanovMeasure`): it is the Black–Scholes socket at the clock times, read
along the monotone time change (`Martingale.comp`), and the equivalence with `μ` on `𝓕 (v T)` is
the Black–Scholes one. Under it the European call is worth the Black–Scholes formula with the
total variance `v(T)` in the place of `σ² T` (`price_europeanCall_constGirsanovMeasure`), the
term-structure-of-volatility call price, at the strike `K e^{−rT}` of the deflated asset.

Not covered: a general `σ(t, S)`, whose asset needs the existence of the SDE's solution, a
non-constant price of risk in the clock, and the uniqueness of the pricing measure.

## Main definitions

* `MathFin.Contracts.TimeDepVol.market`: the Black–Scholes market of the clock `v`, spot `S₀`, rate
  `r` and price of risk `θ`.

## Main results

* `MathFin.Contracts.TimeDepVol.deflated_market`: the deflated asset is the Black–Scholes asset
  `S₀ exp((θ − 1/2) u + W_u)` at the clock time `u = v t`.
* `MathFin.Contracts.TimeDepVol.isPricingMeasure_constGirsanovMeasure`: the Girsanov measure of `θ`
  at a horizon `H` is a pricing measure of the market at every `T` with `v T ≤ H`.
* `MathFin.Contracts.TimeDepVol.price_europeanCall_constGirsanovMeasure`: under it the European
  call at `T` is worth `S₀ Φ(d₁) − K e^{−rT} Φ(d₂)` with `d₁, d₂` of the total variance `v(T)`.

## References

* [F. Black and M. Scholes, *The pricing of options and corporate liabilities*][BlackScholes1973]
* [S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*][ShreveSCFII], 5.2
* [J. Gatheral, *The Volatility Surface: A Practitioner's Guide*][Gatheral2006]

## Tags

time-dependent volatility, term structure of volatility, total variance, time change, pricing
measure, Girsanov theorem, local volatility, MSC 91G20, MSC 60G44, JEL G13
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal
open MathFin ItoIntegralL2 ItoIntegralProcessContinuousModification

namespace MathFin.Contracts.TimeDepVol

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {W : ℝ≥0 → Ω → ℝ}

/-- **The Black–Scholes market with the deterministic volatility clock `v`** under the physical
measure `μ`: the information of `W` up to the clock time `v t`, the asset
`e^{rt} S₀ exp((θ − 1/2) v(t) + W_{v(t)})` and the money market `e^{rt}` as numéraire. -/
noncomputable def market (μ : Measure Ω) (hWmeas : ∀ t, Measurable (W t)) (S_0 r θ : ℝ)
    {v : ℝ≥0 → ℝ≥0} (hv : Monotone v) : Market Unit Ω where
  P := μ
  𝓕 := (natFiltration hWmeas).comp hv
  asset i t ω := Real.exp (r * t) * BlackScholes.pathAssets S_0 θ 1 W i (v t) ω
  numeraire t _ := Real.exp (r * t)
  numeraire_pos _ _ := Real.exp_pos _
  asset_adapted i t :=
    ((BlackScholes.market μ hWmeas S_0 θ 0 1).asset_adapted i (v t)).const_mul (Real.exp (r * t))
  numeraire_adapted _ := stronglyMeasurable_const

section Market

variable (μ : Measure Ω) (hWmeas : ∀ t, Measurable (W t)) (S_0 r θ : ℝ)
  {v : ℝ≥0 → ℝ≥0} (hv : Monotone v)

/-- The deflator of the clocked market is the discount `e^{−rt}`. -/
theorem deflator_market (t : ℝ≥0) (ω : Ω) :
    (market μ hWmeas S_0 r θ hv).deflator t ω = Real.exp (-r * t) :=
  Market.deflator_of_numeraire_exp (fun _ _ ↦ rfl) t ω

/-- The deflated asset of the clocked market is the Black–Scholes asset
`S₀ exp((θ − 1/2) u + W_u)` at the clock time `u = v t`. -/
theorem deflated_market (t : ℝ≥0) (ω : Ω) :
    (market μ hWmeas S_0 r θ hv).deflated () t ω
      = BlackScholes.pathAssets S_0 θ 1 W () (v t) ω :=
  mul_div_cancel_left₀ _ (Real.exp_ne_zero _)

end Market

variable {μ : Measure Ω} [IsProbabilityMeasure μ] (hW : IsPreBrownianReal W μ)
  (hWmeas : ∀ t, Measurable (W t)) {S_0 r θ : ℝ} {v : ℝ≥0 → ℝ≥0} (hv : Monotone v)

/-- **The Girsanov measure of the constant price of risk is a pricing measure of the clocked
market.** At a horizon `H` it prices the market at every `T` with `v T ≤ H`: it is a pricing
measure of the Black–Scholes market with `σ = 1`, rate `0` and drift `θ` at the horizon `v T`
(`BlackScholes.isPricingMeasure_constGirsanovMeasure`), whose deflated asset frozen at `v T`, read
along the monotone clock `v` (`Martingale.comp`), is the deflated asset of the clocked market
frozen at `T`. -/
theorem isPricingMeasure_constGirsanovMeasure {T H : ℝ≥0} (hTH : v T ≤ H) :
    (market μ hWmeas S_0 r θ hv).IsPricingMeasure T
      (BlackScholes.constGirsanovMeasure hW hWmeas θ H) := by
  have h := BlackScholes.isPricingMeasure_constGirsanovMeasure hW hWmeas (S_0 := S_0) (m := θ)
    (r := 0) one_ne_zero hTH
  rw [sub_zero, div_one] at h
  refine ⟨h.isProb, h.ac, h.ac', fun _ ↦ ?_⟩
  have hf : (fun t ↦ (market μ hWmeas S_0 r θ hv).deflated () (min t T)) =
      fun t ↦ (BlackScholes.market μ hWmeas S_0 θ 0 1).deflated () (min (v t) (v T)) := by
    funext t ω
    rw [deflated_market, hv.map_min, BlackScholes.deflated_market]
    simp only [BlackScholes.pathAssets, sub_zero]
  rw [hf]
  exact (h.martingale ()).comp hv

/-- **The European call in the clocked market** is worth the Black–Scholes formula of the total
variance `v(T)`: `S₀ Φ(d₁) − K' Φ(d₂)` for the deflated strike `K' = K e^{−rT}`, with `σ = 1`,
rate `0` and maturity `v(T)`, under the Girsanov pricing measure of `θ` at a horizon `H ≥ v(T)`
(`isPricingMeasure_constGirsanovMeasure`), whatever `θ`. The call pays `(S_T − K)⁺` with
`S_T = e^{rT} S₀ exp((θ − 1/2) v(T) + W_{v(T)})` and is discounted by `e^{−rT}`, so its price is
that of the Black–Scholes call on the deflated asset, `value_europeanCall_physical`. -/
theorem price_europeanCall_constGirsanovMeasure {K : ℝ} {T H : ℝ≥0} (hTH : v T ≤ H)
    (hS₀ : 0 < S_0) (hK : 0 < K) (hT : 0 < (v T : ℝ)) :
    (market μ hWmeas S_0 r θ hv).price (BlackScholes.constGirsanovMeasure hW hWmeas θ H)
        (europeanCall K T)
      = S_0 * Phi (bsd1 S_0 (K * Real.exp (-r * T)) 0 1 (v T))
        - K * Real.exp (-r * T) * Phi (bsd2 S_0 (K * Real.exp (-r * T)) 0 1 (v T)) := by
  have hBS := BlackScholes.value_europeanCall_physical hW hWmeas (S_0 := S_0) (m := θ) (r := 0)
    (σ := 1) (K := K * Real.exp (-r * T)) hTH hS₀ (mul_pos hK (Real.exp_pos _)) one_pos hT
  rw [sub_zero, div_one, europeanCall, Contract.value_pay] at hBS
  have hmax (x : ℝ) : Real.exp (-r * T) * max (Real.exp (r * T) * x - K) 0
      = max (x - K * Real.exp (-r * T)) 0 := by
    have h : Real.exp (-r * T) * Real.exp (r * T) = 1 := by
      rw [← Real.exp_add]; simp
    rw [mul_max_of_nonneg _ _ (Real.exp_pos _).le, mul_zero]
    congr 1
    linear_combination x * h
  have hint : ∫ ω, (market μ hWmeas S_0 r θ hv).deflator T ω *
        (europeanCallPayoff K T).eval (scenarioAt (market μ hWmeas S_0 r θ hv).asset ω)
          ∂BlackScholes.constGirsanovMeasure hW hWmeas θ H
      = ∫ ω, Real.exp (-(0 : ℝ) * (v T : ℝ)) *
        (europeanCallPayoff (K * Real.exp (-r * T)) (v T)).eval
          (scenarioAt (BlackScholes.pathAssets S_0 θ 1 W) ω)
          ∂BlackScholes.constGirsanovMeasure hW hWmeas θ H := by
    refine integral_congr_ae (.of_forall fun ω ↦ ?_)
    simp only [deflator_market]
    simp only [europeanCallPayoff, Payoff.eval, scenarioAt, market]
    rw [hmax]
    simp
  rw [Market.price, europeanCall, Contract.value_pay]
  refine hint.trans (hBS.trans ?_)
  simp

end MathFin.Contracts.TimeDepVol
