/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye, Raphael Coelho
-/
module

public import MathFin.Models.BlackScholes.HigherGreeks
public import MathFin.Models.BlackScholes.Market
public import MathFin.Models.StochVol.SABRImpliedVol

/-!
# SABR chain-rule Greeks (at-the-money)

Hagan, Kumar, Lesniewski & Woodward, "Managing Smile Risk," *Wilmott Magazine*,
September 2002, pp. 84-108, §3.2: a European option `V = BS(f, K, σ_B(K, f), t_ex)` (eq. 3.5)
has price sensitivities that combine the ordinary Black-Scholes sensitivity with the vol smile's
own movement, `Δ_SABR = Δ_BS + Λ_BS · ∂σ_B/∂f` (eq. 3.9) and `Λ_SABR^α = Λ_BS · ∂σ_B/∂α`
(eq. 3.6). This file proves the backbone-convention chain rule: the Black call with strike held
fixed at `K = f` and the spot `s` moving, priced at the ATM-vol curve evaluated at the spot,
`σ_ATM(s) = sabrATMVol s α β ρ ν tex` (eq. 2.18 read as a function of the forward alone, the
"backbone" of `SABRImpliedVol.lean`), and the same for `α` moving. The Delta is the Delta under a
"vol re-marks along the backbone" convention.

## Main results

* The general chain rules `hasDerivAt_bsV_S_chainRule` and `hasDerivAt_bsV_param_chainRule`
  (vol a differentiable function of the spot, resp. of a parameter) are in
  `BlackScholes/HigherGreeks.lean`; this file instantiates them at `sabrATMVol`.
* `differentiableAt_sabrATMVol_F`, `differentiableAt_sabrATMVol_alpha` — the closed form
  `sabrATMVol` is differentiable in `f` (for `f > 0`) and in `α`.
* `sabrATMVol_bsV_delta_chainRule`, `sabrATMVol_bsV_vega_chainRule` — the two combined, with the
  vol's slope written `deriv`: the derivative at `s = f` of
  `s ↦ bsV f 0 (sabrATMVol s α β ρ ν tex) s tex` and of
  `a ↦ bsV f 0 (sabrATMVol f a β ρ ν tex) f tex`.
* `sabrATMVol_marketPrice_delta_chainRule`, `sabrATMVol_marketPrice_vega_chainRule` — the same
  two derivatives for the Black-Scholes market's call price at rate `0`.

## Scope

The Delta is not eq. 3.9 at `K = f`: eq. 3.9 differentiates the fixed-strike smile
`f ↦ σ_B(K, f)`, the Delta here differentiates the ATM curve `f ↦ σ_B(f, f)`; the two agree at
`f = K` but their slopes differ by the smile's ATM strike-slope. Nor is it eq. 3.10 (`σ_ATM`
held fixed). The fixed-strike derivative of the general formula (eq. 2.17a) is not attempted:
at `K = f` its `z / x(z)` factor is `0/0`, so `f ↦ sabrImpliedVol K f ⋯` is not continuous at
`f = K` as defined. The Vega is eq. 3.6 at `K = f`.

## References

* [P. S. Hagan, D. Kumar, A. S. Lesniewski and D. E. Woodward,
  *Managing smile risk*][HaganKumarLesniewskiWoodward2002], §3.2, eqs. 3.5, 3.6, 3.9

## Tags

SABR, chain rule, Greeks, delta, vega, at-the-money, Frechet derivative, implied volatility,
MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real

/-! ### The ATM-vol curve is differentiable -/

/-- `sabrATMVol` (eq. 2.18) is differentiable in the forward, for `f > 0`. -/
theorem differentiableAt_sabrATMVol_F {f α β ρ ν tex : ℝ} (hf : 0 < f) :
    DifferentiableAt ℝ (fun x ↦ sabrATMVol x α β ρ ν tex) f := by
  have h1 : f ^ (1 - β) ≠ 0 := (Real.rpow_pos_of_pos hf _).ne'
  have h2 : f ^ (2 - 2 * β) ≠ 0 := (Real.rpow_pos_of_pos hf _).ne'
  unfold sabrATMVol sabrBackbone
  fun_prop (disch := first | assumption | exact Or.inl hf.ne')

/-- `sabrATMVol` (eq. 2.18) is differentiable in `α` (a polynomial in `α`, with no `α`-dependent
rpow base). -/
theorem differentiableAt_sabrATMVol_alpha {f β ρ ν tex : ℝ} (α : ℝ) :
    DifferentiableAt ℝ (fun a ↦ sabrATMVol f a β ρ ν tex) α := by
  unfold sabrATMVol sabrBackbone
  fun_prop

/-! ### The combined chain-rule Greeks -/

/-- **The SABR ATM chain-rule Delta**: the derivative at spot `s = f` of the Black call
with strike held fixed at `K = f`, priced at spot `s` with the ATM vol curve evaluated at
that spot, `σ_ATM(s) = sabrATMVol s α β ρ ν tex` — spot and the vol's own forward-dependence
moving together, strike fixed — equals `Δ_BS + Λ_BS · ∂σ_ATM/∂f`. See the file docstring
for exactly what this is (and is not) relative to Hagan's eq. 3.9. `hσ` is the
positivity of the vol at `f`, needed for the Black-Scholes sensitivities. -/
theorem sabrATMVol_bsV_delta_chainRule {f α β ρ ν tex : ℝ} (hf : 0 < f)
    (hσ : 0 < sabrATMVol f α β ρ ν tex) (htex : 0 < tex) :
    HasDerivAt (fun s ↦ bsV f 0 (sabrATMVol s α β ρ ν tex) s tex)
      (Phi (bsd1 f f 0 (sabrATMVol f α β ρ ν tex) tex)
        + f * gaussianPDFReal 0 1 (bsd1 f f 0 (sabrATMVol f α β ρ ν tex) tex) * Real.sqrt tex *
          deriv (fun x ↦ sabrATMVol x α β ρ ν tex) f)
      f :=
  hasDerivAt_bsV_S_chainRule hf hf hσ htex (differentiableAt_sabrATMVol_F hf)

/-- **The SABR ATM chain-rule Vega**: the derivative, in `α`, of the Black call priced at
the ATM strike `K = f` (spot and strike both fixed at `f`, only `α` moving through the
vol) with vol `σ_ATM = sabrATMVol f α β ρ ν tex`, equals `Λ_BS · ∂σ_ATM/∂α`. This is
Hagan et al.'s eq. 3.6 at `K = f`. -/
theorem sabrATMVol_bsV_vega_chainRule {f α β ρ ν tex : ℝ} (hf : 0 < f)
    (hσ : 0 < sabrATMVol f α β ρ ν tex) (htex : 0 < tex) :
    HasDerivAt (fun a ↦ bsV f 0 (sabrATMVol f a β ρ ν tex) f tex)
      (f * gaussianPDFReal 0 1 (bsd1 f f 0 (sabrATMVol f α β ρ ν tex) tex) * Real.sqrt tex *
        deriv (fun a ↦ sabrATMVol f a β ρ ν tex) α)
      α :=
  hasDerivAt_bsV_param_chainRule hf hf (v := fun a ↦ sabrATMVol f a β ρ ν tex) hσ htex
    (differentiableAt_sabrATMVol_alpha α)

/-! ### The same Greeks as derivatives of the market price -/

section MarketPrice

open scoped NNReal
open Contracts Contracts.BlackScholes

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {W : ℝ≥0 → Ω → ℝ} {μ : Measure Ω}
  [IsProbabilityMeasure μ] (hW : IsPreBrownianReal W μ) (hWmeas : ∀ t, Measurable (W t))

/-- The price of the European call in the Black-Scholes market at rate `0`, spot `S`, strike `K`
and volatility `σ`, under the Girsanov pricing measure of `θ = m / σ`, is `bsV K 0 σ S T`. -/
theorem price_europeanCall_eq_bsV {K S m σ : ℝ} {T H : ℝ≥0} (hTH : T ≤ H) (hS : 0 < S)
    (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < (T : ℝ)) :
    (market μ hWmeas S m 0 σ).price (constGirsanovMeasure hW hWmeas ((m - 0) / σ) H)
        (europeanCall K T) = bsV K 0 σ S T := by
  rw [price_europeanCall_constGirsanovMeasure hW hWmeas hTH hS hK hσ hT, bsV]
  simp

/-- **The SABR ATM chain-rule Delta is the derivative of the market price.** In the
Black-Scholes market with spot `s`, rate `0` and the SABR ATM vol `σ_ATM(s)` as its volatility,
the price of the European call struck at `f` under the Girsanov pricing measure of the constant
price of risk `m / σ_ATM(s)` (the measure moves with `s`) has, at `s = f`, the derivative
`Δ_BS + Λ_BS · ∂σ_ATM/∂f` of `sabrATMVol_bsV_delta_chainRule`. The price is undiscounted
(`r = 0`) and the horizon `H ≥ T` is the Girsanov horizon. -/
theorem sabrATMVol_marketPrice_delta_chainRule {f α β ρ ν m : ℝ} {T H : ℝ≥0} (hTH : T ≤ H)
    (hf : 0 < f) (hσ : 0 < sabrATMVol f α β ρ ν T) (hT : 0 < (T : ℝ)) :
    HasDerivAt (fun s ↦ (market μ hWmeas s m 0 (sabrATMVol s α β ρ ν T)).price
        (constGirsanovMeasure hW hWmeas ((m - 0) / sabrATMVol s α β ρ ν T) H) (europeanCall f T))
      (Phi (bsd1 f f 0 (sabrATMVol f α β ρ ν T) T)
        + f * gaussianPDFReal 0 1 (bsd1 f f 0 (sabrATMVol f α β ρ ν T) T) * Real.sqrt T *
          deriv (fun x ↦ sabrATMVol x α β ρ ν T) f)
      f := by
  refine (sabrATMVol_bsV_delta_chainRule hf hσ hT).congr_of_eventuallyEq ?_
  have hc : ContinuousAt (fun x ↦ sabrATMVol x α β ρ ν T) f :=
    (differentiableAt_sabrATMVol_F hf).continuousAt
  filter_upwards [hc.eventually (lt_mem_nhds hσ), lt_mem_nhds hf] with s hs hsf
  exact price_europeanCall_eq_bsV hW hWmeas hTH (by linarith) hf hs hT

/-- **The SABR ATM chain-rule Vega is the derivative of the market price.** In the
Black-Scholes market with spot `f`, rate `0` and volatility `σ_ATM(a) = sabrATMVol f a ⋯`, the
price of the European call struck at `f` under the Girsanov pricing measure of the constant price
of risk `m / σ_ATM(a)` has, at `a = α`, the derivative `Λ_BS · ∂σ_ATM/∂α` of
`sabrATMVol_bsV_vega_chainRule`. The price is undiscounted (`r = 0`). -/
theorem sabrATMVol_marketPrice_vega_chainRule {f α β ρ ν m : ℝ} {T H : ℝ≥0} (hTH : T ≤ H)
    (hf : 0 < f) (hσ : 0 < sabrATMVol f α β ρ ν T) (hT : 0 < (T : ℝ)) :
    HasDerivAt (fun a ↦ (market μ hWmeas f m 0 (sabrATMVol f a β ρ ν T)).price
        (constGirsanovMeasure hW hWmeas ((m - 0) / sabrATMVol f a β ρ ν T) H) (europeanCall f T))
      (f * gaussianPDFReal 0 1 (bsd1 f f 0 (sabrATMVol f α β ρ ν T) T) * Real.sqrt T *
        deriv (fun a ↦ sabrATMVol f a β ρ ν T) α)
      α := by
  refine (sabrATMVol_bsV_vega_chainRule hf hσ hT).congr_of_eventuallyEq ?_
  have hc : ContinuousAt (fun a ↦ sabrATMVol f a β ρ ν T) α :=
    (differentiableAt_sabrATMVol_alpha α).continuousAt
  filter_upwards [hc.eventually (lt_mem_nhds hσ)] with a ha
  exact price_europeanCall_eq_bsV hW hWmeas hTH hf hf ha hT

end MarketPrice

end MathFin
