/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.Models.StochVol.Heston
public import MathFin.Models.Rates.AffineTermStructurePDE

/-!
# The Heston transform at zero maturity

At zero time to maturity a European claim's model price must collapse to the undiscounted
payoff: a degenerate-maturity engine must return `(payoff)(spot)` when the computed time
to maturity is exactly zero — the same zero-maturity convention the Black formula applies
at zero standard deviation (returning the discounted intrinsic; at zero variance the
lognormal degenerates to the point mass at the forward). This file proves the two
halves of that convention for the Heston Riccati closed forms of
`Models/StochVol/Heston.lean`: the
transform profile degenerates to the moment-generating function of the point mass at the
initial log-spot, and the European expectation under that degenerate law is the
undiscounted payoff.

The Riccati flows vanish at the zero-argument instance. `hestonBv_at_zero`
(`Models/StochVol/Heston.lean`) gives `b̂(0) = 0` with no hypothesis, and
`hestonA_zeroMaturity` below gives `â(0) = 0` with no hypothesis — the
`hestonGamma ≠ 0` guard of `hestonA_at_zero` is removable: at `γ = 0` the closed form's
log term sees `x/0`, which Lean evaluates to `0`, so the log vanishes and the closed form
still matches the true terminal data `â(0) = 0` of the Riccati system. With both flows
zero, the profile `Φ(t, x, v) = e^{â(0) + u·x + b̂(0)·v}` is `e^{u·x}` — the
moment-generating function of the point mass `Measure.dirac x` at the initial log-spot
`x` (`hestonTransform_zeroMaturity_pointMass`, via Mathlib's `mgf_dirac'`).

The price collapse is the same statement one level down: the expectation of a European
payoff against the point mass at the (log-)spot is the undiscounted payoff —
`max(S − K, 0)`, `max(K − S, 0)` in spot coordinates (no discount factor), the
same collapse in the log-spot
coordinates the Heston profile lives in (`max(e^x − K, 0)`, `max(K − e^x, 0)`).

**Scope.** The collapse is stated at the exact zero instance, as the engine convention
states it; the continuity of the price in the time to maturity (the `τ → 0` limit) is not
proved. The expectation is taken against the point-mass law itself; the identification of
the Heston profile with `E[e^{u·log S_T}]` for a Heston process is not available in the
library (`Heston.lean` does not prove it either), so these are expectations under the
degenerate (zero-maturity) law, not under a proved Heston risk-neutral law. The
characteristic-function route (complex `iu`) is out of scope here, as in `Heston.lean`.

## Main results

* `hestonA_zeroMaturity`: `â(0) = 0` for every parameter — strengthens `hestonA_at_zero`
  by removing the `hestonGamma ≠ 0` guard (`hestonBv_at_zero` needs none).
* `hestonTransform_zeroMaturity`: at zero time to maturity the explicit-flow Heston
  transform profile equals `e^{u·x}`, with no strip hypothesis and for every `u`.
* `hestonTransform_zeroMaturity_pointMass`: that value is exactly
  `mgf id (Measure.dirac x) u`, the moment-generating function of the point mass at the
  initial log-spot.
* The European expectation against the point mass at the (log-)spot is the undiscounted
  intrinsic — Mathlib's `integral_dirac` applied to the payoff (undiscounted: the τ = 0
  discount factor is 1); carried in prose rather than as theorems, per the no-thin-wrapper
  rule for single upstream results.
  the spot is the undiscounted payoff `max(S − K, 0)` / `max(K − S, 0)`.
  coordinates, `max(e^x − K, 0)` / `max(K − e^x, 0)`.

## References

* [Heston, *A closed-form solution for options with stochastic volatility with applications to bond
  and currency options*][Heston1993]
* [The QuantLib contributors, *QuantLib*][QuantLib], AnalyticPTDHestonEngine

## Tags

Heston model, zero maturity, point mass, moment-generating function, European option,
intrinsic value, MSC 91G20, MSC 60J60, JEL G13
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace MathFin.Heston

/-! ### The flows at the zero-argument instance -/

/-- **The `A`-flow at zero time to maturity, with no hypothesis**: `hestonA r κ θ ξ ρ u 0 = 0`
for every choice of the parameters. This strengthens `hestonA_at_zero` by removing its
`hestonGamma ≠ 0` guard: at `γ = 0` the closed form's log sees the division `x/0`, which
Lean evaluates to `0` (the argument is `D(0)/(2γ) = 0/0`), so `Real.log 0 = 0` and the
closed form still vanishes — matching
the true terminal data `â(0) = 0` of the Riccati system (the closed form is otherwise
degenerate at `γ = 0`, as `HestonSmallVolOfVol.lean` documents for the `ξ = 0` face). -/
theorem hestonA_zeroMaturity (r κ θ ξ ρ u : ℝ) : hestonA r κ θ ξ ρ u 0 = 0 := by
  rcases eq_or_ne (hestonGamma κ ξ ρ u) 0 with h0 | h0
  · simp [hestonA, hestonBvDenom, h0]
  · exact hestonA_at_zero r κ θ ξ ρ u h0

/-- **Zero-maturity collapse of the Heston transform.** With maturity `t` and valuation
time `t` — zero time to maturity — the transform profile built from the Riccati closed
forms `hestonA`, `hestonBv` is `e^{u·x}` for every `u` and every parameter: the flows
vanish at the zero-argument instance (`hestonA_zeroMaturity`, `hestonBv_at_zero`), so the
log-spot profile degenerates to the moment-generating function of the point mass at the
initial log-spot `x`. No strip
hypothesis and no guard — this is `hestonTransform_terminal` with `T := t` and its
`ξ ≠ 0`, `0 < u < 1` hypotheses removed. -/
theorem hestonTransform_zeroMaturity (r κ θ ξ ρ u t x v : ℝ) :
    hestonProfile u (fun w => hestonA r κ θ ξ ρ u (t - w))
        (fun w => hestonBv κ ξ ρ u (t - w)) t x v
      = Real.exp (u * x) := by
  refine hestonProfile_terminal u _ _ t x v ?_ ?_
  · simpa using hestonA_zeroMaturity r κ θ ξ ρ u
  · simpa using hestonBv_at_zero κ ξ ρ u

/-! ### The point-mass identification and the price collapse -/

/-- **The zero-maturity profile is the point-mass mgf**: the collapsed transform profile
`e^{u·x}` equals `mgf id (Measure.dirac x) u`, the moment-generating function of the point
mass `Measure.dirac x` at the initial log-spot `x` — the point-mass identification of the
degenerate profile (Mathlib's `mgf_dirac'` at the identity random variable). -/
theorem hestonTransform_zeroMaturity_pointMass (r κ θ ξ ρ u t x v : ℝ) :
    hestonProfile u (fun w => hestonA r κ θ ξ ρ u (t - w))
        (fun w => hestonBv κ ξ ρ u (t - w)) t x v
      = mgf id (Measure.dirac x) u := by
  rw [hestonTransform_zeroMaturity, mgf_dirac']
  simp





end MathFin.Heston
