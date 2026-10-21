/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib
public import MathFin.BlackScholes.GarmanNormalForm
public import MathFin.BlackScholes.ExchangeOption

/-!
# Kirk's approximation for spread options (`K ≠ 0`)

**This is an approximation, not an exact closed form.** The spread-option
payoff `max(S¹_T − S²_T − K, 0)` for `K ≠ 0` has no known exact Black–Scholes
closed form — unlike the `K = 0` case, which is the exact Margrabe exchange
option (`BlackScholes/ExchangeOption.lean`). Kirk (1995) prices it, in
forward terms, by treating `F² + K` as a single "pseudo-asset" and running
the Margrabe/Garman machinery on `F¹` vs. that pseudo-asset, approximating
the pseudo-asset's lognormal volatility by linearising `F²/(F² + K)` at its
initial value. Converting to spot via `Fⁱ = Sⁱ·e^{rT}` (no dividends), the
pseudo-strike becomes `S² + K·e^{-rT}` — only the cash strike `K` is
discounted, `S²` is already a present value — and the linearisation weight
becomes `w = S²₀/(S²₀ + K·e^{-rT})`. The resulting formula is a
Black-Scholes-style **undiscounted** spot price (`DF = 1`, since `S¹, S²`
already are present values) at an **effective volatility**

  `σ_eff² = σ₁² − 2ρσ₁σ₂ · w + σ₂² · w²`,  `w = S²₀/(S²₀ + K·e^{-rT})`,

which this file states and threads through the Garman normal form
(`GarmanNormalForm.lean`). It is a documented approximation (the
"pseudo-asset" is not actually lognormal), so no claim is made that
`kirkSpreadPrice` equals the true discounted expected payoff — only that it
is literally the standard BS closed form at this particular `(A, K', σ_eff)`.
At `K = 0` the discounted cash strike `K·e^{-rT}` is `0` for every `r`, so
the pseudo-asset reduces to `S²` itself for every `r`: both the
**effective-variance parameter** (`kirkEffectiveVariance_zero_eq_margrabe`)
and the **price itself** (`kirkSpreadPrice_zero_eq_margrabe`) collapse to
exactly Margrabe at `K = 0`, for every `r` — the honest consistency check
against the one case where the true answer is known in closed form.

## Results

* `kirkEffectiveVariance`: `σ₁² − 2ρσ₁σ₂·w + σ₂²·w²` where `w = S²₀/(S²₀+K')`
  (`K'` is the already-discounted cash strike, `K·e^{-rT}`).
* `kirkEffectiveVariance_zero_eq_margrabe`: at `K' = 0` (so `w = 1`) Kirk's
  effective variance is exactly the Margrabe effective variance
  `σ₁² + σ₂² − 2ρσ₁σ₂`.
* `kirkSpreadPrice`: the Kirk approximate price, `bsVGarman` at
  `A = S¹₀`, `K' = S²₀ + K·e^{-rT}`, `DF = 1`, `σ = √σ_eff²`.
* `kirkSpreadPrice_eq_bsVGarman`: definitional unfolding exhibiting
  `kirkSpreadPrice` as a `GarmanNormalForm` instance (trivial by
  construction — it is built that way — but names the fact the file is
  for: Kirk's formula is literally the BS closed form parameterised by the
  pseudo-asset, not a new pricing primitive).
* `kirkSpreadPrice_zero_eq_margrabe`: at `K = 0`, for every `r`,
  `kirkSpreadPrice` is exactly `margrabePrice` at the (K=0) effective
  volatility — a genuine price-level equality, not just a variance-level one.
-/

@[expose] public section

namespace MathFin

open Real

/-- **Kirk's weight**: the linearisation point `w = S²₀/(S²₀ + K)` at which the
pseudo-asset `S² + K`'s lognormal volatility is approximated by `σ₂ · w`. -/
noncomputable def kirkWeight (S2 K : ℝ) : ℝ := S2 / (S2 + K)

/-- **Kirk's effective variance**: `σ₁² − 2ρσ₁σ₂·w + σ₂²·w²`, with
`w = kirkWeight S2 K`. This is the variance of `L₁ − w·L₂` under the
Margrabe-style bilinear expansion (`margrabe_variance_sub`), i.e. Kirk's
approximation is "Margrabe with `S²` shrunk by `w`." -/
noncomputable def kirkEffectiveVariance (S2 K σ1 σ2 ρ : ℝ) : ℝ :=
  σ1 ^ 2 - 2 * ρ * σ1 * σ2 * kirkWeight S2 K + σ2 ^ 2 * kirkWeight S2 K ^ 2

/-- **Kirk reduces to Margrabe at `K = 0`**: `kirkWeight S2 0 = 1`, so Kirk's
effective variance collapses to exactly the Margrabe effective variance
`σ₁² + σ₂² − 2ρσ₁σ₂` — the one point where the spread-option payoff
`max(S¹ − S² − K, 0)` is the *exact* exchange-option payoff and Kirk's
approximation is not an approximation at all. -/
theorem kirkEffectiveVariance_zero_eq_margrabe (S2 σ1 σ2 ρ : ℝ) (hS2 : S2 ≠ 0) :
    kirkEffectiveVariance S2 0 σ1 σ2 ρ = σ1 ^ 2 + σ2 ^ 2 - 2 * ρ * σ1 * σ2 := by
  unfold kirkEffectiveVariance kirkWeight
  rw [add_zero, div_self hS2]
  ring

/-- **Kirk's discounted cash strike** `K · e^{-rT}`: the only piece of the
pseudo-strike `S²₀ + K·e^{-rT}` that needs discounting, since `S²₀` is
already a spot (present-value) quantity while `K` is a cash amount paid
at `T`. -/
noncomputable def kirkDiscountedStrike (K r T : ℝ) : ℝ := K * Real.exp (-(r * T))

/-- **Kirk's approximate spread-option price**: the Garman-normal BS closed
form at `A = S¹₀` (the exchange leg), pseudo-strike
`K' = S²₀ + K·e^{-rT}`, `DF = 1` (both `S¹₀` and the pseudo-strike are
already present-value spot quantities, so no further discounting applies),
and effective volatility `√(kirkEffectiveVariance S²₀ (K·e^{-rT}) σ₁ σ₂ ρ)`.
Documented as an **approximation**: this is Kirk's (1995) heuristic, not the
exact discounted expected payoff of `max(S¹_T − S²_T − K, 0)`. -/
noncomputable def kirkSpreadPrice (S1 S2 K r σ1 σ2 ρ T : ℝ) : ℝ :=
  bsVGarman S1 (S2 + kirkDiscountedStrike K r T) 1
    (Real.sqrt (kirkEffectiveVariance S2 (kirkDiscountedStrike K r T) σ1 σ2 ρ)) T

/-- **Kirk's price is, by construction, a `GarmanNormalForm` instance** at the
pseudo-asset strike `S²₀ + K·e^{-rT}` and effective volatility `σ_eff`.
Definitional unfolding — the content is that `kirkSpreadPrice` is *literally*
the one BS closed form `bsVGarman`, not a bespoke new pricing formula,
parameterised by the Kirk pseudo-asset. -/
theorem kirkSpreadPrice_eq_bsVGarman (S1 S2 K r σ1 σ2 ρ T : ℝ) :
    kirkSpreadPrice S1 S2 K r σ1 σ2 ρ T =
      bsVGarman S1 (S2 + kirkDiscountedStrike K r T) 1
        (Real.sqrt (kirkEffectiveVariance S2 (kirkDiscountedStrike K r T) σ1 σ2 ρ)) T :=
  rfl

/-- **Kirk's price collapses to the exact Margrabe price at `K = 0`, for
every `r`**: the discounted cash strike `kirkDiscountedStrike 0 r T` is `0`
regardless of `r` (nothing to discount), so the pseudo-asset is `S²₀` itself
and `kirkSpreadPrice` is literally `margrabePrice` at the `K = 0` effective
volatility — a genuine *price-level* equality (not merely the
variance-level `kirkEffectiveVariance_zero_eq_margrabe`), witnessing that
Kirk's heuristic is exact at the one point where the spread payoff
`max(S¹ − S² − K, 0)` is the exact exchange-option payoff. -/
theorem kirkSpreadPrice_zero_eq_margrabe (S1 S2 r σ1 σ2 ρ T : ℝ) :
    kirkSpreadPrice S1 S2 0 r σ1 σ2 ρ T =
      margrabePrice S1 S2 (Real.sqrt (kirkEffectiveVariance S2 0 σ1 σ2 ρ)) T := by
  unfold kirkSpreadPrice kirkDiscountedStrike
  rw [zero_mul, add_zero]
  exact (margrabe_eq_bsVGarman S1 S2 _ T).symm

end MathFin
