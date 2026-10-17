/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.BlackScholes.GarmanNormalForm

/-!
# Kirk's approximation for spread options (`K ≠ 0`)

**This is an approximation, not an exact closed form.** The spread-option
payoff `max(S¹_T − S²_T − K, 0)` for `K ≠ 0` has no known exact Black–Scholes
closed form — unlike the `K = 0` case, which is the exact Margrabe exchange
option (`BlackScholes/ExchangeOption.lean`). Kirk (1995) prices it by treating
`S² + K` as a single "pseudo-asset" and running the Margrabe/Garman machinery
on `S¹` vs. that pseudo-asset, approximating the pseudo-asset's lognormal
volatility by linearising `S²/(S² + K)` at its initial value. The resulting
formula is a Black-Scholes-style price at an **effective volatility**

  `σ_eff² = σ₁² − 2ρσ₁σ₂ · S²₀/(S²₀ + K) + σ₂² · (S²₀/(S²₀ + K))²`,

which this file states and threads through the Garman normal form
(`GarmanNormalForm.lean`). It is a documented approximation (the
"pseudo-asset" is not actually lognormal), so no claim is made that
`kirkSpreadPrice` equals the true discounted expected payoff — only that it
is literally the standard BS closed form at this particular `(A, K', σ_eff)`,
and that it specialises to the *exact* Margrabe price when `K = 0`
(`kirkEffectiveVariance_zero_eq_margrabe`), where the pseudo-asset reduces to
`S²` itself and the approximation becomes exact.

## Results

* `kirkEffectiveVariance`: `σ₁² − 2ρσ₁σ₂·w + σ₂²·w²` where `w = S²₀/(S²₀+K)`.
* `kirkEffectiveVariance_zero_eq_margrabe`: at `K = 0` (so `w = 1`) Kirk's
  effective variance is exactly the Margrabe effective variance
  `σ₁² + σ₂² − 2ρσ₁σ₂` — the approximation's consistency check against the
  one case where the true answer is known in closed form.
* `kirkSpreadPrice`: the Kirk approximate price, `bsVGarman` at
  `A = S¹₀`, `K' = S²₀ + K`, `DF = e^{−rT}`, `σ = √σ_eff²`.
* `kirkSpreadPrice_eq_bsVGarman`: definitional unfolding exhibiting
  `kirkSpreadPrice` as a `GarmanNormalForm` instance (trivial by
  construction — it is built that way — but names the fact the file is
  for: Kirk's formula is literally the BS closed form parameterised by the
  pseudo-asset, not a new pricing primitive).
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

/-- **Kirk's approximate spread-option price**: the Garman-normal BS closed
form at `A = S¹₀` (the exchange leg), pseudo-strike `K' = S²₀ + K`, discount
factor `e^{−rT}`, and effective volatility `√(kirkEffectiveVariance S²₀ K
σ₁ σ₂ ρ)`. Documented as an **approximation**: this is Kirk's (1995)
heuristic, not the exact discounted expected payoff of
`max(S¹_T − S²_T − K, 0)`. -/
noncomputable def kirkSpreadPrice (S1 S2 K r σ1 σ2 ρ T : ℝ) : ℝ :=
  bsVGarman S1 (S2 + K) (Real.exp (-(r * T)))
    (Real.sqrt (kirkEffectiveVariance S2 K σ1 σ2 ρ)) T

/-- **Kirk's price is, by construction, a `GarmanNormalForm` instance** at the
pseudo-asset strike `S²₀ + K` and effective volatility `σ_eff`. Definitional
unfolding — the content is that `kirkSpreadPrice` is *literally* the one BS
closed form `bsVGarman`, not a bespoke new pricing formula, parameterised by
the Kirk pseudo-asset. -/
theorem kirkSpreadPrice_eq_bsVGarman (S1 S2 K r σ1 σ2 ρ T : ℝ) :
    kirkSpreadPrice S1 S2 K r σ1 σ2 ρ T =
      bsVGarman S1 (S2 + K) (Real.exp (-(r * T)))
        (Real.sqrt (kirkEffectiveVariance S2 K σ1 σ2 ρ)) T := rfl

end MathFin
