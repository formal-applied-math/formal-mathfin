/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Models.BlackScholes.Market
public import MathFin.Models.BlackScholes.American.Stopping.AmericanValue

/-!
# The summit of the American put tower: it dominates the market's European price

The American put tower (`Models/BlackScholes/American/`) values the put as a supremum of expected
discounted payoffs over stopping rules bounded by the horizon, on the risk-neutral asset driven by
a Brownian motion `B`. The Black–Scholes market (`Models/BlackScholes/Market.lean`) prices the
European put as a `Market.price` under a pricing measure. This file ties the two. Under the
Girsanov measure `Q` of `θ = (m − r)/σ`, the physical asset is `Q`-almost surely the risk-neutral
asset of the drift-corrected process `B^θ` (`pathAssets_physical_ae_eq`), so the market price of
the European put is the expected discounted payoff of the stopping rule `θ ≡ T`, which is
admissible; the American value over the natural filtration of `W` dominates it.

Not proved here: that the inequality is strict, or that the American value is the superhedging
price of the put (`thm:american-put-superhedging-price`).

## Main results

* `MathFin.Contracts.BlackScholes.price_europeanPut_le_americanPutValue`: for `σ ≠ 0`, `T ≤ H`,
  the price of `europeanPut K T` in `BlackScholes.market` under `constGirsanovMeasure` at horizon
  `H` is at most `americanPutValue` of the process `B^θ`, without dividends, over the rules
  bounded by `T`.

## References

* [I. Karatzas and S. E. Shreve, *Methods of Mathematical Finance*][KaratzasShreve1998], §2.5
* [R. C. Merton, *Theory of rational option pricing*][Merton1973]

## Tags

American put, European put, Black–Scholes market, Girsanov measure, pricing measure,
early exercise, stopping rules, MSC 91G20, MSC 60G40, JEL G13
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal
open MathFin MathFin.BlackScholes.AmericanPut.Stopping ItoIntegralL2

namespace MathFin.Contracts.BlackScholes

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {W : ℝ≥0 → Ω → ℝ} {μ : Measure Ω}
  [IsProbabilityMeasure μ]

/-- **The American put value dominates the Black–Scholes price of the European put.** For a
nonzero volatility `σ`, at the Girsanov pricing measure `Q` of `θ = (m − r)/σ` with horizon
`H ≥ T`, the price of `europeanPut K T` in `BlackScholes.market` is at most the American put value
(no dividends) of the Brownian motion `B^θ` over the natural filtration of `W`, for the stopping
rules bounded by `T`. The deterministic rule `T` is admissible, and its expected discounted payoff
is the market price because the physical asset is `Q`-almost surely the risk-neutral asset of
`B^θ`. -/
theorem price_europeanPut_le_americanPutValue (hW : IsPreBrownianReal W μ)
    (hWmeas : ∀ t, Measurable (W t)) {S_0 m r σ K : ℝ} {T H : ℝ≥0} (hσ : σ ≠ 0) (hTH : T ≤ H)
    (hB : Measurable (constBtheta (μ := μ) hWmeas ((m - r) / σ) H).uncurry)
    (hK : 0 ≤ K) (hr : 0 ≤ r) (hS : 0 ≤ S_0) :
    (market μ hWmeas S_0 m r σ).price (constGirsanovMeasure hW hWmeas ((m - r) / σ) H)
        (europeanPut K T) ≤
      americanPutValue (constGirsanovMeasure hW hWmeas ((m - r) / σ) H) (natFiltration hWmeas)
        (constBtheta (μ := μ) hWmeas ((m - r) / σ) H) K r 0 σ S_0 T := by
  haveI := constGirsanovMeasure_isProbabilityMeasure hW hWmeas ((m - r) / σ) H
  rw [price_market, europeanPut, Contract.value_pay]
  refine (integral_congr_ae ?_).trans_le (european_expectation_le_value hB hK hr hS)
  filter_upwards [pathAssets_physical_ae_eq hW hWmeas (S_0 := S_0) (m := m) (r := r) hσ H hTH]
    with ω hω
  simp only [Payoff.eval, scenarioAt, putReward, hω]
  simp only [pathAssets, gbmValue, sub_zero]

end MathFin.Contracts.BlackScholes
