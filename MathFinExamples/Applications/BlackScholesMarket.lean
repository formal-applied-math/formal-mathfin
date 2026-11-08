/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import MathFin

/-!
# Using the library: a Black–Scholes market with every hypothesis discharged

A worked use of the library from outside it: a concrete Black–Scholes market, built on a concrete
Brownian motion, with a pricing measure and the price it gives a one-year at-the-money call.
Nothing is assumed: the Brownian motion is BrownianMotion's canonical one on path space
(`ProbabilityTheory.brownian` under `gaussianLimit`), and every numerical side condition is
checked by `norm_num`.

1. The market (`sampleMarket`): spot `100`, physical drift `8%`, rate `5%`, volatility `20%`, the
   information of the Brownian motion, and the money market as numéraire
   (`MathFin.Contracts.BlackScholes.market`).
2. The pricing measure (`sampleQ`): the Girsanov measure of the market price of risk
   `(8% − 5%)/20%` at a one-year horizon.
3. `sampleMarket_checked`: `sampleQ` is a pricing measure of the market up to one year, and under
   it the one-year call struck at `100` is worth the Black–Scholes formula, with the rate `5%`, not
   the drift `8%`, in `d₁` and `d₂`.

## What the library supplies

* `MathFin.Contracts.BlackScholes.market`, `isPricingMeasure_constGirsanovMeasure`,
  `price_europeanCall_constGirsanovMeasure`: the market, its pricing measure, and the call's price
  under it.
* `ProbabilityTheory.isBrownianReal_brownian`, `measurable_brownian`: the Brownian motion.

## What it does not

The price is the price under this pricing measure. That every pricing measure of the market gives
the same price is not proved for the Black–Scholes market (see
`Pricing/MarketCompleteness.lean` and `Pricing/PricingMeasureL2Density.lean` for the uniqueness
argument, stated for a price driven additively by the Brownian motion). The model has one asset,
constant drift, rate and volatility, and no dividends or transaction costs.

## Source

The shape of the file follows the binomial example
(`MathFinExamples/Applications/BinomialTree.lean`).
The numbers are illustrative.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal
open MathFin MathFin.Contracts MathFin.Contracts.BlackScholes

namespace MathFinExamples.BlackScholesMarket

/-- The sample market: spot `100`, physical drift `8%`, rate `5%`, volatility `20%`, driven by the
canonical Brownian motion. -/
noncomputable def sampleMarket : Market Unit (ℝ≥0 → ℝ) :=
  market gaussianLimit measurable_brownian 100 0.08 0.05 0.2

/-- The Girsanov measure of the market price of risk `(8% − 5%)/20%` at a one-year horizon. -/
noncomputable def sampleQ : Measure (ℝ≥0 → ℝ) :=
  constGirsanovMeasure isBrownianReal_brownian.toIsPreBrownianReal measurable_brownian
    ((0.08 - 0.05) / 0.2) 1

/-- **The sample market, checked**: `sampleQ` is a pricing measure up to one year, and under it the
one-year call struck at `100` is worth the Black–Scholes formula at the rate `5%`. -/
theorem sampleMarket_checked :
    sampleMarket.IsPricingMeasure 1 sampleQ ∧
      sampleMarket.price sampleQ (europeanCall 100 1)
        = 100 * Phi (bsd1 100 100 0.05 0.2 (1 : ℝ≥0))
          - 100 * Real.exp (-0.05 * (1 : ℝ≥0)) * Phi (bsd2 100 100 0.05 0.2 (1 : ℝ≥0)) :=
  ⟨isPricingMeasure_constGirsanovMeasure isBrownianReal_brownian.toIsPreBrownianReal
      measurable_brownian (by norm_num) le_rfl,
    price_europeanCall_constGirsanovMeasure isBrownianReal_brownian.toIsPreBrownianReal
      measurable_brownian le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num)⟩

end MathFinExamples.BlackScholesMarket
