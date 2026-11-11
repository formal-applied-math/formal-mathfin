/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Init
public import MathFin.Models.ModelFree.MarketCallPrice
public import MathFin.Models.ModelFree.SVI.TailCondition

/-!
# A market that prices the SVI smile makes the slice butterfly-free

The forward direction of the static fundamental theorem
(`Market.IsPricingMeasure.isNormalizedCallPrice`) meets the SVI sign formula: if the calls of a
market with a pricing measure, in units of the forward, are the SVI-smiled Black prices, and the
parameters are admissible, then `butterflyFreeFormula` holds. The converse (every butterfly-free
slice is the call price function of a market) needs the construction of a measure from a convex
call price function and is not proved here.

## Main results

* `SVI.butterflyFreeFormula_of_isPricingMeasure`: a pricing measure whose normalised calls are the
  SVI smile forces the finite sign formula `butterflyFreeFormula`.

## References

* [Gatheral and Jacquier, *Arbitrage-free SVI volatility surfaces*][GatheralJacquier2014], Lemma 2.2
* [Roper, *Arbitrage free implied volatility surfaces*][Roper2010], Theorem 2.1

## Tags

SVI smile, pricing measure, butterfly arbitrage, no static arbitrage, MSC 91G20, JEL G13
-/

@[expose] public section

open MeasureTheory MathFin.Contracts
open scoped NNReal

namespace MathFin.SVI

/-- **A market that prices the SVI smile makes the slice butterfly-free.** In a market with unit
numéraire and a positive asset, priced at `T` by `Q`, if the calls at the strikes `k F`, in units
of the forward `F`, have the SVI-smiled Black price at every `k > 0`, and the parameters satisfy
`σ ≥ 0`, `b ≥ 0`, `ρ² ≤ 1` with positive variance everywhere, then `butterflyFreeFormula` holds:
the call price function is convex and satisfies the tail condition. -/
theorem butterflyFreeFormula_of_isPricingMeasure {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {M : Market Unit Ω} {T : ℝ≥0} {Q : Measure Ω} {p : Params}
    (hp : 0 ≤ p.sigma ∧ 0 ≤ p.b ∧ 0 ≤ 1 - p.rho ^ 2 ∧ ∀ k, 0 < variance p k)
    (hQ : M.IsPricingMeasure T Q) (hN : ∀ t ω, M.numeraire t ω = 1)
    (hpos : ∀ ω, 0 < M.asset () T ω) {F : ℝ} (hF : F = M.price Q (.pay T (.obs () T)))
    (hsmile : ∀ k > 0, M.price Q (europeanCall (k * F) T) / F = bsSmile p k) :
    butterflyFreeFormula.eval p = true :=
  (butterflyFreeFormula_iff_isNormalizedCallPrice p).2
    ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2,
      (hQ.isNormalizedCallPrice hN hpos hF).of_eqOn fun k hk ↦ hsmile k hk⟩

end MathFin.SVI
