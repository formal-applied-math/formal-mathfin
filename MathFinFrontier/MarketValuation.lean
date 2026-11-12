/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import MathFin

/-!
# Connectors of the valuation limb: the market-level fundamental theorems

Two statements about `Market`, closed by `sorry`.

* `MathFinFrontier.market_dmw`: the Dalang–Morton–Willinger direction of the fundamental theorem
  for a market on a general probability space (frontier node `thm:dmw-ftap`). The library proves
  it for a finite sample space (`Market.noArbitrage_iff_exists_isPricingMeasure_of_finite`) and,
  on a general space, assuming `ConditionalOnePeriodFTAP`
  (`Market.noArbitrage_iff_exists_isPricingMeasure`).
-/

open MeasureTheory ProbabilityTheory MathFin MathFin.Contracts MathFin.Contracts.BlackScholes
open scoped NNReal ENNReal

/-- **Dalang–Morton–Willinger for a market.** A one-asset market on a probability space with no
arbitrage on a grid of dates has a pricing measure for the market traded on the grid. -/
theorem MathFinFrontier.market_dmw {Ω : Type*} {mΩ : MeasurableSpace Ω} (M : Market Unit Ω)
    [IsProbabilityMeasure M.P] {t : ℕ → ℝ≥0} (ht : Monotone t) (N : ℕ) (h : M.NoArbitrage ht N) :
    ∃ Q, (M.onGrid ht N).IsPricingMeasure N Q := by
  sorry
