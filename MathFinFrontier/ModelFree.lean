/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import MathFin

/-!
# Connectors: call-price functions and the market

Call prices in the strike are the static face of the fundamental theorem. A market with a pricing
measure produces a normalised call price function (proved:
`Market.IsPricingMeasure.isNormalizedCallPrice`); the converse, that every normalised call price
function (hence every butterfly-free SVI smile) is produced by a market, is stated here.
Docs: `docs/specs/2026-11-08-chain-design.md` §5 (K2).
-/

open MathFin MathFin.Contracts MeasureTheory
open scoped NNReal

/-- **Roper's converse.** Every normalised call price function is the call price function of a
market with unit numéraire, a positive asset of forward one at time one, and a pricing measure. -/
theorem MathFinFrontier.exists_market_of_isNormalizedCallPrice {C : ℝ → ℝ}
    (hC : IsNormalizedCallPrice C) :
    ∃ (M : Market Unit ℝ) (Q : Measure ℝ), (∀ t ω, M.numeraire t ω = 1) ∧
      (∀ ω, 0 < M.asset () 1 ω) ∧ M.IsPricingMeasure 1 Q ∧
      M.price Q (.pay 1 (.obs () 1)) = 1 ∧ ∀ k > 0, M.price Q (europeanCall k 1) = C k := by
  sorry

/-- **A butterfly-free SVI slice is the call price function of a market.** If the raw SVI
parameters satisfy `butterflyFreeFormula`, the forward-normalised Black call at the SVI smile is
the price of the call at strike `k` in a market with unit numéraire, forward one and a pricing
measure, at maturity one. -/
theorem MathFinFrontier.svi_realised_by_market {p : SVI.Params}
    (h : SVI.butterflyFreeFormula.eval p = true) :
    ∃ (M : Market Unit ℝ) (Q : Measure ℝ), (∀ t ω, M.numeraire t ω = 1) ∧
      M.IsPricingMeasure 1 Q ∧ M.price Q (.pay 1 (.obs () 1)) = 1 ∧
      ∀ k > 0, M.price Q (europeanCall k 1) = SVI.bsSmile p k := by
  sorry
