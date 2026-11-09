/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import MathFin

/-!
# Connectors: call-price functions and the market

Call prices in the strike are the static face of the fundamental theorem: a market with a pricing
measure produces a normalised call price function, and every normalised call price function (hence
every butterfly-free SVI smile) is produced by one. Docs: `docs/specs/2026-11-08-chain-design.md`
§5 (K2).
-/

open MathFin MathFin.Contracts MeasureTheory
open scoped NNReal

/-- **A pricing measure gives a normalised call price function.** In a market with unit numéraire
and a positive asset, priced at `T` by `Q`, the forward `F` of the asset is its price, and the
calls at the strikes `k F` priced in units of `F` are a normalised call price function: convex,
nonincreasing, between the intrinsic value and one, with limits one and zero. -/
theorem MathFinFrontier.isNormalizedCallPrice_of_isPricingMeasure
    {Ω : Type*} [MeasurableSpace Ω] {M : Market Unit Ω} {T : ℝ≥0} {Q : Measure Ω}
    (hQ : M.IsPricingMeasure T Q) (hN : ∀ t ω, M.numeraire t ω = 1)
    (hpos : ∀ ω, 0 < M.asset () T ω) {F : ℝ} (hF : F = M.price Q (.pay T (.obs () T))) :
    IsNormalizedCallPrice fun k ↦ M.price Q (europeanCall (k * F) T) / F := by
  sorry

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
