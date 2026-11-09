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
* `MathFinFrontier.bs_call_price_unique`: every pricing measure of the Black–Scholes market with a
  square-integrable density prices the European call at the Black–Scholes formula (frontier node
  `thm:bs-arbitrage-free-price`). The library proves that the Girsanov measure of the market price
  of risk is one (`BlackScholes.isPricingMeasure_constGirsanovMeasure`) and prices the call so
  (`BlackScholes.price_europeanCall_constGirsanovMeasure`).
-/

open MeasureTheory ProbabilityTheory MathFin MathFin.Contracts MathFin.Contracts.BlackScholes
open scoped NNReal ENNReal

/-- **Dalang–Morton–Willinger for a market.** A one-asset market on a probability space with no
arbitrage on a grid of dates has a pricing measure for the market traded on the grid. -/
theorem MathFinFrontier.market_dmw {Ω : Type*} {mΩ : MeasurableSpace Ω} (M : Market Unit Ω)
    [IsProbabilityMeasure M.P] {t : ℕ → ℝ≥0} (ht : Monotone t) (N : ℕ) (h : M.NoArbitrage ht N) :
    ∃ Q, (M.onGrid ht N).IsPricingMeasure N Q := by
  sorry

/-- **Every pricing measure of the Black–Scholes market with a square-integrable density prices the
European call at the Black–Scholes formula.** The Brownian motion is continuous, the volatility
positive, and the pricing measure `Q` is a probability measure with density `D ∈ L²(μ)` with
respect to the physical measure `μ`. -/
theorem MathFinFrontier.bs_call_price_unique {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {W : ℝ≥0 → Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ] (hW : IsPreBrownianReal W μ)
    (hWmeas : ∀ t, Measurable (W t)) (hWcont : ∀ ω, Continuous fun s : ℝ≥0 ↦ W s ω)
    {S₀ K m r σ : ℝ} {T : ℝ≥0} (hS₀ : 0 < S₀) (hK : 0 < K) (hσ : 0 < σ) (hT : 0 < (T : ℝ))
    {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hQ : (market μ hWmeas S₀ m r σ).IsPricingMeasure T Q) (D : Lp ℝ 2 μ)
    (hD : ∀ᵐ ω ∂μ, 0 ≤ (D : Ω → ℝ) ω)
    (hQD : Q = μ.withDensity fun ω ↦ ENNReal.ofReal ((D : Ω → ℝ) ω)) :
    (market μ hWmeas S₀ m r σ).price Q (europeanCall K T)
      = S₀ * Phi (bsd1 S₀ K r σ T) - K * Real.exp (-r * T) * Phi (bsd2 S₀ K r σ T) := by
  sorry
