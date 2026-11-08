/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import MathFin

/-!
# Connector: a liquidity position is a contract

`DeFi.constantProductPayoff` and `DeFi.lpPayoff` write the constant-product and the
concentrated-liquidity position as payoffs. This connector says that, in any market, paying them
at `T` is worth the discounted expectation of the position's value as `UniswapMechanics` states
it.
-/

open MathFin MathFin.Contracts MeasureTheory
open scoped NNReal

/-- **The price of a liquidity position is the discounted expectation of its value.** In a market
with a positive price of X in Y at `T`, under any measure `Q`: the concentrated-liquidity payoff
`lpPayoff L a b T` (for `0 < a ≤ b`) is worth `∫ D_T · v3PositionValue L a b (√P_T)`, and the
constant-product payoff of invariant `x₀ y₀` is worth the discounted expectation of the reserves
`impermanentLossReservesX/Y` valued at the price `P_T`. -/
theorem MathFinFrontier.price_lpPayoff {Ω : Type*} [MeasurableSpace Ω] (M : Market Unit Ω)
    (Q : Measure Ω) (T : ℝ≥0) (hS : ∀ ω, 0 < M.asset () T ω) :
    (∀ L a b : ℝ, 0 < a → a ≤ b →
      M.price Q (.pay T (DeFi.lpPayoff L a b T)) =
        ∫ ω, M.deflator T ω * DeFi.v3PositionValue L a b (Real.sqrt (M.asset () T ω)) ∂Q) ∧
    (∀ x₀ y₀ : ℝ, 0 < x₀ → 0 < y₀ →
      M.price Q (.pay T (DeFi.constantProductPayoff (x₀ * y₀) T)) =
        ∫ ω, M.deflator T ω *
          (DeFi.impermanentLossReservesX x₀ y₀ (M.asset () T ω * x₀ / y₀) * M.asset () T ω +
            DeFi.impermanentLossReservesY x₀ y₀ (M.asset () T ω * x₀ / y₀)) ∂Q) := by
  sorry
