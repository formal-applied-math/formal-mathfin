/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import MathFin

/-!
# Connector: a bond portfolio's value is a market price

The first-order immunization and the key-rate durations are statements about the flat-rate value
of a cash-flow schedule. This connector says that value is the price, in a market whose numéraire
is the money market at that rate, of the schedule as a contract.
-/

open MathFin MathFin.Contracts MeasureTheory
open scoped NNReal

/-- **A bond portfolio's flat-rate value is the market price of its cash flows.** In a market with
the money market `e^{rt}` as numéraire, under any probability measure `Q`, the portfolio of
zero-coupon bonds of face `w i` and maturity `T i ≥ 0` (`bondPortfolioValue` at time `0`) is the
price of the schedule `fixedFlows`, and the coupon bond at the annually compounded yield `y`
(`bondPriceDisc`) is the price of its cash flows when the numéraire is `(1 + y)^⌊t⌋₊`. -/
theorem MathFinFrontier.bondPortfolioValue_eq_price {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (n : ℕ) (w T : ℕ → ℝ) (hT : ∀ i, 0 ≤ T i) :
    (∀ (M : Market Unit Ω) (r : ℝ), (∀ t ω, M.numeraire t ω = Real.exp (r * t)) →
      bondPortfolioValue (Finset.range n) w T 0 r =
        M.price Q (fixedFlows (fun i ↦ (T i).toNNReal) w n)) ∧
    (∀ (M : Market Unit Ω) (y : ℝ) (t : ℕ → ℕ), 0 < 1 + y →
      (∀ s ω, M.numeraire s ω = (1 + y) ^ ⌊s⌋₊) →
      bondPriceDisc (Finset.range n) t w y =
        M.price Q (fixedFlows (fun i ↦ ((t i : ℕ) : ℝ≥0)) w n)) := by
  sorry
