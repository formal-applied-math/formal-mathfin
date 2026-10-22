/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.DeFi.UniswapMechanics
public import MathFin.BlackScholes.Forward

/-!
# The constant-product LP position under a lognormal price

A fee-free constant-product pool that is kept at the external price by arbitrage holds, after the
price of X (in Y) moves by the factor `r`, reserves worth `2 y₀ √r` in Y (`lpPortfolioValue_eq`,
`DeFi/UniswapMechanics.lean`), against `y₀ (r + 1)` for holding the deposit
(`hodlPortfolioValue_eq`). The LP position is a square-root claim on the price. When the price
move is lognormal, `r = bsTerminal 1 μ σ T Z` with `Z` standard normal (`BSCallHyp`), its square
root is again lognormal, `√r = bsTerminal 1 (μ/2 − σ²/8) (σ/2) T Z`, and the library's forward
identity `expected_terminal_eq_forward` (`BlackScholes/Forward.lean`) computes its expectation.

## Results

* `integral_lpValue_lognormal`: `E[LP_T] = 2 y₀ · exp ((μ/2 − σ²/8) T)`.
* `integral_hodlValue_lognormal`: `E[HODL_T] = y₀ · (exp (μ T) + 1)`.
* `integral_lpValue_eq_exp_mul_integral_hodlValue`: for a driftless price (`μ = 0`),
  `E[LP_T] = exp (−σ² T / 8) · E[HODL_T]`: the expected LP value falls short of the expected
  buy-and-hold value by the factor `exp (−σ² T / 8)`.

## Scope

The pool is fee-free and assumed to sit at the external price at `T` (the reserves are those of
`impermanentLossReservesX/Y`); deposit at the pool price `y₀ / x₀`. Values are in token Y and
undiscounted. Fees, the arbitrage path between `0` and `T`, and gas are not modelled.
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory DeFi

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} [IsProbabilityMeasure Q]

/-- The square root of a lognormal factor is lognormal with half the log-mean and half the
volatility: `√(bsTerminal 1 μ σ T z) = bsTerminal 1 (μ/2 − σ²/8) (σ/2) T z`. -/
lemma sqrt_bsTerminal_one (μ σ T z : ℝ) :
    Real.sqrt (bsTerminal 1 μ σ T z) = bsTerminal 1 (μ / 2 - σ ^ 2 / 8) (σ / 2) T z := by
  rw [bsTerminal, bsTerminal, one_mul, one_mul, ← Real.exp_half]
  congr 1
  ring

/-- **Expected value of a constant-product LP position under a lognormal price move.** Deposit
`(x₀, y₀)` at the pool price `y₀ / x₀`; the price of X moves by the factor
`r_T = bsTerminal 1 μ σ T Z`, lognormal under `Q` (`BSCallHyp`, rate slot read as the drift `μ`).
The LP position at `T` — reserves `impermanentLossReservesX/Y x₀ y₀ r_T` valued at the new price
`r_T · y₀ / x₀` — has expectation `2 y₀ · exp ((μ/2 − σ²/8) T)`. -/
theorem integral_lpValue_lognormal {x0 y0 K μ σ T : ℝ} {Z : Ω → ℝ} (hx0 : 0 < x0)
    (hy0 : 0 < y0) (h : BSCallHyp Q 1 K μ σ T Z) :
    ∫ ω, (impermanentLossReservesX x0 y0 (bsTerminal 1 μ σ T (Z ω))
          * (bsTerminal 1 μ σ T (Z ω) * y0 / x0)
        + impermanentLossReservesY x0 y0 (bsTerminal 1 μ σ T (Z ω))) ∂Q
      = 2 * y0 * Real.exp ((μ / 2 - σ ^ 2 / 8) * T) := by
  have hr (ω : Ω) : 0 < bsTerminal 1 μ σ T (Z ω) := mul_pos one_pos (Real.exp_pos _)
  have hpt (ω : Ω) :
      impermanentLossReservesX x0 y0 (bsTerminal 1 μ σ T (Z ω))
          * (bsTerminal 1 μ σ T (Z ω) * y0 / x0)
        + impermanentLossReservesY x0 y0 (bsTerminal 1 μ σ T (Z ω))
      = 2 * y0 * bsTerminal 1 (μ / 2 - σ ^ 2 / 8) (σ / 2) T (Z ω) := by
    rw [lpPortfolioValue_eq x0 y0 _ hx0 hy0 (hr ω), sqrt_bsTerminal_one]
  have h' : BSCallHyp Q 1 K (μ / 2 - σ ^ 2 / 8) (σ / 2) T Z :=
    ⟨one_pos, h.K_pos, half_pos h.σ_pos, h.T_pos, h.Z_law⟩
  simp_rw [hpt]
  rw [integral_const_mul, expected_terminal_eq_forward h', one_mul]

/-- **Expected value of holding the deposit** under the same lognormal price move:
`E[x₀ · (r_T y₀ / x₀) + y₀] = y₀ · (exp (μ T) + 1)`. -/
theorem integral_hodlValue_lognormal {x0 y0 K μ σ T : ℝ} {Z : Ω → ℝ} (hx0 : 0 < x0)
    (h : BSCallHyp Q 1 K μ σ T Z) :
    ∫ ω, (x0 * (bsTerminal 1 μ σ T (Z ω) * y0 / x0) + y0) ∂Q
      = y0 * (Real.exp (μ * T) + 1) := by
  have hpt (ω : Ω) : x0 * (bsTerminal 1 μ σ T (Z ω) * y0 / x0) + y0
      = y0 * (bsTerminal 1 μ σ T (Z ω) + 1) :=
    hodlPortfolioValue_eq x0 y0 _ hx0
  simp_rw [hpt]
  rw [integral_const_mul, integral_add (integrable_bsTerminal h.Z_law 1 μ σ T) (integrable_const 1),
    expected_terminal_eq_forward h, one_mul]
  simp

/-- **In expectation the LP position trails holding by the factor `exp (−σ² T / 8)`.** For a
driftless lognormal price move (`μ = 0`), the expected LP value at `T` is `exp (−σ² T / 8)`
times the expected buy-and-hold value. -/
theorem integral_lpValue_eq_exp_mul_integral_hodlValue {x0 y0 K σ T : ℝ} {Z : Ω → ℝ}
    (hx0 : 0 < x0) (hy0 : 0 < y0) (h : BSCallHyp Q 1 K 0 σ T Z) :
    ∫ ω, (impermanentLossReservesX x0 y0 (bsTerminal 1 0 σ T (Z ω))
          * (bsTerminal 1 0 σ T (Z ω) * y0 / x0)
        + impermanentLossReservesY x0 y0 (bsTerminal 1 0 σ T (Z ω))) ∂Q
      = Real.exp (-(σ ^ 2 * T / 8))
        * ∫ ω, (x0 * (bsTerminal 1 0 σ T (Z ω) * y0 / x0) + y0) ∂Q := by
  rw [integral_lpValue_lognormal hx0 hy0 h, integral_hodlValue_lognormal hx0 h, zero_mul,
    Real.exp_zero, show (0 / 2 - σ ^ 2 / 8) * T = -(σ ^ 2 * T / 8) by ring]
  ring

end MathFin
