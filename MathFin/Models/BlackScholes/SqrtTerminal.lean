/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.Models.BlackScholes.Call

/-!
# The square root of a lognormal terminal price

The square root of a lognormal factor is lognormal with half the log-volatility. This is the
one algebraic step behind the expected value of any square-root claim on a lognormal quantity
(the constant-product LP position, the volatility-swap strike).

## Main results

* `sqrt_bsTerminal`: `√(bsTerminal S₀ μ σ T z) = √S₀ · bsTerminal 1 (μ/2 − σ²/8) (σ/2) T z`
  for `0 ≤ S₀`.

## Tags

lognormal, square root, Black–Scholes terminal price, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin

/-- The square root of a lognormal factor is lognormal with half the log-mean and half the
volatility, with the factor `S_0` pulled out of the root:
`√(bsTerminal S_0 μ σ T z) = √S_0 · bsTerminal 1 (μ/2 − σ²/8) (σ/2) T z`. -/
lemma sqrt_bsTerminal {S_0 : ℝ} (hS : 0 ≤ S_0) (μ σ T z : ℝ) :
    Real.sqrt (bsTerminal S_0 μ σ T z)
      = Real.sqrt S_0 * bsTerminal 1 (μ / 2 - σ ^ 2 / 8) (σ / 2) T z := by
  rw [bsTerminal, bsTerminal, Real.sqrt_mul hS, one_mul, ← Real.exp_half]
  congr 2
  ring

end MathFin
