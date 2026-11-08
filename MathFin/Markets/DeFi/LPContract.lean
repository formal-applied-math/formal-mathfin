/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Contracts.Core
public import MathFin.Markets.DeFi.UniswapMechanics

/-!
# Liquidity positions as payoffs

A fee-free automated-market-maker position is a function of the price `P` of token X in token Y at
the date it is read, so it is a `Contracts.Payoff` on the single underlying `()`, and paying it at
`T` is a `Contract`. Both positions are functions of `√P`, which is the `rpow` of the payoff
language with exponent `1/2`:

* the constant-product position with invariant `k = x₀ y₀` is worth `2 √k √P` in token Y
  (`lpPortfolioValue_eq`: `2 y₀ √r` at the price ratio `r = P x₀ / y₀`);
* the concentrated-liquidity position with liquidity `L` on the square-root range `[a, b]` is worth
  `v3PositionValue L a b (√P)`, which is `L (2u − a − u²/b) + L (1/a − 1/b) (m² − a²)` for
  `u = max a (min √P b)` and `m = min √P a`: concave inside the range, the quadratic
  `L (1/a − 1/b) P` below it, constant above.

## Main definitions

* `constantProductPayoff`: the constant-product position as a payoff.
* `lpPayoff`: the concentrated-liquidity position as a payoff.

## Scope

Only the definitions are here; that they evaluate to `v3PositionValue` and to the reserve form of
`UniswapMechanics` is stated, not proved, by the connector `MathFinFrontier.price_lpPayoff`.

## References

* [H. Adams et al., *Uniswap v3 Core*][AdamsEtAl2021], §6.4.1 (eqs. 6.29-6.30)
* [G. Angeris et al., *An analysis of Uniswap markets*][AngerisKaoChiangNoyesChitra2021]

## Tags

liquidity position, constant-product market maker, Uniswap v3, concentrated liquidity,
payoff language, MSC 91G80, JEL G23
-/

@[expose] public section

open scoped NNReal

namespace MathFin.DeFi

open MathFin.Contracts

/-- The square root `√P` of the price observed at `T`, as a payoff. -/
noncomputable def sqrtObs (T : ℝ≥0) : Payoff Unit := .rpow (.obs () T) (1 / 2)

/-- **The constant-product position** with invariant `k = x₀ y₀`, as a payoff on the price of X
in Y observed at `T`: `2 √k √P`. -/
noncomputable def constantProductPayoff (k : ℝ) (T : ℝ≥0) : Payoff Unit :=
  .mul (.const (2 * Real.sqrt k)) (sqrtObs T)

/-- **The concentrated-liquidity position** with liquidity `L` on the square-root range `[a, b]`,
as a payoff on the price of X in Y observed at `T`: `L (2u − a − u²/b) + L (1/a − 1/b) (m² − a²)`
with `u = max a (min √P b)` and `m = min √P a`. -/
noncomputable def lpPayoff (L a b : ℝ) (T : ℝ≥0) : Payoff Unit :=
  let u : Payoff Unit := .max (.const a) (.min (sqrtObs T) (.const b))
  let m : Payoff Unit := .min (sqrtObs T) (.const a)
  .add (.mul (.const L) (.sub (.sub (.mul (.const 2) u) (.const a)) (.mul (.const b⁻¹) (.mul u u))))
    (.mul (.const (L * (a⁻¹ - b⁻¹))) (.sub (.mul m m) (.const (a ^ 2))))

end MathFin.DeFi
