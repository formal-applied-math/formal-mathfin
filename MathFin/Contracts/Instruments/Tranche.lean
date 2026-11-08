/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Contracts.Core

/-!
# A credit tranche leg, as a contract

The loss of the tranche `[a, d]` of a credit portfolio, as a fraction of its notional, is
`((L − a)⁺ − (L − d)⁺)/(d − a)` when the portfolio has lost the fraction `L`
(`tranchePayoff` in `Risk/Credit/TrancheLoss.lean`). Reading `L` as the single underlying `()` of
a scenario, that is a `Payoff`, and paying it at `T` is a `Contract`.

## Main definitions

* `trancheLossPayoff`: the tranche loss as a payoff on the portfolio loss observed at `T`.
* `trancheLeg`: the tranche loss paid at `T`.

## Scope

Only the definitions are here; that the leg's value is the discounted expected `tranchePayoff` is
the connector `MathFinFrontier.value_trancheLeg`.

## References

* [A. McNeil, R. Frey and P. Embrechts, *Quantitative Risk Management*][McNeilFreyEmbrechts],
  §11

## Tags

credit tranche, CDO, attachment point, detachment point, tranche loss, payoff language,
MSC 91G40, JEL G13
-/

@[expose] public section

open scoped NNReal

namespace MathFin.Contracts

/-- **The tranche loss as a payoff**: with the portfolio loss fraction `L` observed at `T`,
`((L − a)⁺ − (L − d)⁺)/(d − a)`. -/
noncomputable def trancheLossPayoff (a d : ℝ) (T : ℝ≥0) : Payoff Unit :=
  .mul (.const (d - a)⁻¹)
    (.sub (.max (.sub (.obs () T) (.const a)) (.const 0))
      (.max (.sub (.obs () T) (.const d)) (.const 0)))

/-- **The tranche leg**: the tranche loss `trancheLossPayoff a d T`, paid at `T`. -/
noncomputable def trancheLeg (a d : ℝ) (T : ℝ≥0) : Contract Unit :=
  .pay T (trancheLossPayoff a d T)

end MathFin.Contracts
