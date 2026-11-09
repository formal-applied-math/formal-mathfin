/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib
public import MathFin.DeFi.UniswapMechanics
public import MathFin.RiskMeasures.DiscreteVaR

/-!
# Historical-simulation value-at-risk for a Uniswap v3 concentrated-liquidity position

Historical-simulation VaR revalues today's position under each of `n` historical scenarios for the
risk factor, treats the resulting `n` hypothetical losses as equally likely (`1/n` each), and
reports the empirical `α`-quantile of that loss distribution — the standard methodology of
P. Jorion, *Value at Risk* (3rd ed., 2007), ch. 10 "VAR Methods" — applied here to a Uniswap v3
concentrated-liquidity LP position (`MathFin.DeFi.v3PositionValue`,
`MathFin/DeFi/UniswapMechanics.lean`) whose risk factor is the square-root price `√P`.

This file does **not** model fees, re-ranging, or multi-day return compounding: a genuine
"99%/10-day" VaR additionally needs a horizon-scaling convention applied to the `n` historical
scenarios themselves (e.g. overlapping 10-day log-return windows), which is a modeling choice made
upstream of this file on the scenario data, not a theorem about the risk measure. What is
formalized is the historical-simulation *risk measure applied to the position's deterministic value
function*, reusing the general finite-law VaR machinery of `MathFin.DiscreteVaR`
(`RiskMeasures/DiscreteVaR.lean`) rather than re-deriving quantile mechanics, together with the
already-proved Uniswap v3 virtual-reserve curve (`MathFin/DeFi/UniswapMechanics.lean`). The two
theorems below rest only on the position's value being nonnegative and linear in liquidity — true
of any such value function, not special to the concentrated-liquidity range shape — so they do not
yet use the v3 curve's own monotonicity in price. A genuine "VaR is the full revaluation at the
empirical price quantile" result is future work, not claimed here.

## Main definitions

* `historicalScenarioLoss`: the loss of a v3 position, marked today at square-root price `s0`,
  under a historical scenario `i` whose square-root price is `scenarios i`.
* `clHistoricalVaR`: the historical-simulation VaR of the position — `MathFin.DiscreteVaR.finiteVaR`
  of `historicalScenarioLoss` at `MathFin.DiscreteVaR.uniformWeights`.

## Main results

* `clHistoricalVaR_const_mul`: historical VaR scales with liquidity restricted to `c ≥ 0` (positive
  homogeneity, the sign restriction VaR itself needs) — scaling the liquidity deployed to a range by
  a nonnegative factor (holding the range and the historical scenarios fixed) scales its
  historical-simulation VaR by the same factor, via `MathFin.DeFi.v3PositionValue_const_mul`
  (linear in `L` for any real `c`) and `MathFin.DiscreteVaR.finiteVaR_const_mul`.
* `clHistoricalVaR_le_value`: historical VaR never exceeds the position's current mark-to-market
  value — a concentrated-liquidity LP position is worth at least `0` at every price
  (`v3PositionValue_nonneg`), so no historical scenario's loss can exceed today's value, and VaR is
  attained at a loss value (`MathFin.DiscreteVaR.finiteVaR_eq_value_min`,
  via `MathFin.DiscreteVaR.finiteVaR_le_of_forall_le`).

## References

* H. Adams, N. Zinsmeister, M. Salem, R. Keefer, D. Robinson, *Uniswap v3 Core* (2021), §2, §6.4.1.
* P. Jorion, *Value at Risk: The New Benchmark for Managing Financial Risk*, 3rd ed. (2007),
  ch. 10 "VAR Methods" (historical simulation).
-/

@[expose] public section

namespace MathFin

namespace DeFi

open MathFin.DiscreteVaR Set

/-! ## Historical-simulation VaR -/

/-- **Historical-simulation loss**: the loss of a v3 position with liquidity `L` on range `[a, b]`,
marked today at square-root price `s0`, under historical scenario `i`'s square-root price
`scenarios i`. Positive when the scenario's price move decreases the position's value. -/
noncomputable def historicalScenarioLoss (L a b s0 : ℝ) {n : ℕ} (scenarios : Fin n → ℝ)
    (i : Fin n) : ℝ :=
  v3PositionValue L a b s0 - v3PositionValue L a b (scenarios i)

/-- **Historical-simulation VaR** of a v3 concentrated-liquidity position: the `finiteVaR` of
`historicalScenarioLoss` at the equal weights `uniformWeights n hn` — the empirical `α`-quantile of
`n` historical hypothetical losses, each equally likely. -/
noncomputable def clHistoricalVaR (L a b s0 : ℝ) {n : ℕ} (hn : 0 < n) (scenarios : Fin n → ℝ)
    (α : ℝ) : ℝ :=
  finiteVaR (uniformWeights n hn) (historicalScenarioLoss L a b s0 scenarios) α

/-- **Historical VaR scales with deployed liquidity.** Holding the range `[a, b]`, the mark `s0`
and the historical scenarios fixed, scaling the liquidity `L` by a nonnegative factor `c` scales the
position's historical-simulation VaR by the same factor: the loss function scales by `c` pointwise
(`v3PositionValue_const_mul`), and VaR is positively homogeneous in the loss
(`MathFin.DiscreteVaR.finiteVaR_const_mul`). -/
theorem clHistoricalVaR_const_mul {n : ℕ} (hn : 0 < n) (L a b s0 : ℝ)
    (scenarios : Fin n → ℝ) {α : ℝ} (hα : α ∈ Ioo (0 : ℝ) 1) {c : ℝ} (hc : 0 ≤ c) :
    clHistoricalVaR (c * L) a b s0 hn scenarios α
      = c * clHistoricalVaR L a b s0 hn scenarios α := by
  have hloss : historicalScenarioLoss (c * L) a b s0 scenarios
      = fun i ↦ c * historicalScenarioLoss L a b s0 scenarios i := by
    funext i
    unfold historicalScenarioLoss
    rw [v3PositionValue_const_mul, v3PositionValue_const_mul, mul_sub]
  unfold clHistoricalVaR
  rw [hloss]
  exact finiteVaR_const_mul hα hc

/-- **Historical VaR never exceeds the position's current value.** A v3 position's value is always
nonnegative (`v3PositionValue_nonneg`), so no historical scenario can produce a loss larger than
today's mark `v3PositionValue L a b s0` — and VaR is attained at a loss value
(`MathFin.DiscreteVaR.finiteVaR_eq_value_min`, via `MathFin.DiscreteVaR.finiteVaR_le_of_forall_le`).
-/
theorem clHistoricalVaR_le_value {n : ℕ} (hn : 0 < n) {L a b : ℝ} (hL : 0 ≤ L) (ha : 0 < a)
    (hab : a ≤ b) (s0 : ℝ) (scenarios : Fin n → ℝ) {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    clHistoricalVaR L a b s0 hn scenarios α ≤ v3PositionValue L a b s0 :=
  finiteVaR_le_of_forall_le hα0 hα1 fun _ ↦ sub_le_self _ (v3PositionValue_nonneg hL ha hab)

end DeFi

end MathFin
