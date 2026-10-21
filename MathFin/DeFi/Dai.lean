/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib

/-!
# Dai (MakerDAO): liquidation inequality and stability-fee compounding

Adapted from the MakerDAO whitepaper (Maker, "The Maker Protocol:
MakerDAO's Multi-Collateral Dai (MCD) System", 2020,
<https://makerdao.com/en/whitepaper>): the collateralization /
liquidation criterion from the "Liquidation of Risky Maker Vaults" section,
and the "Liquidation Ratio" / "Stability Fee" parameter entries under
"Risk Parameters Controlled by Maker Governance" (these are named
parameter entries, not sub-sections of the paper).

## Results

* `isLiquidatable`: the predicate `collateral / debt < liquidationRatio`.
* `isLiquidatable_iff_mul`: cross-multiplied equivalent form (no division), for
  `debt > 0`.
* `debt_eq_debt_zero_mul_pow`: the compounding recurrence
  `debt (n+1) = debt n · (1 + fee)` has closed form `debt n = debt 0 · (1+fee)^n`.
-/

@[expose] public section

namespace MathFin

namespace DeFi

namespace Dai

/-- **Dai liquidation predicate**: a vault is liquidatable once its
collateralization ratio `collateral / debt` falls below the protocol's
liquidation ratio. -/
noncomputable def isLiquidatable (collateral debt liquidationRatio : ℝ) : Prop :=
  collateral / debt < liquidationRatio

/-- **Division-free equivalent** of the liquidation predicate, valid when
debt is positive: `collateral / debt < LR ↔ collateral < LR · debt`. -/
theorem isLiquidatable_iff_mul
    {collateral debt liquidationRatio : ℝ} (hdebt : 0 < debt) :
    isLiquidatable collateral debt liquidationRatio ↔ collateral < liquidationRatio * debt := by
  unfold isLiquidatable
  rw [div_lt_iff₀ hdebt]

/-- **Dai stability-fee compounding**: given a vault-debt sequence
satisfying `debt (n+1) = debt n · (1 + fee)` at every step, the debt after
`n` periods equals the initial debt compounded at the per-period stability
fee, `debt n = debt 0 · (1 + fee)^n`. Proved by induction on `n`. -/
theorem debt_eq_debt_zero_mul_pow
    (debt : ℕ → ℝ) (fee : ℝ)
    (hrec : ∀ n, debt (n + 1) = debt n * (1 + fee)) :
    ∀ n, debt n = debt 0 * (1 + fee) ^ n
  | 0 => by simp
  | (n + 1) => by
      rw [hrec n, debt_eq_debt_zero_mul_pow debt fee hrec n, pow_succ]
      ring

end Dai

end DeFi

end MathFin
