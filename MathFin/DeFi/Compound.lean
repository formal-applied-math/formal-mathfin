/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib

/-!
# Compound: utilization, affine borrow rate, cToken exchange-rate monotonicity

Adapted from the Compound whitepaper (Compound Labs, "Compound: The Money
Market Protocol", 2019), the Interest Rate Model section (utilization,
affine borrow rate) and the cToken Contracts / accrual sections (exchange
rate, reserve-factor accrual).

## Results

* `utilization`: `U = Borrows / (Cash + Borrows)`, matching the whitepaper's
  §2.3 definition exactly. (The deployed `BaseJumpRateModelV2` contract nets
  reserves out of the denominator, `Borrows / (Cash + Borrows − Reserves)`;
  this file follows the whitepaper, not that later on-chain refinement.)
* `utilization_mem_Icc`: for nonnegative cash and borrows, `U ∈ [0, 1]`.
* `borrowRate`: the affine rate `r = base + slope · U`, monotone in `U` when
  `slope ≥ 0`.
* `exchangeRate`: `(Cash + Borrows − Reserves) / TotalSupply`.
* `exchangeRate_mono`: the exchange rate is monotone nondecreasing as
  interest accrues, **under the explicit hypothesis that the reserve-factor
  cut does not exceed the accrued interest** (`reservesAdded ≤ interest`) —
  the whitepaper's reserve-factor accrual equations give this directly
  (`reservesAdded = interest · reserveFactor` with `reserveFactor ∈ [0,1]`),
  but state it as a standalone hypothesis on the accrued amounts rather than
  re-deriving it from `reserveFactor` each time.
-/

@[expose] public section

namespace MathFin

namespace DeFi

namespace Compound

/-- **Compound utilization rate**: the fraction of the pool's assets
(cash + outstanding borrows) that is currently borrowed out, per the
whitepaper's §2.3 definition. (The deployed interest-rate-model contract
additionally nets reserves out of the denominator; that refinement is not
formalized here.) -/
noncomputable def utilization (cash borrows : ℝ) : ℝ :=
  borrows / (cash + borrows)

/-- For nonnegative cash and borrows the utilization lies in `[0, 1]` (it is `0` for an
empty pool, by the `x / 0 = 0` convention). -/
theorem utilization_mem_Icc {cash borrows : ℝ} (hcash : 0 ≤ cash) (hborrows : 0 ≤ borrows) :
    utilization cash borrows ∈ Set.Icc 0 1 :=
  ⟨div_nonneg hborrows (add_nonneg hcash hborrows),
    div_le_one_of_le₀ (by linarith) (add_nonneg hcash hborrows)⟩

/-- **Compound affine borrow-rate model**: `r(U) = base + slope · U`. Takes
`U` directly (rather than `cash`/`borrows`) so it applies uniformly whether
`U` comes from `utilization` or from the on-chain reserves-netted refinement
noted on `utilization`. -/
def borrowRate (base slope U : ℝ) : ℝ :=
  base + slope * U

/-- **Borrow rate is monotone nondecreasing in utilization** when the
slope is nonnegative. -/
theorem borrowRate_monotone {base slope : ℝ} (hslope : 0 ≤ slope) :
    Monotone (borrowRate base slope) := by
  intro U V hUV
  unfold borrowRate
  gcongr

/-- **Compound cToken exchange rate**: the redeemable-underlying-per-cToken
rate `(Cash + Borrows − Reserves) / TotalSupply`. -/
noncomputable def exchangeRate (cash borrows reserves totalSupply : ℝ) : ℝ :=
  (cash + borrows - reserves) / totalSupply

/-- **cToken exchange-rate monotonicity under interest accrual.**
Suppose a period accrues `interest` of new borrows, of which
`reservesAdded` is cut to reserves. **Explicit hypothesis**
`reservesAdded ≤ interest` — the whitepaper's reserve-factor accrual equations give
this directly (`reservesAdded = interest · reserveFactor` with
`reserveFactor ∈ [0,1]`), but we state it as a standalone hypothesis on the
accrued amounts rather than re-deriving it from `reserveFactor` here. Under
it, and with cash and supply unchanged, the exchange rate after accrual is
at least the rate before. -/
theorem exchangeRate_mono
    {cash borrows reserves totalSupply interest reservesAdded : ℝ}
    (htotalSupply : 0 < totalSupply)
    (hreservesAdded : reservesAdded ≤ interest) :
    exchangeRate cash borrows reserves totalSupply ≤
      exchangeRate cash (borrows + interest) (reserves + reservesAdded) totalSupply := by
  unfold exchangeRate
  rw [div_le_div_iff_of_pos_right htotalSupply]
  linarith

end Compound

end DeFi

end MathFin
