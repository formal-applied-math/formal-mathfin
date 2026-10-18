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
Market Protocol", 2019, <https://compound.finance/documents/Compound.Whitepaper.pdf>),
the utilization/interest-rate model (§"Interest Rate Model") and the cToken
exchange-rate mechanics (§"The cToken Contracts").

## Results

* `utilization`: `U = Borrows / (Cash + Borrows)` — the whitepaper's formula
  is `Borrows / (Cash + Borrows − Reserves)`; we state the reserves-free
  simplification (equivalent to `Reserves = 0`) and disclose it here rather
  than silently dropping the term.
* `borrowRate`: the affine rate `r = base + slope · U`, monotone in `U` when
  `slope ≥ 0`.
* `exchangeRate`: `(Cash + Borrows − Reserves) / TotalSupply`.
* `exchangeRate_mono`: the exchange rate is monotone nondecreasing as
  interest accrues, **under the explicit hypothesis that the reserve
  factor cut does not exceed the accrued interest** (`reservesAdded ≤
  interest`) — the whitepaper states the reserve factor is a fraction
  `< 1` of interest but never spells out this inequality as a standalone
  hypothesis, so we state it as one rather than assume it silently.
-/

@[expose] public section

namespace MathFin

namespace DeFi

namespace Compound

/-- **Compound utilization rate**: the fraction of the pool's assets
(cash + outstanding borrows) that is currently borrowed out. **Scope
disclosure**: the whitepaper's formula nets out reserves,
`Borrows / (Cash + Borrows − Reserves)`; this definition is the
`Reserves = 0` simplification. -/
noncomputable def utilization (cash borrows : ℝ) : ℝ :=
  borrows / (cash + borrows)

/-- **Compound affine borrow-rate model**: `r(U) = base + slope · U`. -/
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
Suppose a period accrues `interest ≥ 0` of new borrows, of which
`reservesAdded ≥ 0` is cut to reserves. **Explicit hypothesis**
`reservesAdded ≤ interest` — this is the fact that the reserve factor is a
genuine *fraction* (`< 1`, in fact `≤ 1`) of the interest, which the
Compound whitepaper states qualitatively ("a portion of the interest...
is allocated to the Reserves") but never isolates as the standalone
inequality this lemma depends on; we make it an explicit hypothesis rather
than bake it into the model. Under it, and with cash and supply unchanged,
the exchange rate after accrual is at least the rate before. -/
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
