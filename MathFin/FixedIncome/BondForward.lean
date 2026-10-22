/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib

/-!
# Bond forward price by cash-and-carry replication

A forward contract on a coupon bond, struck at forward price `X`, maturing at
the forward-expiry date `t_fe`, is replicated by buying the bond today and
financing the purchase to `t_fe`, keeping every coupon `CF(t)` paid at
`t ≤ t_fe` along the way (worth `Df(t) · CF(t)` today). No-arbitrage
forces the forward contract's value at inception to be zero: discounting the
strike `X` paid at `t_fe` back to today must equal the bond's price net of the
discounted coupons it sheds before `t_fe`,

  `Df(t_fe) · X = P₀ - Σ_{t ≤ t_fe} Df(t) · CF(t)`,

equivalently (the usual forward-price statement)

  `X = (P₀ - Σ_{t ≤ t_fe} Df(t) · CF(t)) / Df(t_fe)`.

Here `s` is the caller-supplied set of coupon dates in `(0, t_fe]`; nothing in
`Finset ι` itself enforces that range, so passing it correctly is the
caller's responsibility. The coupon-stripped spot `P₀ - Σ Df(t)·CF(t)` plays
the role of `S₀` in `forward_price_from_no_arbitrage`
(`MathFin/Foundations/NoArbitrageDerivations.lean`); this module states the
replication identity as a definition (`bondForwardPrice`) and proves it is
exactly the strike making the forward contract's time-0 value zero — the
no-arbitrage characterization — without re-deriving the replication argument
itself.

## Result

* `forwardValue`: the time-0 value of a forward contract struck at `X`.
* `bondForwardPrice`: the closed-form forward price
  `(P₀ - Σ Df(t)·CF(t)) / Df(t_fe)`.
* `forwardValue_eq_zero_iff_eq_bondForwardPrice`: `X` makes the forward's
  value zero iff `X = bondForwardPrice` — the no-arbitrage characterization.
-/

@[expose] public section

namespace MathFin

variable {ι : Type*}

/-- Time-0 value of a forward contract on a bond, struck at `X`: the
discounted strike against the bond's spot price net of the discounted
coupons shed before the forward-expiry date. Positive means the long forward
position has positive value; the no-arbitrage strike sets this to zero. -/
noncomputable def forwardValue (s : Finset ι) (Df : ι → ℝ) (CF : ι → ℝ)
    (P0 Df_fe X : ℝ) : ℝ :=
  P0 - ∑ t ∈ s, Df t * CF t - Df_fe * X

/-- The **bond forward price**: the replication-implied strike
`X = (P₀ - Σ Df(t)·CF(t)) / Df(t_fe)`. -/
noncomputable def bondForwardPrice (s : Finset ι) (Df : ι → ℝ) (CF : ι → ℝ)
    (P0 Df_fe : ℝ) : ℝ :=
  (P0 - ∑ t ∈ s, Df t * CF t) / Df_fe

/-- **No-arbitrage characterization**: a strike `X` prices the forward
contract to zero value iff it equals `bondForwardPrice`. -/
theorem forwardValue_eq_zero_iff_eq_bondForwardPrice (s : Finset ι) (Df CF : ι → ℝ)
    (P0 Df_fe : ℝ) (hDf : Df_fe ≠ 0) (X : ℝ) :
    forwardValue s Df CF P0 Df_fe X = 0 ↔ X = bondForwardPrice s Df CF P0 Df_fe := by
  unfold forwardValue bondForwardPrice
  rw [sub_eq_zero, eq_div_iff hDf, mul_comm, eq_comm]

end MathFin
