/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import Mathlib
public import MathFin.Foundations.NoArbitrageDerivations

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
(`MathFin/Foundations/NoArbitrageDerivations.lean`), and
`bondForwardPrice_from_no_arbitrage` derives the forward price from it: in a
finite-state market whose state prices price the bond as its pre-expiry coupons
plus its value at `t_fe`, the forward contract paying `B(t_fe) - X` is worth
zero exactly at `X = bondForwardPrice`.

## Result

* `forwardValue`: the time-0 value of a forward contract struck at `X`.
* `bondForwardPrice`: the closed-form forward price
  `(P₀ - Σ Df(t)·CF(t)) / Df(t_fe)`.
* `forwardValue_eq_zero_iff_eq_bondForwardPrice`: `X` makes the forward's
  value zero iff `X = bondForwardPrice` — the no-arbitrage characterization.
* `bondForwardPrice_from_no_arbitrage`: the forward price derived from
  `forward_price_from_no_arbitrage`, with the coupon-stripped bond as the asset.
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

/-- **Bond forward price from no-arbitrage.** A finite-state market with state
prices `q` on the states `Ω` at the forward-expiry date `t_fe`: the zero-coupon
bond to `t_fe` costs `Df_fe = Σ q ω`, and the bond, worth `B ω` (ex-coupon) at
`t_fe` in state `ω`, is priced as its coupons paid up to `t_fe` plus its value
then, `P₀ = Σ Df(t)·CF(t) + Σ q ω · B ω`. Then the forward contract paying
`B - X` at `t_fe` is worth zero iff `X = bondForwardPrice`: this is
`forward_price_from_no_arbitrage` with the coupon-stripped bond
`P₀ - Σ Df(t)·CF(t)` as the spot. -/
theorem bondForwardPrice_from_no_arbitrage {Ω : Type*} (states : Finset Ω) (q B : Ω → ℝ)
    (s : Finset ι) (Df CF : ι → ℝ) (P0 Df_fe X : ℝ) (hDf : Df_fe ≠ 0)
    (h_zcb : ∑ ω ∈ states, q ω = Df_fe)
    (h_bond : P0 = ∑ t ∈ s, Df t * CF t + ∑ ω ∈ states, q ω * B ω) :
    ∑ ω ∈ states, q ω * (B ω - X) = 0 ↔ X = bondForwardPrice s Df CF P0 Df_fe :=
  forward_price_from_no_arbitrage states q B Df_fe _ X hDf h_zcb (by rw [h_bond]; ring)

end MathFin
