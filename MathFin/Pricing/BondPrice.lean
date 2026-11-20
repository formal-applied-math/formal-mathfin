/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Pricing.Market

/-!
# The zero-coupon bond price

`bondPrice Q 𝓕 D t T = 𝔼_Q[D T ∣ 𝓕 t] / D t` is the zero-coupon bond price `P(t, T)`: the value at
`t` of one unit paid at `T`, for any stochastic discount factor `D`. It is the library's canonical
bond price (`tools/verify/trunk.toml`). In a market it is the market's price at `t` of the unit
payment (`bondPrice_deflator_eq_priceAt`). At `t = 0`, under a probability measure, with
`D 0 = 1` and no information at `0`, it is the zero curve `𝔼_Q[D T]`
(`bondPrice_zero_eq_zeroCurve`). When `D` is deterministic it is the ratio `D T / D t` under any
finite measure (`bondPrice_deterministic`), so a market whose numéraire is a deterministic `f`
prices the unit payment at `f t / f T` (`Market.priceAt_pay_one_of_numeraire`).

The Gaussian short-rate models compute it in closed form (`bondPrice_vasicek`,
`bondPrice_hullWhite`), the caplet is priced through it (`Models/Rates/Caplet.lean`), and the
deterministic bond formulas are tied to it in `Models/Rates/DeterministicMarket.lean`
(`Rates.bondPrice_exp_eq_zcb`, `Rates.bondPriceKeyRate_eq_sum_bondPrice`).

## Main definitions

* `bondPrice`: the zero-coupon bond price `P(t, T) = 𝔼_Q[D T ∣ 𝓕 t] / D t`.

## Main results

* `bondPrice_deflator_eq_priceAt`: at a market's deflator, `P(t, T)` is the market's price at `t`
  of one unit paid at `T`.
* `bondPrice_zero_eq_zeroCurve`: at `t = 0`, with `D 0 = 1` and trivial information at `0`,
  `P(0, T)` is the zero curve `zeroCurve Q D T`.
* `bondPrice_deterministic`: a deterministic discount factor gives `P(t, T) = D T / D t`.
* `Market.priceAt_pay_one_of_numeraire`: with a deterministic numéraire `f`, the market's price at
  `t` of one unit paid at `T` is `f t / f T`.

## References

* [D. Brigo and F. Mercurio, *Interest Rate Models --- Theory and Practice*][BrigoMercurio2006],
  sec. 1.2

## Tags

zero-coupon bond, bond price, discount factor, zero curve, conditional expectation, MSC 91G30,
JEL E43, JEL G12
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace MathFin.Contracts

variable {ι Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The **zero-coupon bond price at time `t`** under the stochastic discount factor `D`:
`P(t, T) = 𝔼_Q[D T | 𝓕 t] / D t`, the value at `t` of one unit paid at `T`. At `t = 0` with
`D 0 = 1` and a trivial `𝓕 0` it is the zero curve `zeroCurve Q D T`
(`bondPrice_zero_eq_zeroCurve`). -/
noncomputable def bondPrice (Q : Measure Ω) (𝓕 : Filtration ℝ≥0 mΩ) (D : ℝ≥0 → Ω → ℝ)
    (t T : ℝ≥0) : Ω → ℝ :=
  fun ω ↦ (Q[D T | 𝓕 t]) ω / D t ω

/-- **The bond price is the price at `t` of one unit paid at `T`**: in a market whose deflator
`N 0 / N t` is the discount factor, `P(t, T)` is `Market.priceAt` of the payment of `1` at `T`. -/
theorem bondPrice_deflator_eq_priceAt (M : Market ι Ω) (Q : Measure Ω) (t T : ℝ≥0) :
    bondPrice Q M.𝓕 M.deflator t T = M.priceAt Q t (.pay T (.const 1)) := by
  funext ω
  simp [Market.priceAt, bondPrice, Contract.pathPV, Contract.cashflows, Payoff.eval]

/-- **At time `0` the bond price is the zero curve**: with no information at `0` and `D 0 = 1`,
under a probability measure, `P(0, T) = 𝔼_Q[D T]`, the zero curve `zeroCurve Q D T`. -/
theorem bondPrice_zero_eq_zeroCurve (Q : Measure Ω) [IsProbabilityMeasure Q]
    (𝓕 : Filtration ℝ≥0 mΩ) (h𝓕 : 𝓕 0 = ⊥) (D : ℝ≥0 → Ω → ℝ) (hD : ∀ ω, D 0 ω = 1)
    (T : ℝ≥0) :
    bondPrice Q 𝓕 D 0 T = fun _ ↦ zeroCurve Q D T := by
  funext ω
  simp [bondPrice, h𝓕, condExp_bot, hD, zeroCurve]

/-- **A deterministic discount factor prices the bond by its ratio**: when the discount factor
`D` does not depend on the outcome, `P(t, T) = D T / D t` under any finite measure and any
information, on either side of maturity. The flat-rate bond `zcb` is this bond price at the curve
`e^{−rs}`, and the coupon bond at a yield and the key-rate price are sums of cash flows times it,
the key-rate price with one curve per cash flow (`Rates.bondPrice_exp_eq_zcb`,
`Rates.bondPriceDisc_eq_sum_bondPrice`, `Rates.bondPriceKeyRate_eq_sum_bondPrice`). -/
theorem bondPrice_deterministic (Q : Measure Ω) [IsFiniteMeasure Q] (𝓕 : Filtration ℝ≥0 mΩ)
    (D : ℝ≥0 → ℝ) (t T : ℝ≥0) :
    bondPrice Q 𝓕 (fun s _ ↦ D s) t T = fun _ ↦ D T / D t := by
  funext ω
  simp [bondPrice, condExp_const (𝓕.le t)]

end MathFin.Contracts

namespace MathFin.Market

open MathFin.Contracts

variable {ι Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **A deterministic numéraire prices the unit payment by its ratio**: if the numéraire is the
deterministic `f`, then under any finite measure the market's price at `t` of one unit paid at
`T` is `f t / f T`, on either side of `T` (`bondPrice_deflator_eq_priceAt`,
`bondPrice_deterministic`). -/
theorem priceAt_pay_one_of_numeraire {M : Market ι Ω} {f : ℝ≥0 → ℝ}
    (hf : ∀ t ω, M.numeraire t ω = f t) (Q : Measure Ω) [IsFiniteMeasure Q] (t T : ℝ≥0) :
    M.priceAt Q t (.pay T (.const 1)) = fun _ ↦ f t / f T := by
  rw [← bondPrice_deflator_eq_priceAt, funext₂ (deflator_of_numeraire hf),
    bondPrice_deterministic]
  funext ω
  have h0 : f 0 ≠ 0 := (hf 0 ω ▸ M.numeraire_pos 0 ω).ne'
  exact div_div_div_cancel_left' _ _ h0

end MathFin.Market
