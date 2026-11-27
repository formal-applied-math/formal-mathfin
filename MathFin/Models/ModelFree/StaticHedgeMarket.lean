/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Init
public import MathFin.Pricing.StaticHedge
public import MathFin.Models.ModelFree.MarketCallPrice

/-!
# A piecewise-linear payoff is priced by the smile alone

In a market with a pricing measure, the price of a payoff `e` of the terminal asset that is a
continuous piecewise-linear function (the fragment `Payoff.IsPiecewiseLinear`) is read off the
prices of the bond, the forward and finitely many calls, with the weights of the static hedge that
`Payoff.staticHedge` compiles. No model of the asset enters: two markets with the same call prices
at the hedge's strikes, the same forward and the same discount give `pay T e` the same price.

With a unit numéraire and a positive asset, the call prices at the strikes `k F` in units of the
forward `F` are a normalised call price function (`Market.IsPricingMeasure.isNormalizedCallPrice`),
so the price of the payoff is `a + b F + F ∑ⱼ wⱼ c(Kⱼ / F)` for that function `c`
(`Market.IsPricingMeasure.exists_isNormalizedCallPrice_price_pay`): the payoff is priced by the
smile, and the smile is an object of the library's static no-arbitrage theory.

What is not claimed: that the call price function determines the price of a payoff outside the
fragment (that is the Carr–Madan spanning formula, `Models/ModelFree/CarrMadan.lean`, for smooth
payoffs), that the hedge is the cheapest or unique, or anything about dates other than `T`.

## Main results

* `Market.price_pay_eq_price_staticHedge`: in a market whose asset is nonnegative at `T`, `pay T e`
  and its compiled portfolio have the same price.
* `Market.IsPricingMeasure.price_pay_eq_smile`: under a pricing measure and a deterministic
  numéraire `f`, the price of `pay T e` is the bond amount times `f 0 / f T`, plus the forward
  amount times the forward's price, plus the weighted prices of the calls of the hedge.
* `Market.IsPricingMeasure.exists_isNormalizedCallPrice_price_pay`: with unit numéraire and a
  positive asset, the price of `pay T e` is `a + b F + F ∑ⱼ wⱼ c(Kⱼ / F)` for a normalised call
  price function `c`.

## References

* [P. Carr and D. Madan, *Towards a theory of volatility trading*][CarrMadan1998]
* [Roper, *Arbitrage free implied volatility surfaces*][Roper2010], Theorem 2.1
* [P. Bilokon, *The Contract Is Not the Model*][Bilokon2026]

## Tags

static hedge, model-free pricing, call price function, implied volatility smile, piecewise linear
payoff, pricing measure, MSC 91G20, JEL G13
-/

@[expose] public section

open MeasureTheory MathFin.Contracts
open scoped NNReal

namespace MathFin

namespace Market

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {M : Market Unit Ω} {T : ℝ≥0} {Q : Measure Ω}
  {e : Payoff Unit}

/-- **In a market, a piecewise-linear payoff has the price of its static hedge.** If the asset is
nonnegative at `T`, `pay T e` and the compiled portfolio of a bond, a forward and calls have the
same price, under any measure: no pricing measure is needed. -/
theorem price_pay_eq_price_staticHedge (h : e.IsPiecewiseLinear T)
    (hpos : ∀ ω, 0 ≤ M.asset () T ω) :
    M.price Q (.pay T e) = M.price Q ((e.staticHedge T).contract T) :=
  Contract.value_pay_eq_value_staticHedge M.deflator M.asset h hpos

/-- **A piecewise-linear payoff is priced by the bond, the forward and the calls.** Under a pricing
measure up to `T`, with a deterministic numéraire `f` and an asset nonnegative at `T`, the price of
`pay T e` is the bond amount times the bond price `f 0 / f T`, plus the forward amount times the
price of the forward, plus the call amounts times the prices of the calls, with the amounts and
strikes of the static hedge `e.staticHedge T`. -/
theorem IsPricingMeasure.price_pay_eq_smile {f : ℝ≥0 → ℝ} (hQ : M.IsPricingMeasure T Q)
    (hf : ∀ t ω, M.numeraire t ω = f t) (h : e.IsPiecewiseLinear T)
    (hpos : ∀ ω, 0 ≤ M.asset () T ω) :
    M.price Q (.pay T e) = (e.staticHedge T).bondAmount * (f 0 / f T)
      + (e.staticHedge T).forwardAmount * M.price Q (.pay T (.obs () T))
      + ((e.staticHedge T).calls.map fun p ↦ p.2 * M.price Q (europeanCall p.1 T)).sum := by
  have := hQ.isProb
  have hX : Integrable (fun ω ↦ f 0 / f T * M.asset () T ω) Q := by
    simpa only [deflator_of_numeraire hf] using
      hQ.integrable_deflator_mul_asset (n₀ := f 0) (fun ω ↦ hf 0 ω) ()
  simp only [price_eq_value_of_numeraire hf Q]
  rw [Contract.value_pay_eq_value_staticHedge _ M.asset h hpos,
    StaticHedge.value_contract (D := fun t ↦ f 0 / f t) (X := M.asset) (T := T) hX]

/-- **A piecewise-linear payoff is priced by the smile.** In a market with unit numéraire and a
positive asset, priced at `T` by `Q`, with forward `F`, there is a normalised call price function
`c` (convex, nonincreasing, between the intrinsic value and one, with limits one at `0` and zero at
infinity) such that the price of `pay T e` is `a + b F + F ∑ⱼ wⱼ c(Kⱼ / F)`, where `a` is the bond
amount, `b` the forward amount and `(Kⱼ, wⱼ)` the calls of the static hedge. The function `c` is
the market's call price function `k ↦ price (europeanCall (k F) T) / F` of
`IsPricingMeasure.isNormalizedCallPrice`. -/
theorem IsPricingMeasure.exists_isNormalizedCallPrice_price_pay (hQ : M.IsPricingMeasure T Q)
    (hN : ∀ t ω, M.numeraire t ω = 1) (hpos : ∀ ω, 0 < M.asset () T ω) {F : ℝ}
    (hF : F = M.price Q (.pay T (.obs () T))) (h : e.IsPiecewiseLinear T) :
    ∃ c : ℝ → ℝ, IsNormalizedCallPrice c ∧
      M.price Q (.pay T e) = (e.staticHedge T).bondAmount + (e.staticHedge T).forwardAmount * F
        + F * ((e.staticHedge T).calls.map fun p ↦ p.2 * c (p.1 / F)).sum := by
  have hF0 : 0 < F := by
    rw [hF]
    exact hQ.price_obs_pos hN hpos
  refine ⟨fun k ↦ M.price Q (europeanCall (k * F) T) / F,
    hQ.isNormalizedCallPrice hN hpos hF, ?_⟩
  have key := hQ.price_pay_eq_smile (f := fun _ ↦ (1 : ℝ)) hN h fun ω ↦ (hpos ω).le
  rw [← hF] at key
  have hcalls : ((e.staticHedge T).calls.map fun p ↦ p.2 * M.price Q (europeanCall p.1 T)).sum
      = F * ((e.staticHedge T).calls.map fun p ↦
          p.2 * (M.price Q (europeanCall (p.1 / F * F) T) / F)).sum := by
    rw [← List.sum_map_mul_left]
    refine congrArg List.sum (List.map_congr_left fun p _ ↦ ?_)
    show p.2 * M.price Q (europeanCall p.1 T)
      = F * (p.2 * (M.price Q (europeanCall (p.1 / F * F) T) / F))
    rw [div_mul_cancel₀ _ hF0.ne', mul_left_comm, mul_div_cancel₀ _ hF0.ne']
  rw [key, hcalls]
  simp only [div_one, mul_one]

end Market

end MathFin
