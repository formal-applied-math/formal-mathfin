/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Pricing.Market
public import MathFin.Probability.Martingales.StoppingRule

/-!
# The American price of an exercise right

An American claim gives its holder the right to choose when, up to a horizon `T`, to receive a
cash flow: exercising at `t` pays the payoff `g t`, which observes the market's assets at its own
dates. In a market `M` under a measure `Q`, its price is the value of the optimal stopping problem
of the deflated cash flow `N₀ / N_t · (g t)(S)`: the supremum, over the stopping rules of the
market's filtration bounded by `T`, of its `Q`-expectation (`stoppingValue`,
`Probability/Martingales/StoppingRule.lean`). The same definition serves a continuous-time market
and a discrete one read through `DiscreteMarket.toMarket`.

Waiting to the horizon is one of the rules, and its expected exercise value is the
`Market.price` of the European contract `Contract.pay T (g T)`; so the European price is at most
the American price whenever the expected exercise values are bounded above.

Like `Market.price`, the definition is total: it is a price when `Q` is a pricing measure, the
exercise payoffs observe the assets no later than the exercise date, and the expected exercise
values are integrable and bounded above. As a bare `sSup` it is `0` when they are unbounded; the
lemmas carry the bound they need.

## Main definitions

* `Market.exerciseValue`: the deflated cash flow `N₀ / N_t · (g t)(S)` of exercising at `t`.
* `Market.americanPrice`: the supremum of its `Q`-expectation over the market's stopping rules
  bounded by `T`.

## Main results

* `Market.integral_le_americanPrice`: if the expected exercise values of all rules are bounded
  above, each of them is at most the American price.
* `Market.americanPrice_le`: a bound on the expected exercise values of all rules bounds the
  American price.
* `Market.price_pay_le_americanPrice`: under the same bound, the price of the European contract
  paying `g T` at `T` is at most the American price; `Market.price_europeanPut_le_americanPrice` is
  the put, whose exercise right is the family `europeanPutPayoff K`.

## References

* [I. Karatzas and S. E. Shreve, *Methods of Mathematical Finance*][KaratzasShreve1998], §2.5
* [H. Föllmer and A. Schied, *Stochastic Finance*][FollmerSchied], §6.1
* [G. Peskir and A. Shiryaev, *Optimal Stopping and Free-Boundary Problems*][PeskirShiryaev2006]

## Tags

American option, early exercise, exercise right, optimal stopping, stopping rule, numéraire,
pricing measure, MSC 91G20, MSC 60G40, JEL G13
-/

@[expose] public section

open MeasureTheory Set MathFin.Contracts
open scoped NNReal

namespace MathFin.Market

variable {ι Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The deflated cash flow of exercising the right `g` at time `t`: the payoff `g t`, evaluated
on the market's asset paths, times the deflator `N₀ / N_t`. -/
noncomputable def exerciseValue (M : Market ι Ω) (g : ℝ≥0 → Payoff ι) (t : ℝ≥0)
    (ω : Ω) : ℝ :=
  M.deflator t ω * (g t).eval (scenarioAt M.asset ω)

/-- **The American price** under `Q` of the right to receive `g t` at a time `t ≤ T` of the
holder's choosing: the supremum, over the stopping rules of the market's filtration bounded by
`T`, of the expected deflated cash flow `𝔼_Q[N₀ / N_τ · (g τ)(S)]`. It is a price when `Q` is a
pricing measure and the expected exercise values are integrable and bounded above; otherwise it
is `stoppingValue`'s junk value. -/
noncomputable def americanPrice (M : Market ι Ω) (Q : Measure Ω) (g : ℝ≥0 → Payoff ι)
    (T : ℝ≥0) : ℝ :=
  stoppingValue Q M.𝓕 (M.exerciseValue g) T

variable {M : Market ι Ω} {Q : Measure Ω} {g : ℝ≥0 → Payoff ι} {T : ℝ≥0} {C : ℝ}

/-- If the expected exercise values of all rules are at most `C`, each of them is at most the
American price. -/
theorem integral_le_americanPrice
    (hC : ∀ θ : StoppingRule M.𝓕 T, ∫ ω, M.exerciseValue g (θ.time ω) ω ∂Q ≤ C)
    (θ : StoppingRule M.𝓕 T) :
    ∫ ω, M.exerciseValue g (θ.time ω) ω ∂Q ≤ M.americanPrice Q g T :=
  integral_le_stoppingValue (fun η _ ↦ hC η) (mem_univ θ)

/-- A bound on the expected exercise values of all rules bounds the American price. -/
theorem americanPrice_le
    (hC : ∀ θ : StoppingRule M.𝓕 T, ∫ ω, M.exerciseValue g (θ.time ω) ω ∂Q ≤ C) :
    M.americanPrice Q g T ≤ C :=
  stoppingValue_le univ_nonempty fun θ _ ↦ hC θ

/-- **The European claim is worth at most the American one.** If the expected exercise values of
all rules are bounded above, the price of the contract paying `g T` at `T` is at most the American
price: waiting to the horizon is a stopping rule, and its expected exercise value is that price. -/
theorem price_pay_le_americanPrice
    (hC : ∀ θ : StoppingRule M.𝓕 T, ∫ ω, M.exerciseValue g (θ.time ω) ω ∂Q ≤ C) :
    M.price Q (.pay T (g T)) ≤ M.americanPrice Q g T := by
  simpa [price, Contract.value_pay, exerciseValue, StoppingRule.constant] using
    integral_le_americanPrice hC (.constant M.𝓕 T T le_rfl)

/-- **The American put is worth at least the European put.** Its exercise right is the family of
European put payoffs `t ↦ max (K − S_t) 0`; under a bound on the expected exercise values, the
price of `europeanPut K T` is at most its American price. -/
theorem price_europeanPut_le_americanPrice {M : Market Unit Ω} {K : ℝ}
    (hC : ∀ θ : StoppingRule M.𝓕 T,
      ∫ ω, M.exerciseValue (europeanPutPayoff K) (θ.time ω) ω ∂Q ≤ C) :
    M.price Q (europeanPut K T) ≤ M.americanPrice Q (europeanPutPayoff K) T :=
  price_pay_le_americanPrice hC

end MathFin.Market
