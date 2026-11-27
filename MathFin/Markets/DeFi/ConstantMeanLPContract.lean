/-
Copyright (c) 2026 Yang Ye. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yang Ye
-/
module

public import MathFin.Contracts.Core
public import MathFin.Pricing.Market
public import MathFin.Markets.DeFi.ConstantMeanAMM
public import MathFin.Markets.DeFi.LPContract
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Fin.VecNotation

/-!
# The constant-mean liquidity position, priced

The two-token constant-mean position of invariant `V = x^w y^(1-w)` (weights `w` on X and
`1 − w` on Y), marked at a price `P` of X in Y, is worth in token Y

  `V * P^w / (w^w * (1-w)^(1-w))`,

the pool re-balanced onto its invariant curve at that price,

the weighted generalization of the constant-product mark `2 √k √P`: at `w = 1/2` the value is
`2 V √P`, the constant-product position of invariant `V²` (`constantProductPayoff`), and at
the pool's own spot price it is `y / (1-w)`, the whitepaper's constant value distribution
`V^t = B_t / W_t`. This file reprices the position through the payoff language, the way
`LPContract.lean` reprices the constant-product and concentrated-liquidity positions:

* `constantMeanPayoff`: the position as a payoff on the price of X in Y observed at `T`.
* `eval_constantMeanPayoff_eq_reserves`: the marking identity — at the pool's spot price the
  payoff is worth exactly its reserves `x P + y`.
* `price_constantMeanPayoff`: paying the position at `T` is worth the discounted expectation
  of the closed-form mark, in any market with a positive price of X in Y at `T`.
* `price_constantMeanPayoff_eq_hodl`: in a market whose price of X in Y at `T` is the pool's spot
  price, the position is priced as its reserves `x P_T + y`.
* `constantMeanPayoff_one_half_eq_constantProductPayoff`: the equal-weight position *is* the
  constant-product payoff of invariant `V²`, tying the constant-mean line to the
  `thm:impermanent-loss` pricing line of `LPContract.lean`.

## Scope

Fee-free. The value is the whole-pool value (the `constantProductPayoff` precedent), not a
per-LP-token price. The payoff language has one underlying, so the `n`-token pool — whose
mark depends on several prices — is not covered: this is the two-token instance. The weight
is strictly between 0 and 1 in the theorems (the formula's limits at `w → 0, 1` are the pure
single-token holdings `V` and `V P`, outside the hypotheses).

## Main definitions

* `constantMeanPayoff`: the two-token constant-mean position as a payoff.

## Main results

* `eval_constantMeanPayoff`: the payoff is the closed form `V P^w / (w^w (1-w)^(1-w))`.
* `eval_constantMeanPayoff_eq_reserves`: at the pool's spot price the payoff is worth the
  reserves `x P + y`.
* `price_constantMeanPayoff`: the discounted-expectation price.
* `price_constantMeanPayoff_eq_hodl`: at the pool's spot price, the position is priced as its
  reserves.
* `constantMeanPayoff_one_half_eq_constantProductPayoff`: the `w = 1/2` reduction to
  `constantProductPayoff`.

## References

* [F. Martinelli, N. Mushegian, *Balancer: a non-custodial portfolio manager, liquidity
  provider, and price sensor*][MartinelliMushegian2019], "Theory": Value Function; Spot
  Price; Constant Value Distribution Proof (`V^t = B_t / W_t`, of which the marking identity
  is the two-token instance at the pool's own spot price).

## Tags

liquidity position, Balancer, constant mean invariant, weighted pool, payoff language,
MSC 91G80, JEL G23
-/

@[expose] public section

open scoped NNReal

namespace MathFin

namespace DeFi

open MathFin.Contracts MeasureTheory

/-- **The two-token constant-mean position** with invariant `V` and weight `w` on X, as a
payoff on the price of X in Y observed at `T`: `V P^w / (w^w (1-w)^(1-w))`, the weighted
generalization of `constantProductPayoff`'s `2 √k √P`. A value for `0 < V`, `0 < w < 1` and
a nonnegative price (at a negative base `Real.rpow` is junk); the theorems carry the
hypotheses. -/
noncomputable def constantMeanPayoff (V : ℝ) (w : ℝ≥0) (T : ℝ≥0) : Payoff Unit :=
  .mul (.const (V / ((w : ℝ) ^ (w : ℝ) * (1 - (w : ℝ)) ^ (1 - (w : ℝ)))))
    (.rpow (.obs () T) w)

/-- The payoff is its closed form: `V P^w / (w^w (1-w)^(1-w))`. -/
theorem eval_constantMeanPayoff (V : ℝ) (w : ℝ≥0) (T : ℝ≥0) (s : Scenario Unit) :
    (constantMeanPayoff V w T).eval s =
      V / ((w : ℝ) ^ (w : ℝ) * (1 - (w : ℝ)) ^ (1 - (w : ℝ))) * s () T ^ (w : ℝ) := by
  simp [constantMeanPayoff, Payoff.eval]

/-- **The marking identity**: a pool of reserves `x, y > 0` with weight `w` on X, marked at
its own spot price `P` of X in Y, is worth exactly its reserves `x P + y` in Y. This is the
constant-mean counterpart of `eval_constantProductPayoff`, and at the spot price it is
the whitepaper's constant value distribution: the value in Y is `y / (1-w) = B_Y / W_Y`. -/
theorem eval_constantMeanPayoff_eq_reserves (x y : ℝ) (w : ℝ≥0) (hx : 0 < x) (hy : 0 < y)
    (hw : 0 < w) (hw1 : (w : ℝ) < 1) (T : ℝ≥0) (s : Scenario Unit)
    (hspot : s () T = spotPrice (![x, y] : Fin 2 → ℝ) ![↑w, 1 - ↑w] 0 1) :
    (constantMeanPayoff (constantMeanInvariant ![x, y] ![↑w, 1 - ↑w]) w T).eval s
      = x * s () T + y := by
  have hwy : 0 < 1 - (w : ℝ) := by linarith
  have hwR : 0 < (w : ℝ) := by exact_mod_cast hw
  have hone : (1 - (w : ℝ)) + (w : ℝ) = 1 := by ring
  have hone' : (w : ℝ) + (1 - (w : ℝ)) = 1 := by ring
  have hspot' : s () T = (y / (1 - (w : ℝ))) / (x / (w : ℝ)) := by
    rw [hspot, spotPrice_pair]
  have hVeq : constantMeanInvariant ![x, y] ![↑w, 1 - ↑w]
      = x ^ (w : ℝ) * y ^ (1 - (w : ℝ)) :=
    constantMeanInvariant_pair x y (w : ℝ) (1 - (w : ℝ))
  have hye : y ^ (1 - (w : ℝ)) * y ^ (w : ℝ) = y := by
    rw [← Real.rpow_add hy (1 - (w : ℝ)) (w : ℝ)]
    simp only [hone, Real.rpow_one]
  have hwe : (1 - (w : ℝ)) ^ (1 - (w : ℝ)) * (1 - (w : ℝ)) ^ (w : ℝ) = 1 - (w : ℝ) := by
    rw [← Real.rpow_add hwy (1 - (w : ℝ)) (w : ℝ)]
    simp only [hone, Real.rpow_one]
  have hval : x * s () T + y = y / (1 - (w : ℝ)) := by
    rw [hspot']; field_simp
    ring
  rw [eval_constantMeanPayoff, hval, hspot', hVeq]
  rw [Real.div_rpow (div_pos hy hwy).le (div_pos hx hwR).le, Real.div_rpow hy.le hwy.le,
    Real.div_rpow hx.le hwR.le]
  field_simp [hx.ne', hwR.ne', hwy.ne', (Real.rpow_pos_of_pos hx _).ne',
    (Real.rpow_pos_of_pos hwR _).ne', (Real.rpow_pos_of_pos hwy _).ne']
  rw [show (1 - (w : ℝ)) * y ^ (1 - (w : ℝ)) * y ^ (w : ℝ)
      = (1 - (w : ℝ)) * (y ^ (1 - (w : ℝ)) * y ^ (w : ℝ)) from by ring, hye, hwe]

/-- **The price of the constant-mean position is the discounted expectation of its mark.**
Paying the position of invariant `V` and weight `w` at `T` is worth, under the measure `Q`, the
discounted expectation of the position's value at the observed price (its closed form is
`eval_constantMeanPayoff`). The statement is unconditional, an unfolding of the market's price
of a payment; the hypotheses `0 < V`, `0 < w < 1` and nonnegative prices matter only for
reading the mark as a position value. -/
theorem price_constantMeanPayoff {Ω : Type*} [MeasurableSpace Ω] (M : Market Unit Ω)
    (Q : Measure Ω) (T : ℝ≥0) (V : ℝ) (w : ℝ≥0) :
    M.price Q (.pay T (constantMeanPayoff V w T)) =
      ∫ ω, M.deflator T ω * (constantMeanPayoff V w T).eval (scenarioAt M.asset ω) ∂Q := by
  rw [Market.price, Contract.value_pay]

/-- **The constant-mean position is priced as its reserves at the pool's own spot price.** In a
market whose price of X in Y at `T` equals the pool's spot price `y / (1-w) / (x / w)` of a
pool with reserves `x, y > 0` and weight `w`, `Q`-almost surely, paying the position of the
pool's own invariant at `T` is worth paying its reserves: the price of the position equals
the price of the deposit claim `x P_T + y` (`hodlPayoff`). It is the marking identity
`eval_constantMeanPayoff_eq_reserves` integrated against the deflator, through
`Contract.value_pay`. -/
theorem price_constantMeanPayoff_eq_hodl {Ω : Type*} [MeasurableSpace Ω] (M : Market Unit Ω)
    (Q : Measure Ω) (T : ℝ≥0) {x y : ℝ} {w : ℝ≥0} (hx : 0 < x) (hy : 0 < y) (hw : 0 < w)
    (hw1 : (w : ℝ) < 1)
    (hspot : ∀ᵐ ω ∂Q, M.asset () T ω = spotPrice (![x, y] : Fin 2 → ℝ) ![↑w, 1 - ↑w] 0 1) :
    M.price Q (.pay T (constantMeanPayoff (constantMeanInvariant ![x, y] ![↑w, 1 - ↑w]) w T)) =
      M.price Q (.pay T (hodlPayoff x y T)) := by
  simp only [Market.price, Contract.value_pay]
  refine integral_congr_ae (hspot.mono fun ω h ↦ ?_)
  simp only [eval_hodlPayoff]
  exact congrArg _ (eval_constantMeanPayoff_eq_reserves x y w hx hy hw hw1 T _ h)

/-- **The equal-weight constant-mean position is the constant-product position**: the payoff
of invariant `V` at weight `1/2` is the payoff of invariant `V²`, the constant-product
position of `LPContract.lean`. This ties the constant-mean line to the priced
constant-product line of `thm:impermanent-loss`. -/
theorem constantMeanPayoff_one_half_eq_constantProductPayoff (V : ℝ) (hV : 0 < V) (T : ℝ≥0) :
    constantMeanPayoff V (1 / 2 : ℝ≥0) T = constantProductPayoff (V ^ 2) T := by
  have hhalf : ((1 : ℝ) / 2) ^ ((1 : ℝ) / 2) * ((1 : ℝ) / 2) ^ ((1 : ℝ) / 2) = 1 / 2 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 1 / 2) _ _, show (1 : ℝ) / 2 + (1 : ℝ) / 2 = 1
      from by norm_num, Real.rpow_one]
  have hsqrt : Real.sqrt (V ^ 2) = V := Real.sqrt_sq hV.le
  have hcoe : (((1 : ℝ≥0) / 2 : ℝ≥0) : ℝ) = 1 / 2 := by norm_num
  simp only [constantMeanPayoff, constantProductPayoff, sqrtObs, hsqrt, hcoe]
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 from by norm_num, hhalf]
  field_simp

end DeFi

end MathFin
