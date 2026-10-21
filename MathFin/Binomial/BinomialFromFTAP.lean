/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.Foundations.FTAPTwoState
public import MathFin.Bridges.PricingKernel
public import MathFin.Binomial.ReplicatingUniqueness

/-!
# The one-period binomial price is the two-state FTAP pricing kernel

`Binomial/Model.lean` defines the one-period price `binomialOptionPriceOnePeriod` directly as
`e^{−r}·(q·V_u + (1−q)·V_d)` with `q = crrUpProb u d r = (e^r − d)/(u − d)`, and checks it
against the replicating portfolio. `Foundations/FTAPTwoState.lean` builds, from the sign data of
a two-state excess-return market `(z_up, z_down)`, the backward-FTAP martingale weights
`emmWeightUp = −z_down/(z_up − z_down)` and `emmWeightDown = z_up/(z_up − z_down)` (after Nagy,
SSRN 6336503, 2026, Thm 7.3), and `Bridges/PricingKernel.lean` discounts them into state prices
and the linear pricing functional `pricingKernel_two_state`.

This file connects the two. Under `BinomialNoArb u d r` the binomial excess returns
`z_up = u − e^r > 0`, `z_down = d − e^r < 0` satisfy the FTAP sign condition, the FTAP weights
are `q` and `1 − q` (`binomial_q_eq_emm`, `binomial_emmWeightDown_eq`), and therefore the
binomial price is the pricing-kernel price
(`binomialOptionPriceOnePeriod_eq_pricingKernel`). With the uniqueness of the replicating
portfolio (`Binomial.ReplicatingUniqueness`) this gives the law of one price in both readings:
every replicating portfolio costs the FTAP state-price value of the claim
(`binomial_replication_cost_eq_pricingKernel`).

Scope: one period, two states; the definition of `binomialOptionPriceOnePeriod` is unchanged,
and what is proved is that it agrees with the kernel built from the FTAP weights.

## Results

* `binomial_excess_return_signs`, `binomial_emm_exists`, `binomial_no_arbitrage`: the FTAP
  sign condition, an EMM, and no arbitrage for the binomial excess-return market.
* `binomial_q_eq_emm`, `binomial_emmWeightDown_eq`: the FTAP weights are `q` and `1 − q`.
* `binomialOptionPriceOnePeriod_eq_pricingKernel`: the binomial price is the two-state
  pricing kernel `pricingKernel_two_state (u − e^r) (d − e^r) r`.
* `binomial_replication_cost_eq_pricingKernel`: every replicating portfolio costs that price.
-/

@[expose] public section

namespace MathFin

/-- **Excess-return signs from `BinomialNoArb`**: under `d < e^r < u`,
the up-state excess return `z_u = u − e^r > 0` and the down-state
excess return `z_d = d − e^r < 0`. -/
theorem binomial_excess_return_signs {u d r : ℝ} (h : BinomialNoArb u d r) :
    0 < u - Real.exp r ∧ d - Real.exp r < 0 :=
  ⟨sub_pos.mpr h.lt_u, sub_neg.mpr h.d_lt⟩

/-- **EMM existence in the binomial market** (Nagy 2026 §7 applied to the
binomial excess-return market). Under `BinomialNoArb`, the excess-return
vector `(u − e^r, d − e^r)` satisfies the sign condition of Nagy's
backward FTAP (Theorem 7.3), so an EMM exists. -/
theorem binomial_emm_exists {u d r : ℝ} (h : BinomialNoArb u d r) :
    HasEMM_two_state (u - Real.exp r) (d - Real.exp r) :=
  emm_of_signs (u - Real.exp r) (d - Real.exp r)
    (binomial_excess_return_signs h).1 (binomial_excess_return_signs h).2

/-- **The FTAP up-weight is the binomial up-probability**: for the excess returns
`z_u = u − e^r`, `z_d = d − e^r`,

  `emmWeightUp z_u z_d = −z_d / (z_u − z_d) = (e^r − d) / (u − d) = crrUpProb u d r`.

An identity of the two definitions (no hypothesis is needed; `z_u − z_d = u − d`). -/
theorem binomial_q_eq_emm (u d r : ℝ) :
    emmWeightUp (u - Real.exp r) (d - Real.exp r) = crrUpProb u d r := by
  rw [emmWeightUp, crrUpProb, sub_sub_sub_cancel_right, neg_sub]

/-- **The FTAP down-weight is `1 − q`**: under `BinomialNoArb`,
`emmWeightDown (u − e^r) (d − e^r) = (u − e^r)/(u − d) = 1 − crrUpProb u d r`. -/
theorem binomial_emmWeightDown_eq {u d r : ℝ} (h : BinomialNoArb u d r) :
    emmWeightDown (u - Real.exp r) (d - Real.exp r) = 1 - crrUpProb u d r := by
  rw [one_sub_crrUpProb h, emmWeightDown, sub_sub_sub_cancel_right]

/-- **No-arbitrage in the binomial market** (forward FTAP applied):
`BinomialNoArb` ⟹ no portfolio can produce a sure non-negative excess
return with at least one strictly positive outcome. -/
theorem binomial_no_arbitrage {u d r : ℝ} (h : BinomialNoArb u d r) :
    ¬ HasArbitrage_two_state (u - Real.exp r) (d - Real.exp r) :=
  noArbitrage_of_emm _ _ (binomial_emm_exists h)

/-- **The one-period binomial price is the FTAP pricing kernel.** Under `BinomialNoArb`, the
risk-neutral price `e^{−r}·(q·V_u + (1−q)·V_d)` equals the two-state state-price value
`ψ_up·V_u + ψ_down·V_d` whose state prices `ψ = e^{−r}·(emmWeightUp, emmWeightDown)` are the
discounted backward-FTAP weights of the excess returns `(u − e^r, d − e^r)`. -/
theorem binomialOptionPriceOnePeriod_eq_pricingKernel {u d r : ℝ} (h : BinomialNoArb u d r)
    (V_u V_d : ℝ) :
    binomialOptionPriceOnePeriod u d r V_u V_d =
      pricingKernel_two_state (u - Real.exp r) (d - Real.exp r) r V_u V_d := by
  simp only [pricingKernel_two_state, statePricePricing, statePrices_two_state,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    binomial_q_eq_emm, binomial_emmWeightDown_eq h, binomialOptionPriceOnePeriod]
  ring

/-- **Law of one price, FTAP form.** Under `BinomialNoArb` and `S₀ > 0`, every portfolio
`(Δ, B)` replicating `(V_u, V_d)` costs the FTAP state-price value of the claim:
`Δ·S₀ + B = pricingKernel_two_state (u − e^r) (d − e^r) r V_u V_d`. Combines the uniqueness
of the replicating portfolio (`binomial_replication_cost_eq_price`) with
`binomialOptionPriceOnePeriod_eq_pricingKernel`. -/
theorem binomial_replication_cost_eq_pricingKernel {S₀ u d r V_u V_d Δ B : ℝ} (hS₀ : 0 < S₀)
    (h : BinomialNoArb u d r) (h_up : Δ * (S₀ * u) + B * Real.exp r = V_u)
    (h_down : Δ * (S₀ * d) + B * Real.exp r = V_d) :
    Δ * S₀ + B = pricingKernel_two_state (u - Real.exp r) (d - Real.exp r) r V_u V_d :=
  (binomial_replication_cost_eq_price hS₀ h h_up h_down).trans
    (binomialOptionPriceOnePeriod_eq_pricingKernel h V_u V_d)

end MathFin
