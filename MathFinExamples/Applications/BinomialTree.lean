/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import MathFin

/-!
# Using the library: a binomial tree you can trust

A worked use of the library from outside it, the way a course or a model validator would check a
binomial tree before pricing on it. A tree is trustworthy when:
- it admits no arbitrage;
- its price for a claim is what it costs to hedge that claim;
- it prices the underlying and the bond correctly, so put–call parity holds on it;
- it is consistent with the continuous model it approximates.

This file checks the first three on a sample tree and the fourth on a separate CRR market:

1. records a one-period tree as data (spot, strike, up and down factors, rate per step), with what
   it leaves out;
2. proves its no-arbitrage condition `d < eʳ < u` from the numbers (`sample_noArb`), using only
   `1 + x ≤ eˣ`;
3. prices a call on it, and proves the price is the cost of a hedge, `½` a share and a short bond,
   that pays the call in both states (`TreeSheet.hedge`, `sample_price`);
4. applies put–call parity `C − P = S − K e^{−nr}` on the `n`-step tree
   (`binomialPrice_callPut_parity`), which follows from the linearity of the tree price and the
   fact that the tree prices the stock at spot and cash at its discount;
5. applies the Cox–Ross–Rubinstein → Black–Scholes limit to the trees of a concrete market,
   discharging its no-arbitrage hypothesis at every step from `|r|√T < σ` (`market_tendsto_bs`).

`sample_checked` is the single statement the build certifies.

## What the library supplies

* `MathFin.BinomialNoArb`: the no-arbitrage condition.
* `MathFin.binomialOptionPriceOnePeriod`, `replicating_portfolio_cost`, `replicating_payoff_up`,
  `replicating_payoff_down`: the one-period price and its hedge.
* `MathFin.binomialPrice_callPut_parity`: put–call parity on the `n`-step tree, from
  `binomialPrice_add`, `binomialPrice_smul`, `binomialPrice_id` and `binomialPrice_const`.
* `MathFin.binomialNoArb_crr`, `binomialPrice_call_tendsto_bs_closed`: the CRR trees are
  arbitrage-free when `|r|√T < σ`, and their call prices converge to the Black–Scholes price.

## What it does not

The trees model one asset with a constant up and down factor and a constant rate; there are no
dividends, transaction costs or bid–ask spreads, and the hedge is rebalanced only at the tree's
dates. The limit says the CRR prices converge, not how fast: it gives no error bound for a given
number of steps.

## Source

The shape of the file follows the capped-call example
(`MathFinExamples/Applications/CappedCall.lean`). The numbers below are illustrative.
-/

namespace MathFin.Examples.BinomialTree

open Filter
open scoped Topology

/-! ### The tree, as data -/

/-- A one-period binomial tree for a call: the spot, the strike, the up and down factors, and the
continuously compounded rate per step, with what the tree leaves out. -/
structure TreeSheet where
  spot : ℝ
  strike : ℝ
  /-- The factor the underlying moves by in the up state. -/
  up : ℝ
  /-- The factor the underlying moves by in the down state. -/
  down : ℝ
  /-- The continuously compounded rate per step. -/
  rate : ℝ
  spot_pos : 0 < spot
  /-- Where the numbers come from. -/
  sources : List String
  /-- What the tree does not model. -/
  unmodelled : List String

namespace TreeSheet

/-- The call's payoff in the up state. -/
noncomputable def callUp (t : TreeSheet) : ℝ := max (t.spot * t.up - t.strike) 0

/-- The call's payoff in the down state. -/
noncomputable def callDown (t : TreeSheet) : ℝ := max (t.spot * t.down - t.strike) 0

/-- The call's one-period price: its discounted risk-neutral expectation. -/
noncomputable def price (t : TreeSheet) : ℝ :=
  binomialOptionPriceOnePeriod t.up t.down t.rate t.callUp t.callDown

/-- The hedge's position in the underlying, `Δ = (V_u − V_d) / (S (u − d))`. -/
noncomputable def shares (t : TreeSheet) : ℝ :=
  (t.callUp - t.callDown) / (t.spot * (t.up - t.down))

/-- The hedge's position in the bond, at its time-`0` value. -/
noncomputable def bond (t : TreeSheet) : ℝ :=
  Real.exp (-t.rate) * (t.up * t.callDown - t.down * t.callUp) / (t.up - t.down)

/-- **The price is the cost of a hedge.** On an arbitrage-free tree, `Δ` shares and the bond
position cost the tree price today, and pay the call in the up state and in the down state. -/
theorem hedge (t : TreeSheet) (h : BinomialNoArb t.up t.down t.rate) :
    t.shares * t.spot + t.bond = t.price ∧
      t.shares * (t.spot * t.up) + t.bond * Real.exp t.rate = t.callUp ∧
      t.shares * (t.spot * t.down) + t.bond * Real.exp t.rate = t.callDown :=
  ⟨replicating_portfolio_cost t.spot_pos h, replicating_payoff_up t.spot_pos h,
    replicating_payoff_down t.spot_pos h⟩

end TreeSheet

/-- Illustrative numbers: spot `100`, strike `100`, the underlying up `10%` or down `10%` over
one step, and a rate of `1%` per step. -/
noncomputable def sample : TreeSheet where
  spot := 100
  strike := 100
  up := 1.1
  down := 0.9
  rate := 0.01
  spot_pos := by norm_num
  sources := ["illustrative: a one-step tree for an at-the-money call"]
  unmodelled :=
    ["dividends on the underlying", "transaction costs and bid–ask spreads",
      "moves other than up or down by the stated factors", "a rate that changes over the step"]

/-- **The sample tree admits no arbitrage**: `0.9 < e^{0.01} < 1.1`, from `1 + x ≤ eˣ` at `0.01`
and at `−0.01`. -/
theorem sample_noArb : BinomialNoArb sample.up sample.down sample.rate := by
  have h₁ : (1.01 : ℝ) ≤ Real.exp 0.01 := by linarith [Real.add_one_le_exp (0.01 : ℝ)]
  have h₂ : (0.99 : ℝ) ≤ Real.exp (-0.01) := by linarith [Real.add_one_le_exp (-0.01 : ℝ)]
  have h₃ : Real.exp 0.01 * Real.exp (-0.01) = 1 := by rw [← Real.exp_add]; norm_num
  refine ⟨by norm_num [sample], by simp only [sample]; linarith, ?_⟩
  simp only [sample]
  nlinarith [Real.exp_pos (0.01 : ℝ)]

/-- **The sample call's price, and its hedge.** The call pays `10` up and `0` down. It costs
`50 − 45 e^{−0.01}`, about `5.45` (a numerical remark, not proved): half a share, and a bond
position worth `−45 e^{−0.01}` today. -/
theorem sample_price :
    sample.shares = 1 / 2 ∧ sample.bond = -45 * Real.exp (-0.01) ∧
      sample.price = 50 - 45 * Real.exp (-0.01) := by
  have hUp : sample.callUp = 10 := by norm_num [TreeSheet.callUp, sample]
  have hDown : sample.callDown = 0 := by norm_num [TreeSheet.callDown, sample]
  have hΔ : sample.shares = 1 / 2 := by
    rw [TreeSheet.shares, hUp, hDown]
    norm_num [sample]
  have hB : sample.bond = -45 * Real.exp (-0.01) := by
    rw [TreeSheet.bond, hUp, hDown]
    norm_num [sample]
    ring
  refine ⟨hΔ, hB, ?_⟩
  rw [← (sample.hedge sample_noArb).1, hΔ, hB]
  norm_num [sample]
  ring

/-! ### The trees of a market, and their limit -/

/-- **The CRR trees of a market with volatility `20%`, rate `5%` and a one-year horizon price the
at-the-money call, in the limit, at the Black–Scholes price.** Spot and strike are `100`. The
trees' no-arbitrage condition holds at every step because `|r|√T = 0.05 < 0.2 = σ`
(`binomialNoArb_crr`). -/
theorem market_tendsto_bs :
    Tendsto (fun n : ℕ ↦ binomialPrice (crrUp 0.2 1 n) (crrDown 0.2 1 n)
        (crrPerStepRate 0.05 1 n) (fun x ↦ max (x - 100) 0) n 100) atTop
      (𝓝 (100 * Phi (bsd1 100 100 0.05 0.2 1)
        - 100 * Real.exp (-(0.05 * 1)) * Phi (bsd2 100 100 0.05 0.2 1))) := by
  have hrT : |(0.05 : ℝ)| * Real.sqrt 1 < 0.2 := by
    rw [Real.sqrt_one, abs_of_pos (by norm_num)]
    norm_num
  exact binomialPrice_call_tendsto_bs_closed (by norm_num) one_pos (by norm_num) (by norm_num)
    fun _ hn ↦ binomialNoArb_crr one_pos hrT hn

/-! ### The check -/

/-- **The check for the sample tree and market**, the statement this file's build certifies:
- the sample tree admits no arbitrage;
- the call's price on it is `50 − 45 e^{−0.01}`;
- half a share and the bond cost that price and pay the call in both states;
- put–call parity holds on every `n`-step version of the tree;
- the CRR trees of a separate market (`σ = 20%`, `r = 5%`, `T = 1`, `S = K = 100`) converge to
  its Black–Scholes call price. -/
theorem sample_checked :
    BinomialNoArb sample.up sample.down sample.rate ∧
      sample.price = 50 - 45 * Real.exp (-0.01) ∧
      (sample.shares * sample.spot + sample.bond = sample.price ∧
        sample.shares * (sample.spot * sample.up) + sample.bond * Real.exp sample.rate
          = sample.callUp ∧
        sample.shares * (sample.spot * sample.down) + sample.bond * Real.exp sample.rate
          = sample.callDown) ∧
      (∀ n : ℕ, binomialPrice sample.up sample.down sample.rate (fun x ↦ max (x - 100) 0) n 100
          - binomialPrice sample.up sample.down sample.rate (fun x ↦ max (100 - x) 0) n 100
        = 100 - 100 * Real.exp (-(n : ℝ) * sample.rate)) ∧
      Tendsto (fun n : ℕ ↦ binomialPrice (crrUp 0.2 1 n) (crrDown 0.2 1 n)
          (crrPerStepRate 0.05 1 n) (fun x ↦ max (x - 100) 0) n 100) atTop
        (𝓝 (100 * Phi (bsd1 100 100 0.05 0.2 1)
          - 100 * Real.exp (-(0.05 * 1)) * Phi (bsd2 100 100 0.05 0.2 1))) :=
  ⟨sample_noArb, sample_price.2.2, sample.hedge sample_noArb,
    fun n ↦ by rw [binomialPrice_callPut_parity sample_noArb]; ring, market_tendsto_bs⟩

end MathFin.Examples.BinomialTree
