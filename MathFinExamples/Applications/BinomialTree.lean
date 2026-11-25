/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin

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
   it leaves out; the sample is the one-step Cox–Ross–Rubinstein tree of a market with `σ = 20%`,
   `r = 5%`, `T = 1`;
2. proves its no-arbitrage condition `d < eʳ < u` (`sample_noArb`) from `|r| √T < σ`
   (`binomialNoArb_crr`);
3. prices a call on it, and proves the price is the cost of a hedge, a share fraction and a short
   bond,
   that pays the call in both states (`TreeSheet.hedge`, `sample_price`), and is the only such
   position, so the only arbitrage-free price (`TreeSheet.hedge_unique`);
4. applies put–call parity `C − P = S − K e^{−nr}` on the `n`-step tree
   (`binomialPrice_callPut_parity`), which follows from the linearity of the tree price and the
   fact that the tree prices the stock at spot and cash at its discount;
5. builds the sample tree as a `Market` (one step a year, a fair coin as the physical law), with
   every hypothesis discharged: the risk-neutral law is a pricing measure, and every pricing
   measure prices the one-year call at the tree price (`sampleMarket_checked`);
6. applies the Cox–Ross–Rubinstein → Black–Scholes limit to the trees of a concrete market,
   discharging its no-arbitrage hypothesis at every step from `|r|√T < σ` (`market_tendsto_bs`).

`sample_checked` is the single statement the build certifies.

## What the library supplies

* `MathFin.BinomialNoArb`: the no-arbitrage condition.
* `MathFin.binomialOptionPriceOnePeriod`, `replicating_portfolio_cost`, `replicating_payoff_up`,
  `replicating_payoff_down`, `binomial_replicatingPortfolio_unique`,
  `binomial_replication_cost_eq_price`: the one-period price, its hedge, and their uniqueness.
* `MathFin.binomialPrice_callPut_parity`: put–call parity on the `n`-step tree, from
  `binomialPrice_add`, `binomialPrice_smul`, `binomialPrice_id` and `binomialPrice_const`.
* `MathFin.Contracts.Binomial.market`, `isPricingMeasure_coinFlipMeasure`,
  `price_pay_eq_binomialPrice_of_isPricingMeasure`: the tree as a market, its pricing measure, and
  the price every pricing measure gives.
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

@[expose] public section

namespace MathFin.Examples.BinomialTree

open Filter
open scoped Topology NNReal

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

/-- **The hedge is the only one, and its cost the only arbitrage-free price.** On an
arbitrage-free tree, any position of `Δ` shares and `B` in the bond that pays the call in both
states is the hedge `shares`, `bond` (`binomial_replicatingPortfolio_unique`), and so costs the tree
price (`binomial_replication_cost_eq_price`): a different price would be an arbitrage. -/
theorem hedge_unique (t : TreeSheet) (h : BinomialNoArb t.up t.down t.rate) {Δ B : ℝ}
    (hup : Δ * (t.spot * t.up) + B * Real.exp t.rate = t.callUp)
    (hdown : Δ * (t.spot * t.down) + B * Real.exp t.rate = t.callDown) :
    Δ = t.shares ∧ B = t.bond ∧ Δ * t.spot + B = t.price := by
  obtain ⟨p, -, hp⟩ := binomial_replicatingPortfolio_unique (V_u := t.callUp) (V_d := t.callDown)
    t.spot_pos h
  obtain ⟨h₁, h₂⟩ := Prod.mk.inj ((hp (Δ, B) ⟨hup, hdown⟩).trans
    (hp (t.shares, t.bond) ⟨(t.hedge h).2.1, (t.hedge h).2.2⟩).symm)
  exact ⟨h₁, h₂, binomial_replication_cost_eq_price t.spot_pos h hup hdown⟩

end TreeSheet

/-- The one-step Cox–Ross–Rubinstein tree of a market with volatility `20%` and rate `5%` over a
one-year horizon: spot `100`, strike `100`, the up and down factors `crrUp 0.2 1 1 = e^{0.2}` and
`crrDown 0.2 1 1 = e^{−0.2}`, and the rate per step `crrPerStepRate 0.05 1 1 = 0.05`. -/
noncomputable def sample : TreeSheet where
  spot := 100
  strike := 100
  up := crrUp 0.2 1 1
  down := crrDown 0.2 1 1
  rate := crrPerStepRate 0.05 1 1
  spot_pos := by norm_num
  sources := ["illustrative: the one-step CRR tree (σ = 20%, r = 5%, T = 1), at the money"]
  unmodelled :=
    ["dividends on the underlying", "transaction costs and bid–ask spreads",
      "moves other than up or down by the stated factors", "a rate that changes over the step"]

theorem sample_spot : sample.spot = 100 := rfl

theorem sample_strike : sample.strike = 100 := rfl

theorem sample_up : sample.up = Real.exp 0.2 := by simp [sample, crrUp, crrStep]

theorem sample_down : sample.down = Real.exp (-0.2) := by simp [sample, crrDown, crrStep]

theorem sample_rate : sample.rate = 0.05 := by simp [sample, crrPerStepRate, crrStep]

/-- **The sample tree admits no arbitrage**: `|r| √T = 0.05 < 0.2 = σ` (`binomialNoArb_crr`). -/
theorem sample_noArb : BinomialNoArb sample.up sample.down sample.rate := by
  have hrT : |(0.05 : ℝ)| * Real.sqrt 1 < 0.2 := by
    rw [Real.sqrt_one, abs_of_pos (by norm_num)]
    norm_num
  exact binomialNoArb_crr one_pos hrT one_pos

/-- **The sample call's price, and its hedge.** With `a = e^{0.2}` the call pays `100 (a − 1)` up
and `0` down. It costs `100 (a − e^{−0.05}) / (a + 1)`: `a / (a + 1)` of a share, and a bond
position worth `−100 e^{−0.05} / (a + 1)` today. -/
theorem sample_price :
    sample.shares = Real.exp 0.2 / (Real.exp 0.2 + 1) ∧
      sample.bond = -(100 * Real.exp (-0.05)) / (Real.exp 0.2 + 1) ∧
      sample.price = 100 * (Real.exp 0.2 - Real.exp (-0.05)) / (Real.exp 0.2 + 1) := by
  have ha : 1 < Real.exp 0.2 := Real.one_lt_exp.2 (by norm_num)
  have hb : Real.exp (-0.2) < 1 := Real.exp_lt_one (by norm_num)
  have hab : Real.exp 0.2 * Real.exp (-0.2) = 1 := by rw [← Real.exp_add]; norm_num
  have hne : Real.exp 0.2 + 1 ≠ 0 := by positivity
  have hsub : Real.exp 0.2 - Real.exp (-0.2) ≠ 0 := by linarith
  have hUp : sample.callUp = 100 * (Real.exp 0.2 - 1) := by
    rw [TreeSheet.callUp, sample_spot, sample_strike, sample_up]
    exact max_eq_left (by linarith)
  have hDown : sample.callDown = 0 := by
    rw [TreeSheet.callDown, sample_spot, sample_strike, sample_down]
    exact max_eq_right (by linarith)
  have hΔ : sample.shares = Real.exp 0.2 / (Real.exp 0.2 + 1) := by
    rw [TreeSheet.shares, hUp, hDown, sample_spot, sample_up, sample_down,
      div_eq_div_iff (mul_ne_zero (by norm_num) hsub) hne]
    linear_combination 100 * hab
  have hB : sample.bond = -(100 * Real.exp (-0.05)) / (Real.exp 0.2 + 1) := by
    rw [TreeSheet.bond, hUp, hDown, sample_rate, sample_up, sample_down,
      div_eq_div_iff hsub hne]
    linear_combination (-100 * Real.exp (-0.05) * Real.exp 0.2) * hab
  refine ⟨hΔ, hB, ?_⟩
  rw [← (sample.hedge sample_noArb).1, hΔ, hB, sample_spot, div_mul_eq_mul_div, ← add_div]
  congr 1
  ring

/-! ### The tree as a market -/

/-- The risk-neutral up-probability of the sample tree,
`(e^{0.05} − e^{−0.2}) / (e^{0.2} − e^{−0.2})`. -/
noncomputable def sampleQ : ℝ≥0 :=
  ⟨crrUpProb sample.up sample.down sample.rate, (crrUpProb_mem_Ioo sample_noArb).1.le⟩

theorem sampleQ_le_one : sampleQ ≤ 1 :=
  (crrUpProb_mem_Ioo sample_noArb).2.le

/-- The fair coin, the physical law of the sample market's flips. -/
noncomputable def fairCoin : MeasureTheory.Measure (ℕ → Bool) :=
  coinFlipMeasure (1 / 2) (by norm_num)

/-- **The sample tree as a market**: one step a year, the spot after the flips, the money market
`e^{0.05 n}` as numéraire, and a fair coin as the physical law. -/
noncomputable def sampleMarket : Market Unit (ℕ → Bool) :=
  Contracts.Binomial.market fairCoin sample.spot sample.up sample.down sample.rate (h := 1)
    zero_le_one

/-- **The sample market, with every hypothesis discharged.** Its risk-neutral law is a pricing
measure at the one-year horizon, though the physical law is a fair coin, and every pricing measure
prices the one-year call at the tree price `sample.price`. No-arbitrage is `sample_noArb`. -/
theorem sampleMarket_checked :
    sampleMarket.IsPricingMeasure 1 (coinFlipMeasure sampleQ sampleQ_le_one) ∧
      ∀ Q, sampleMarket.IsPricingMeasure 1 Q →
        sampleMarket.price Q (Contracts.europeanCall sample.strike 1) = sample.price := by
  refine ⟨Contracts.Binomial.isPricingMeasure_coinFlipMeasure sampleQ_le_one sample_noArb rfl _
    zero_le_one (p := 1 / 2) (by norm_num) (by norm_num) 1, fun Q hQ ↦ ?_⟩
  rw [sampleMarket, Contracts.europeanCall,
    Contracts.Binomial.price_pay_eq_binomialPrice_of_isPricingMeasure (by norm_num [sample])
      sample_noArb one_pos (T := 1) (N := 1) (by norm_num)
      (a := Contracts.europeanCallPayoff sample.strike 1)
      (g := fun S ↦ max (S - sample.strike) 0) (fun _ ↦ rfl) hQ]
  exact (binomialPrice_succ _ _ _ _ 0 _).trans rfl

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
- the call's price on it is `100 (e^{0.2} − e^{−0.05}) / (e^{0.2} + 1)`;
- half a share and the bond cost that price and pay the call in both states;
- put–call parity holds on every `n`-step version of the tree;
- the sample tree, as a market under a fair coin, is priced by its risk-neutral law, and every
  pricing measure prices the call at the tree price;
- the CRR trees of a separate market (`σ = 20%`, `r = 5%`, `T = 1`, `S = K = 100`) converge to
  its Black–Scholes call price. -/
theorem sample_checked :
    BinomialNoArb sample.up sample.down sample.rate ∧
      sample.price = 100 * (Real.exp 0.2 - Real.exp (-0.05)) / (Real.exp 0.2 + 1) ∧
      (sample.shares * sample.spot + sample.bond = sample.price ∧
        sample.shares * (sample.spot * sample.up) + sample.bond * Real.exp sample.rate
          = sample.callUp ∧
        sample.shares * (sample.spot * sample.down) + sample.bond * Real.exp sample.rate
          = sample.callDown) ∧
      (∀ n : ℕ, binomialPrice sample.up sample.down sample.rate (fun x ↦ max (x - 100) 0) n 100
          - binomialPrice sample.up sample.down sample.rate (fun x ↦ max (100 - x) 0) n 100
        = 100 - 100 * Real.exp (-(n : ℝ) * sample.rate)) ∧
      (sampleMarket.IsPricingMeasure 1 (coinFlipMeasure sampleQ sampleQ_le_one) ∧
        ∀ Q, sampleMarket.IsPricingMeasure 1 Q →
          sampleMarket.price Q (Contracts.europeanCall sample.strike 1) = sample.price) ∧
      Tendsto (fun n : ℕ ↦ binomialPrice (crrUp 0.2 1 n) (crrDown 0.2 1 n)
          (crrPerStepRate 0.05 1 n) (fun x ↦ max (x - 100) 0) n 100) atTop
        (𝓝 (100 * Phi (bsd1 100 100 0.05 0.2 1)
          - 100 * Real.exp (-(0.05 * 1)) * Phi (bsd2 100 100 0.05 0.2 1))) :=
  ⟨sample_noArb, sample_price.2.2, sample.hedge sample_noArb,
    fun n ↦ by rw [binomialPrice_callPut_parity sample_noArb]; ring, sampleMarket_checked,
    market_tendsto_bs⟩

end MathFin.Examples.BinomialTree
