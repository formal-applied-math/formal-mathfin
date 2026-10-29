/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import MathFin

/-!
# Using the library: put–call parity as a check on quoted prices

A worked use of the library from outside it, the way a desk checks a pair of quotes before trading
on them. A call and a put on the same underlying, strike and maturity are quoted. This file

1. records the quotes as data, with where they come from and what the check leaves out;
2. proves, in the library's payoff language (`MathFin.Contracts`), that a call pays a put plus a
   forward on every path (`pathPV_europeanCall_eq_put_add_forward`), so that long the call, short
   the put and short the forward pays nothing in any scenario;
3. prices the forward in a Black–Scholes market (`value_forward`) and recovers put–call parity
   `C − P = S₀ − K e^{−rT}` through the contract layer: the call is worth the put plus the forward
   (`value_europeanCall_eq_put_add_forward`), not because the two closed forms happen to subtract
   to it, as in `bs_put_call_parity`;
4. checks the illustrative quotes `sample` against parity, and finds them inconsistent.

`sample_checked` is the single statement the build certifies for `sample`: the portfolio pays
nothing on every path, its quoted cost is negative, and no Black–Scholes market with the sample's
spot and rate, whatever its volatility, prices both quotes.

## What the library supplies

* `MathFin.Contracts.europeanCall`, `europeanPut`, `forward`: the three contracts.
* `MathFin.Contracts.pathPV_europeanCall_eq_put_add_forward`: a call pays a put plus a forward,
  in every scenario.
* `MathFin.Contracts.value_europeanCall_eq_put_add_forward`: so it is worth the put plus the
  forward, in any model where both are integrable.
* `MathFin.Contracts.BlackScholes.value_forward`: the forward's Black–Scholes value.
* The closed forms `MathFin.Contracts.BlackScholes.value_europeanCall` and `value_europeanPut` are
  not needed: parity goes through `value_forward`, so the check holds whatever the volatility.

## What it does not

The sheet's `unmodelled` field lists what the check leaves out: bid–ask spreads, dividends and
borrow costs on the underlying, early exercise, and the difference between the quoted rate and the
rate at which the desk can actually lend and borrow. A parity violation on screen is a reason to
look, not a trade.

## Source

The shape of the file (the problem as data with an `unmodelled` list, the model admitted by proving
its hypotheses, one certified statement) follows the capped-call example
(`MathFinExamples/Applications/CappedCall.lean`). The quotes below are illustrative.
-/

namespace MathFin.Examples.PutCallParity

open MeasureTheory ProbabilityTheory MathFin.Contracts
open scoped NNReal

/-! ### The quotes, as data -/

/-- A call and a put on the same underlying, strike and maturity, as quoted, together with the
market data the check needs and what it leaves out. -/
structure QuoteSheet where
  /-- The spot price of the underlying. -/
  spot : ℝ
  /-- The continuously compounded short rate, per year. -/
  rate : ℝ
  /-- The common maturity, in years. -/
  maturity : ℝ≥0
  /-- The common strike. -/
  strike : ℝ
  /-- The quoted call price. -/
  call : ℝ
  /-- The quoted put price. -/
  put : ℝ
  spot_pos : 0 < spot
  strike_pos : 0 < strike
  maturity_pos : 0 < maturity
  /-- Where the numbers come from. -/
  sources : List String
  /-- What the check does not model. -/
  unmodelled : List String

namespace QuoteSheet

/-- The discount factor to maturity, `e^{−rT}`. -/
noncomputable def discount (q : QuoteSheet) : ℝ :=
  Real.exp (-q.rate * q.maturity)

/-- **The parity gap**: the quoted cost `C − P` of long the call and short the put, less the cost
`S₀ − K e^{−rT}` of the forward bought statically, by buying the underlying and borrowing the
discounted strike. -/
noncomputable def parityGap (q : QuoteSheet) : ℝ :=
  q.call - q.put - (q.spot - q.strike * q.discount)

/-- The portfolio parity trades: long the call, short the put, short the forward. -/
noncomputable def portfolio (q : QuoteSheet) : Contract Unit :=
  .both (europeanCall q.strike q.maturity)
    (.scale (-1) (.both (europeanPut q.strike q.maturity) (forward q.strike q.maturity)))

/-- **The portfolio pays nothing, on every path and for any discount.** The call pays exactly
what the put and the forward pay together (`pathPV_europeanCall_eq_put_add_forward`). No model is
involved. -/
theorem portfolio_pays_zero (q : QuoteSheet) (D : ℝ≥0 → ℝ) (s : Scenario Unit) :
    q.portfolio.pathPV D s = 0 := by
  rw [portfolio, Contract.pathPV_both, Contract.pathPV_scale,
    pathPV_europeanCall_eq_put_add_forward]
  ring

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **The quotes are Black–Scholes prices**: some volatility `σ > 0` and some standard normal
driver price the call and the put, at the sheet's spot and rate, at exactly the quoted values. -/
def IsBSConsistent (q : QuoteSheet) (Q : Measure Ω) : Prop :=
  ∃ σ > 0, ∃ Z : Ω → ℝ, HasLaw Z (gaussianReal 0 1) Q ∧
    (europeanCall q.strike q.maturity).value Q (fun _ ↦ q.discount)
        (BlackScholes.assets q.spot q.rate σ q.maturity Z) = q.call ∧
      (europeanPut q.strike q.maturity).value Q (fun _ ↦ q.discount)
        (BlackScholes.assets q.spot q.rate σ q.maturity Z) = q.put

/-- **Put–call parity, through the contracts.** If a Black–Scholes market prices both quotes, the
parity gap is `0`: the call is worth the put plus the forward
(`value_europeanCall_eq_put_add_forward`), and the forward is worth `S₀ − K e^{−rT}`
(`value_forward`). Neither closed form is used. -/
theorem parityGap_eq_zero {q : QuoteSheet} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (h : q.IsBSConsistent Q) : q.parityGap = 0 := by
  obtain ⟨σ, hσ, Z, hZ, hC, hP⟩ := h
  have hBS : BSCallHyp Q q.spot q.strike q.rate σ q.maturity Z :=
    ⟨q.spot_pos, q.strike_pos, hσ, NNReal.coe_pos.mpr q.maturity_pos, hZ⟩
  have hparity := value_europeanCall_eq_put_add_forward Q _ _
    (BlackScholes.integrable_europeanPut_pathPV hZ q.spot q.strike q.rate σ q.maturity)
    (BlackScholes.integrable_forward_pathPV hZ q.spot q.strike q.rate σ q.maturity)
  rw [discount] at hC hP
  rw [hC, hP, BlackScholes.value_forward hBS] at hparity
  rw [parityGap, discount, hparity]
  ring

end QuoteSheet

/-! ### The check -/

/-- Illustrative quotes: spot `100`, rate `5%`, one year, strike `100`, the call at `10.45` and the
put at `8.00`. At 20% volatility the Black–Scholes formulas give about `10.45` and `5.57` (a
numerical remark, not proved here); the put here is quoted far too rich. -/
noncomputable def sample : QuoteSheet where
  spot := 100
  rate := 0.05
  maturity := 1
  strike := 100
  call := 10.45
  put := 8
  spot_pos := by norm_num
  strike_pos := by norm_num
  maturity_pos := one_pos
  sources := ["illustrative screen quotes for a one-year at-the-money call and put"]
  unmodelled :=
    ["bid–ask spreads on the options and the underlying", "dividends on the underlying",
      "the cost of borrowing the underlying to sell it short", "early exercise of an American put",
      "the gap between the quoted rate and the desk's own lending and borrowing rates"]

/-- The sample's parity gap is negative: `100 e^{−0.05} ≤ 100 / 1.05 < 97.55`, from
`1 + x ≤ eˣ`. -/
theorem sample_parityGap_neg : sample.parityGap < 0 := by
  have h₁ : (1.05 : ℝ) ≤ Real.exp 0.05 := by linarith [Real.add_one_le_exp (0.05 : ℝ)]
  have h₂ : Real.exp (-0.05) * Real.exp 0.05 = 1 := by rw [← Real.exp_add]; norm_num
  have h₃ := Real.exp_pos (-0.05)
  simp only [QuoteSheet.parityGap, QuoteSheet.discount, sample, NNReal.coe_one, mul_one]
  rw [show -(0.05 : ℝ) = -0.05 by norm_num]
  nlinarith

/-- **The desk check for `sample`**, the statement this file's build certifies. Long the call,
short the put and short the forward pays nothing on every path. At the quoted prices, with the
forward costed at `S₀ − K e^{−rT}`, the portfolio's cost is negative. That would be an arbitrage
if the forward could be replicated at that cost; replication is not formalized here. And so no
Black–Scholes market with spot `100` and rate `5%`, whatever its volatility and on whatever
probability space, prices both quotes. -/
theorem sample_checked :
    (∀ (D : ℝ≥0 → ℝ) (s : Scenario Unit), sample.portfolio.pathPV D s = 0) ∧
      sample.parityGap < 0 ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q],
        ¬ sample.IsBSConsistent Q :=
  ⟨sample.portfolio_pays_zero, sample_parityGap_neg, fun _ _ h ↦
    sample_parityGap_neg.ne (QuoteSheet.parityGap_eq_zero h)⟩

end MathFin.Examples.PutCallParity
