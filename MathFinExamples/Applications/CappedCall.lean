/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import MathFin

/-!
# Using the library: from a term sheet to a checked price

A worked use of the library from outside it, the way a pricing desk or a model validator would
use it. A term sheet describes a capped call on an index. This file

1. records the sheet's terms as data, each with the clause it comes from, together with the
   features of the instrument the formal contract leaves out;
2. writes the contract in the library's payoff language (`MathFin.Contracts`) and proves it pays
   what the payoff clause says, in every scenario;
3. admits a Black–Scholes market through a certificate, the hypothesis `BSCallHyp` that the
   pricing theorems ask for, built from a Brownian motion;
4. prices the contract by composing two call prices, and proves the price lies within the static
   bounds of the payoff: between `0` and the discounted width of the cap.

`sample_checked` is the single statement the build certifies for the illustrative sheet `sample`.

Step 4's bound is a fact about the Black–Scholes formula that the formula does not show: the call
price falls as the strike rises, by no more than the discounted strike gap. Here it comes from the
payoff, not from any property of `Φ`.

## What the library supplies

* `MathFin.Contracts.cappedCall`, `cappedCall_payoff_eq`: the contract and its payoff.
* `MathFin.Contracts.value_cappedCall`: its Black–Scholes value.
* `MathFin.BSCallHyp.of_isPreBrownian`: the model certificate, from a pre-Brownian motion.
* `MathFin.Contracts.Contract.pathPV_const`: a constant discount comes out of a present value.

## What it does not

The sheet's `unmodelled` field is part of the record, not a disclaimer. Settlement lags, the
issuer's credit, the index's dividends, fixing and disruption rules are outside the model, and a
reader of `sample_checked` should know they are.

## Source

Keeping the contract, its sources and its omissions as data, admitting the model through a
certificate, and certifying one aggregate statement follow Paul Bilokon, *The Contract Is Not the
Model* (working paper, 2026), and its code <https://github.com/thalesians/lean_contracts>. No code
is taken from it. The sheet below is illustrative, not a real instrument.
-/

namespace MathFin.Examples.CappedCall

open MeasureTheory ProbabilityTheory MathFin.Contracts
open scoped NNReal

/-! ### The term sheet, as data -/

/-- One clause of a term sheet: where it sits in the document, and what it says. -/
structure Clause where
  /-- The clause's place in the document, such as `"§2 Payoff"`. -/
  locator : String
  /-- What the clause says. -/
  text : String

/-- The terms of a capped call as a term sheet states them, with the clauses they come from and
the features of the instrument the formal contract leaves out. -/
structure CappedCallSheet where
  /-- The strike `K₁`. -/
  strike : ℝ
  /-- The cap level `K₂`: the payoff stops growing once the index passes it. -/
  cap : ℝ
  /-- The maturity, in years. -/
  maturity : ℝ≥0
  strike_pos : 0 < strike
  strike_le_cap : strike ≤ cap
  maturity_pos : 0 < maturity
  /-- The clauses the terms above are read from. -/
  sources : List Clause
  /-- Features of the instrument that the contract below does not model. -/
  unmodelled : List String

/-- An illustrative sheet: strike `100`, cap `120`, one year. -/
noncomputable def sample : CappedCallSheet where
  strike := 100
  cap := 120
  maturity := 1
  strike_pos := by norm_num
  strike_le_cap := by norm_num
  maturity_pos := one_pos
  sources :=
    [⟨"§2 Payoff", "At maturity the holder receives the index level less 100, floored at 0 and \
        capped at 20."⟩,
      ⟨"§3 Maturity", "The final fixing is one year after the trade date."⟩]
  unmodelled :=
    ["settlement two business days after the final fixing", "the issuer's credit risk",
      "dividends on the index", "the fixing source and market disruption events",
      "the day-count convention"]

/-! ### The model, admitted through a certificate -/

/-- A Black–Scholes market under a pricing measure `Q`: spot, short rate, volatility, and the
Brownian motion that drives the index. -/
structure BSMarket {Ω : Type*} {mΩ : MeasurableSpace Ω} (Q : Measure Ω) where
  spot : ℝ
  rate : ℝ
  vol : ℝ
  W : ℝ≥0 → Ω → ℝ
  spot_pos : 0 < spot
  vol_pos : 0 < vol
  brownian : IsPreBrownianReal W Q

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω}

namespace BSMarket

/-- The standard normal behind the index level at `T`: `W_T / √T`. -/
noncomputable def normal (m : BSMarket Q) (T : ℝ≥0) : Ω → ℝ :=
  fun ω ↦ m.W (T : ℝ).toNNReal ω / Real.sqrt T

/-- The index, read off at `T`. -/
noncomputable def index (m : BSMarket Q) (T : ℝ≥0) : Unit → ℝ≥0 → Ω → ℝ :=
  bsAssets m.spot m.rate m.vol T (m.normal T)

/-- The discount factor to `T`, as the constant curve the pricing theorems take: every cashflow
of the contracts priced here falls at `T`. -/
noncomputable def discountTo (m : BSMarket Q) (T : ℝ≥0) : ℝ≥0 → ℝ :=
  fun _ ↦ Real.exp (-m.rate * T)

/-- The Black–Scholes price of a call struck at `K` with maturity `T`. -/
noncomputable def call (m : BSMarket Q) (K : ℝ) (T : ℝ≥0) : ℝ :=
  m.spot * Phi (bsd1 m.spot K m.rate m.vol T)
    - K * Real.exp (-m.rate * T) * Phi (bsd2 m.spot K m.rate m.vol T)

/-- **The certificate.** At every positive strike and maturity, the market meets the hypothesis
of the Black–Scholes call formula. -/
theorem certificate [IsProbabilityMeasure Q] (m : BSMarket Q) {K : ℝ} (hK : 0 < K) {T : ℝ≥0}
    (hT : 0 < T) :
    BSCallHyp Q m.spot K m.rate m.vol T (m.normal T) :=
  BSCallHyp.of_isPreBrownian Q m.W m.brownian m.spot_pos hK m.vol_pos (NNReal.coe_pos.mpr hT)

end BSMarket

/-! ### The contract, its payoff and its price -/

namespace CappedCallSheet

/-- The contract the sheet describes: long a call at the strike, short a call at the cap. -/
noncomputable def contract (c : CappedCallSheet) : Contract Unit :=
  cappedCall c.strike c.cap c.maturity

/-- **The contract pays what the sheet says.** In every scenario, before discounting, it pays
`min (max (S_T − strike) 0) (cap − strike)`. -/
theorem contract_pays (c : CappedCallSheet) (s : Scenario Unit) :
    c.contract.pathPV (fun _ ↦ 1) s
      = min (max (s () c.maturity - c.strike) 0) (c.cap - c.strike) :=
  cappedCall_payoff_eq c.strike_le_cap s

/-- **The price.** In a Black–Scholes market, the contract is worth the call at the strike less
the call at the cap. -/
theorem value_contract [IsProbabilityMeasure Q] (c : CappedCallSheet)
    (m : BSMarket Q) :
    c.contract.value Q (m.discountTo c.maturity) (m.index c.maturity)
      = m.call c.strike c.maturity - m.call c.cap c.maturity :=
  value_cappedCall (m.certificate c.strike_pos c.maturity_pos)
    (m.certificate (c.strike_pos.trans_le c.strike_le_cap) c.maturity_pos)

/-- **The price respects the payoff's bounds.** The payoff lies between `0` and `cap − strike` in
every scenario, so its discounted expectation lies between `0` and `e^{−rT}·(cap − strike)`.
Only the payoff is used: no integrability, and no property of the call formula. -/
theorem value_mem_Icc [IsProbabilityMeasure Q] (c : CappedCallSheet) (m : BSMarket Q) :
    c.contract.value Q (m.discountTo c.maturity) (m.index c.maturity)
      ∈ Set.Icc 0 (Real.exp (-m.rate * c.maturity) * (c.cap - c.strike)) := by
  set e := Real.exp (-m.rate * c.maturity)
  have hb (s : Scenario Unit) :
      c.contract.pathPV (fun _ ↦ e) s ∈ Set.Icc 0 (e * (c.cap - c.strike)) := by
    rw [Contract.pathPV_const, c.contract_pays]
    have he : 0 ≤ e := (Real.exp_pos _).le
    exact ⟨mul_nonneg he (le_min (le_max_right _ _) (sub_nonneg.mpr c.strike_le_cap)),
      mul_le_mul_of_nonneg_left (min_le_right _ _) he⟩
  have hb' (ω : Ω) := hb (scenarioAt (m.index c.maturity) ω)
  rw [Contract.value, Set.mem_Icc]
  refine ⟨integral_nonneg fun ω ↦ (hb' ω).1, ?_⟩
  calc _ ≤ ∫ _, e * (c.cap - c.strike) ∂Q :=
        integral_mono_of_nonneg (ae_of_all _ fun ω ↦ (hb' ω).1) (integrable_const _)
          (ae_of_all _ fun ω ↦ (hb' ω).2)
    _ = e * (c.cap - c.strike) := by simp

end CappedCallSheet

/-! ### The check -/

/-- **The desk check for `sample`**, the statement this file's build certifies. In every
Black–Scholes market, the sample contract pays its §2 payoff in every scenario, is worth the
100-strike call less the 120-strike call, and that value lies between `0` and `20·e^{−r}`. -/
theorem sample_checked [IsProbabilityMeasure Q] (m : BSMarket Q) :
    (∀ s : Scenario Unit,
        sample.contract.pathPV (fun _ ↦ 1) s = min (max (s () 1 - 100) 0) (120 - 100)) ∧
      sample.contract.value Q (m.discountTo 1) (m.index 1) = m.call 100 1 - m.call 120 1 ∧
      sample.contract.value Q (m.discountTo 1) (m.index 1)
        ∈ Set.Icc 0 (Real.exp (-m.rate * (1 : ℝ≥0)) * (120 - 100)) :=
  ⟨sample.contract_pays, sample.value_contract m, sample.value_mem_Icc m⟩

end MathFin.Examples.CappedCall
