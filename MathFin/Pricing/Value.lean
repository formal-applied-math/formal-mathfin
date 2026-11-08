/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Contracts.Instruments.FixedIncome
public import Mathlib.Probability.Martingale.Basic

/-!
# Pricing a contract: value, its linearity, and the martingale seam

A `Contract` is still model-agnostic data until it meets a stochastic model. `Scenario`
becomes a random variable once a model `X : ι → ℝ≥0 → Ω → ℝ` and an outcome `ω : Ω` are
fixed (`scenarioAt`); `Contract.value` integrates the resulting `pathPV` against a pricing
measure `Q` and a discount curve `D`.

This file's connection to the market vocabulary is through `Martingale`, not `IsEMM`:
`value_deliverAsset`'s pricing identity needs a `Q`-martingale price process and `Q` a
probability measure, nothing more. The mutual-absolute-continuity content that makes a
martingale measure an *equivalent* one — `IsEMM`'s `ac`/`ac'` fields — is not needed by
anything here; it lives in `ContinuousMarket.lean` (`isEMM_noArbitrageSimple`), where it
is load-bearing.

## Main definitions

* `scenarioAt` — the scenario read off a model `X` at a single outcome `ω`.
* `Contract.value` — the pricing integral `∫ ω, c.pathPV D (scenarioAt X ω) ∂Q`.

## Main results

* `Contract.value_pay` — a single cash flow is worth the integral of its discounted payoff.
* `Contract.value_scale`, `Contract.value_both` — `value` is homogeneous and additive,
  inherited from `pathPV_scale` and `pathPV_both`. The two carry different hypotheses on
  purpose: `value_scale` needs none, because `integral_const_mul` holds unconditionally in
  Mathlib's Bochner integral (it returns `0` off the integrable set on both sides), while
  `value_both` genuinely needs both summands integrable — `integral_add` is false without
  them. That asymmetry, not a uniform "linearity", is the honest content of this pair.
* `Contract.value_deliverAsset` — a contract that simply delivers the asset `S` at time `T`
  is worth `∫ ω, S 0 ω ∂Q` today, given `S` is a `Q`-martingale and `Q` a probability
  measure. Mechanically this *is* conditional-expectation machinery (`condExp_ae_eq` +
  `integral_condExp`), the same kind `value_process_martingale` uses, evaluated at the
  fixed times `0` and `T` — it carries no equivalence content, so it is stated against
  `Martingale` directly rather than the library's `IsEMM` bundle, whose `ac`/`ac'` fields
  this argument never needs.
* `Contract.value_eq_of_pathPV_eq`, `value_fixedFlows` — a contract that pays the same amount
  along every scenario, a schedule of fixed cash flows among them, is worth that amount in every
  model.
* `Contract.value_congr_ae` — a fixed-dated contract has the same value in two models that agree
  almost surely at the `(underlying, date)` observations it reads (`Contract.obsList`).
* `Contract.value_process_martingale` — the conditional-expectation value process of a
  contract is a `Q`-martingale. Carries **no** `Integrable` hypothesis: `martingale_condExp`
  is unconditional, because Mathlib's Bochner integral returns the junk value `0` off the
  integrable set, and the constant-`0` process is trivially a martingale — so the theorem is
  honest but its content lives entirely in the integrable case. It is also stated with **no**
  `IsEMM` hypothesis: it is `martingale_condExp` specialized to a contract's cashflows, true
  for any `Q` with a `SigmaFiniteFiltration`, not a fact about the pricing measure. Shipping it
  with an `IsEMM` hypothesis would misattribute a conditional-expectation fact to the EMM
  structure — and, as `value_deliverAsset` above shows, no theorem in this file has any actual
  EMM content to misattribute it to.

## Source

The layered separation of contract semantics from pricing semantics, and the
framing "the contract is not the model", are due to Paul Bilokon,
*The Contract Is Not the Model: Proof-Carrying Exotic Derivatives and the
Economics of Model Risk* (working paper, 9 August 2026; Mathematical
Finance, Imperial College London), with code at
<https://github.com/thalesians/lean_contracts> (Apache-2.0). That paper in
turn builds on the compositional contract-DSL of
Peyton Jones, Eber and Seward (2000) and the certified-contract work of Bahr,
Berthold and Elsman (2015) and Annenkov (2018).

Bilokon separates pricing semantics from contract semantics — a pricing model
is a law over deterministic scenarios — and that separation is his; but his
`PricingModel.value` integrates a function never shown measurable and his
`value_eq_of_pathPV_eq` is `congrArg` under the integral, whereas this file's
linearity carries real integrability hypotheses and its delivery-of-asset
identity is a genuine martingale-pricing fact (`Martingale.condExp_ae_eq`
chained through `integral_condExp`), not an unconditional integral congruence.

No code is copied from `lean_contracts`; every definition and proof here is
written for this library. See `docs/specs/2026-08-16-contracts-tower-design.md`
§6 for the full credit line.

## References

* [P. Bilokon, *The Contract Is Not the Model*][Bilokon2026]
* [J. C. Hull, *Options, Futures, and Other Derivatives*][Hull], 1.1
* [S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*][ShreveSCFII], 5.2;
  ch. 5

## Tags

contract pricing, risk-neutral valuation, pricing measure, martingale pricing, discounted payoff,
cash flow valuation, MSC 91G20, MSC 60G44, JEL G13
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace MathFin.Contracts

variable {ι Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The scenario read off a model at a single outcome. -/
def scenarioAt (X : ι → ℝ≥0 → Ω → ℝ) (ω : Ω) : Scenario ι := fun i t ↦ X i t ω

/-- The value of a `Contract`: the `Q`-expectation of its discounted pathwise present value,
against a model `X` that reifies each `Scenario` observation as a random variable. -/
noncomputable def Contract.value (Q : Measure Ω) (D : ℝ≥0 → ℝ)
    (X : ι → ℝ≥0 → Ω → ℝ) (c : Contract ι) : ℝ :=
  ∫ ω, c.pathPV D (scenarioAt X ω) ∂Q

/-- **The value of a single cash flow** is the integral of its discounted payoff. Every
instrument that pays once (`Contracts/Instruments/Options.lean`) reaches its closed form in a
model by rewriting through this lemma. -/
theorem Contract.value_pay (Q : Measure Ω) (D : ℝ≥0 → ℝ) (X : ι → ℝ≥0 → Ω → ℝ) (t : ℝ≥0)
    (a : Payoff ι) :
    (Contract.pay t a).value Q D X = ∫ ω, D t * a.eval (scenarioAt X ω) ∂Q := by
  simp [Contract.value, Contract.pathPV, Contract.cashflows]

/-- `value` is homogeneous under `scale`, unconditionally: `integral_const_mul` holds even
off the integrable set (both sides are `0` there), so no integrability hypothesis is needed. -/
theorem Contract.value_scale (Q : Measure Ω) (D : ℝ≥0 → ℝ)
    (X : ι → ℝ≥0 → Ω → ℝ) (r : ℝ) (a : Contract ι) :
    (Contract.scale r a).value Q D X = r * a.value Q D X := by
  simp only [value, Contract.pathPV_scale]
  exact integral_const_mul r _

/-- `value` is additive under `both`, given both summands are integrable — `integral_add`
is false without that hypothesis on either side, unlike `value_scale`'s unconditional case. -/
theorem Contract.value_both (Q : Measure Ω) (D : ℝ≥0 → ℝ)
    (X : ι → ℝ≥0 → Ω → ℝ) (a b : Contract ι)
    (ha : Integrable (fun ω ↦ a.pathPV D (scenarioAt X ω)) Q)
    (hb : Integrable (fun ω ↦ b.pathPV D (scenarioAt X ω)) Q) :
    (Contract.both a b).value Q D X = a.value Q D X + b.value Q D X := by
  simp only [value, Contract.pathPV_both]
  exact integral_add ha hb

/-- Under a `Q`-martingale `S` and `Q` a probability measure, a contract that simply
delivers the asset `S` at time `T`, undiscounted, is worth `∫ ω, S 0 ω ∂Q` today — the
`Q`-price of `S` at time `0`. This is `Martingale.condExp_ae_eq` between `0` and `T`
chained through `integral_condExp`: a martingale-plus-probability-measure fact evaluated
at fixed times, the same conditional-expectation machinery `value_process_martingale`
uses. It carries no equivalence content — `Q` need not be an EMM for `S`, only a
probability measure under which `S` is a martingale — so it is stated against
`Martingale` directly rather than the library's `IsEMM` bundle, whose `ac`/`ac'` fields
this argument never needs; that mutual-absolute-continuity content lives elsewhere
(`ContinuousMarket.isEMM_noArbitrageSimple`). -/
theorem Contract.value_deliverAsset {𝓕 : Filtration ℝ≥0 mΩ}
    {S : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hM : Martingale S 𝓕 Q) (T : ℝ≥0) :
    (Contract.pay T (Payoff.obs () T)).value Q (fun _ ↦ 1) (fun _ ↦ S)
      = ∫ ω, S 0 ω ∂Q := by
  simp only [value, Contract.pathPV, Contract.cashflows, Payoff.eval, scenarioAt,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, one_mul, add_zero]
  rw [← integral_condExp (𝓕.le 0)]
  exact integral_congr_ae (hM.condExp_ae_eq zero_le)

/-- The conditional-expectation value process of a contract is a `Q`-martingale. Needs
**no** `Integrable` hypothesis — `martingale_condExp` is unconditional, so a non-integrable
contract just gives the constant-`0` martingale (Bochner junk value); the theorem's content
is the integrable case. Needs **no** EMM hypothesis either: it is a property of conditional
expectation, not of the pricing measure — no theorem in this file needs `IsEMM`;
`value_deliverAsset` needs only `Martingale S 𝓕 Q` and `[IsProbabilityMeasure Q]`. -/
theorem Contract.value_process_martingale {Q : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    [SigmaFiniteFiltration Q 𝓕] (D : ℝ≥0 → ℝ) (X : ι → ℝ≥0 → Ω → ℝ)
    (c : Contract ι) :
    Martingale (fun t ↦ Q[fun ω ↦ c.pathPV D (scenarioAt X ω) | 𝓕 t]) 𝓕 Q :=
  martingale_condExp _ 𝓕 Q

/-! ### Two models that agree where the contract looks -/

/-- **A fixed-dated contract has the same value in two models that agree almost surely at the
observations it reads.** The models need not agree anywhere else: this is what lets a model that
is only Brownian up to a horizon price a contract whose dates lie before it. -/
theorem Contract.value_congr_ae {Q : Measure Ω} {D : ℝ≥0 → ℝ} {X Y : ι → ℝ≥0 → Ω → ℝ}
    (c : Contract ι) (hc : c.FixedDated)
    (h : ∀ p ∈ c.obsList, ∀ᵐ ω ∂Q, X p.1 p.2 ω = Y p.1 p.2 ω) :
    c.value Q D X = c.value Q D Y := by
  refine integral_congr_ae ?_
  have hall : ∀ᵐ ω ∂Q, ∀ p ∈ {p | p ∈ c.obsList}, X p.1 p.2 ω = Y p.1 p.2 ω :=
    (ae_ball_iff (List.finite_toSet _).countable).2 h
  filter_upwards [hall] with ω hω
  unfold Contract.pathPV
  rw [Contract.cashflows_congr c hc (s := scenarioAt X ω) (s' := scenarioAt Y ω) hω]

/-- **A contract that pays the same along every scenario is worth that amount** in every model,
under any probability measure. -/
theorem Contract.value_eq_of_pathPV_eq {Q : Measure Ω} [IsProbabilityMeasure Q] {D : ℝ≥0 → ℝ}
    (X : ι → ℝ≥0 → Ω → ℝ) {c : Contract ι} {v : ℝ} (h : ∀ s, c.pathPV D s = v) :
    c.value Q D X = v := by
  simp [Contract.value, h]

/-- In every model, a schedule of fixed cash flows is worth `∑ D(tᵢ) cᵢ`. -/
theorem value_fixedFlows {Q : Measure Ω} [IsProbabilityMeasure Q] (D : ℝ≥0 → ℝ)
    (X : ι → ℝ≥0 → Ω → ℝ) (t : ℕ → ℝ≥0) (c : ℕ → ℝ) (n : ℕ) :
    (fixedFlows t c n : Contract ι).value Q D X = ∑ i ∈ Finset.range n, D (t i) * c i :=
  Contract.value_eq_of_pathPV_eq X fun s ↦ pathPV_fixedFlows D s t c n

end MathFin.Contracts
