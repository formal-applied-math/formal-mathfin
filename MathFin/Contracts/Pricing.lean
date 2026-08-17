/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Contracts.Adapted
public import MathFin.Foundations.ContinuousMarket

/-!
# Pricing a contract: value, its linearity, and the EMM seam

A `Contract` is still model-agnostic data until it meets a stochastic model. `Scenario`
becomes a random variable once a model `X : ι → ℝ≥0 → Ω → ℝ` and an outcome `ω : Ω` are
fixed (`scenarioAt`); `Contract.value` integrates the resulting `pathPV` against a pricing
measure `Q` and a discount curve `D`.

## Main definitions

* `scenarioAt` — the scenario read off a model `X` at a single outcome `ω`.
* `Contract.value` — the pricing integral `∫ ω, c.pathPV D (scenarioAt X ω) ∂Q`.

## Main results

* `Contract.value_scale`, `Contract.value_both` — `value` is homogeneous and additive,
  inherited from `pathPV_scale` and `pathPV_both`. The two carry different hypotheses on
  purpose: `value_scale` needs none, because `integral_const_mul` holds unconditionally in
  Mathlib's Bochner integral (it returns `0` off the integrable set on both sides), while
  `value_both` genuinely needs both summands integrable — `integral_add` is false without
  them. That asymmetry, not a uniform "linearity", is the honest content of this pair.
* `Contract.value_deliverAsset` — the EMM seam: under `IsEMM S Q`, a contract that simply
  delivers the asset `S` at time `T` is worth `∫ ω, S 0 ω ∂Q` today. This is genuinely an EMM
  fact — it consumes `hEMM.martingale` between times `0` and `T` — not a restatement of
  conditional-expectation machinery.
* `Contract.value_process_martingale` — the conditional-expectation value process of *any*
  integrable contract is a `Q`-martingale. Deliberately stated with **no** `IsEMM` hypothesis:
  it is `martingale_condExp` specialized to a contract's cashflows, true for any `Q` with a
  `SigmaFiniteFiltration`, not a fact about the pricing measure. Shipping it with an `IsEMM`
  hypothesis would misattribute a conditional-expectation fact to the EMM structure —
  `value_deliverAsset` above is where this file's actual EMM content lives.

## Source

The layered separation of contract semantics from pricing semantics, and the
framing "the contract is not the model", are due to Paul Bilokon, *The Contract
Is Not the Model: Proof-Carrying Exotic Derivatives and the Economics of Model
Risk* (working paper, 9 August 2026; Mathematical Finance, Imperial College
London), with code at <https://github.com/thalesians/lean_contracts>
(Apache-2.0). That paper in turn builds on the compositional contract-DSL of
Peyton Jones, Eber and Seward (2000) and the certified-contract work of Bahr,
Berthold and Elsman (2015) and Annenkov (2018).

Bilokon separates pricing semantics from contract semantics — a pricing model
is a law over deterministic scenarios — and that separation is his; but his
`PricingModel.value` integrates a function never shown measurable and his
`value_eq_of_pathPV_eq` is `congrArg` under the integral, whereas this file
states its results against the library's existing `ContinuousMarket.IsEMM`
and carries real integrability hypotheses.

No code is copied from `lean_contracts`; every definition and proof here is
written for this library. See `docs/specs/2026-08-16-contracts-tower-design.md`
§6 for the full credit line.
-/

@[expose] public section

open MeasureTheory MathFin.ContinuousMarket
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

/-- **The EMM seam.** Under `IsEMM S Q`, a contract that simply delivers the asset `S` at
time `T`, undiscounted, is worth `∫ ω, S 0 ω ∂Q` today — the `Q`-price of `S` at time `0`.
This genuinely uses `hEMM.martingale`, between times `0` and `T`: it is the one theorem in
this file that is an EMM fact rather than a conditional-expectation fact. -/
theorem Contract.value_deliverAsset {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {S : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} (hEMM : IsEMM (P := P) (𝓕 := 𝓕) S Q)
    (T : ℝ≥0) :
    (Contract.pay T (Payoff.obs () T)).value Q (fun _ ↦ 1) (fun _ ↦ S)
      = ∫ ω, S 0 ω ∂Q := by
  haveI := hEMM.isProb
  simp only [value, Contract.pathPV, Contract.cashflows, Payoff.eval, scenarioAt,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, one_mul, add_zero]
  rw [← integral_condExp (𝓕.le 0)]
  exact integral_congr_ae (hEMM.martingale.condExp_ae_eq zero_le)

/-- The conditional-expectation value process of any integrable contract is a
`Q`-martingale. This needs **no** EMM hypothesis: it is a property of conditional
expectation, not of the pricing measure. `value_deliverAsset` is the statement in
this file that actually consumes `IsEMM`. -/
theorem Contract.value_process_martingale {Q : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    [SigmaFiniteFiltration Q 𝓕] (D : ℝ≥0 → ℝ) (X : ι → ℝ≥0 → Ω → ℝ)
    (c : Contract ι) :
    Martingale (fun t ↦ Q[fun ω ↦ c.pathPV D (scenarioAt X ω) | 𝓕 t]) 𝓕 Q :=
  martingale_condExp _ 𝓕 Q

end MathFin.Contracts
