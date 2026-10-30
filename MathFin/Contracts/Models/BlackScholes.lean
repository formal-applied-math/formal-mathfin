/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Contracts.Parity
public import MathFin.BlackScholes.Digital
public import MathFin.BlackScholes.Put
public import MathFin.BlackScholes.Forward

/-!
# The contracts priced in the Black–Scholes model

`Contracts/Instruments/Options.lean` defines the instruments and says what they pay; this file
prices them in one model. `BlackScholes.assets` is the single-asset Black–Scholes market as a
model map, and each instrument's `Contract.value` under it is the closed form
`MathFin/BlackScholes/` already proves. Another model gets its own file of the same shape and its
own namespace (`Contracts/Models/Binomial.lean`, `Contracts.Binomial`); the instruments do not
change.

`BlackScholes.assets` is constant in `t`: every instrument priced here observes the underlying
only at its maturity `T`, so the model's value at other times is irrelevant to what gets priced. A
path-dependent instrument needs the full path and is deferred.

Nothing new is proved about Black–Scholes here. A single cash flow's value is the integral of
its discounted payoff (`Contract.value_pay`), which is exactly the integral `bs_call_formula`,
`bs_put_formula` and `bs_cash_or_nothing_formula` compute. The capped call is priced by
composition: `Contract.value_both` and `Contract.value_scale` reduce it to two call values, and
no third integral is evaluated.

## Main definitions

* `BlackScholes.assets` — the single-asset Black–Scholes model as a model map `Unit → ℝ≥0 → Ω → ℝ`,
  constant in `t` and equal to `bsTerminal` at every time.

## Main results

* `value_europeanCall`, `value_europeanPut`, `value_digitalCall` — each instrument's value is
  `bs_call_formula`, `bs_put_formula` and `bs_cash_or_nothing_formula` respectively.
* `value_forward` — the forward is worth `S₀ − K e^{−rT}`.
* `value_cappedCall` — the capped call is worth the difference of two call values.

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

The source paper's §"Pricing-model validation" lists proving contract cashflows
measurable and integrable, and connecting them to a concrete model, as future
work; this file does that reduction against closed forms the library already
proves.

No code is copied from `lean_contracts`; every definition and proof here is
written for this library. See `docs/specs/2026-08-16-contracts-tower-design.md`
§6 for the full credit line.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace MathFin.Contracts.BlackScholes

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The single-asset Black–Scholes market as a model map. Every instrument in
this file observes only at `T`, so the value at other times is irrelevant; a
path-dependent instance needs the full GBM path and is deferred. -/
noncomputable def assets (S_0 r σ T : ℝ) (Z : Ω → ℝ) : Unit → ℝ≥0 → Ω → ℝ :=
  fun _ _ ω ↦ bsTerminal S_0 r σ T (Z ω)

/-- The reified European call prices to the Black–Scholes call formula: the value of
`europeanCall K T` under `BlackScholes.assets` is exactly `bs_call_formula`'s right-hand side. -/
theorem value_europeanCall {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r σ : ℝ} {T : ℝ≥0} {Z : Ω → ℝ} (h : BSCallHyp Q S_0 K r σ T Z) :
    (europeanCall K T).value Q (fun _ ↦ Real.exp (-r * T)) (assets S_0 r σ T Z)
      = S_0 * Phi (bsd1 S_0 K r σ T) - K * Real.exp (-r * T) * Phi (bsd2 S_0 K r σ T) := by
  rw [europeanCall, Contract.value_pay]
  exact MathFin.bs_call_formula h

/-- The reified cash-or-nothing digital call prices to the Black–Scholes
cash-or-nothing formula: the value of `digitalCall K T` under `BlackScholes.assets` is exactly
`bs_cash_or_nothing_formula`'s right-hand side. -/
theorem value_digitalCall {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r σ : ℝ} {T : ℝ≥0} {Z : Ω → ℝ} (h : BSCallHyp Q S_0 K r σ T Z) :
    (digitalCall K T).value Q (fun _ ↦ Real.exp (-r * T)) (assets S_0 r σ T Z)
      = Real.exp (-r * T) * Phi (bsd2 S_0 K r σ T) := by
  rw [digitalCall, Contract.value_pay]
  have heq (ω : Ω) : Payoff.eval (scenarioAt (assets S_0 r σ T Z) ω)
      ((Payoff.const K).indicatorLt (Payoff.obs () T))
        = (Set.Ioi K).indicator (fun _ ↦ (1 : ℝ)) (bsTerminal S_0 r σ T (Z ω)) := by
    simp [Payoff.eval, scenarioAt, assets, Set.indicator_apply, Set.mem_Ioi]
    congr 1
  simp only [heq]
  exact MathFin.bs_cash_or_nothing_formula h

/-- The reified European put prices to the Black–Scholes put formula: the value of
`europeanPut K T` under `BlackScholes.assets` is exactly `bs_put_formula`'s right-hand side. -/
theorem value_europeanPut {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r σ : ℝ} {T : ℝ≥0} {Z : Ω → ℝ} (h : BSCallHyp Q S_0 K r σ T Z) :
    (europeanPut K T).value Q (fun _ ↦ Real.exp (-r * T)) (assets S_0 r σ T Z)
      = K * Real.exp (-r * T) * Phi (-(bsd2 S_0 K r σ T)) - S_0 * Phi (-(bsd1 S_0 K r σ T)) := by
  rw [europeanPut, Contract.value_pay]
  exact MathFin.bs_put_formula h

/-- **The forward's Black–Scholes value** is `S₀ − K e^{−rT}`: the discounted terminal price has
mean `S₀` (`discounted_terminal_eq_S0`), so this is `value_forward_of_integral`. -/
theorem value_forward {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r σ : ℝ} {T : ℝ≥0} {Z : Ω → ℝ} (h : BSCallHyp Q S_0 K r σ T Z) :
    (forward K T).value Q (fun _ ↦ Real.exp (-r * T)) (assets S_0 r σ T Z)
      = S_0 - K * Real.exp (-r * T) :=
  value_forward_of_integral ((integrable_bsTerminal h.Z_law S_0 r σ T).const_mul _)
    (by simpa [assets, neg_mul] using discounted_terminal_eq_S0 h)

/-- **The capped call's Black–Scholes value, by composition, not by a third integral.**
`cappedCall K₁ K₂ T`'s value under the single-asset Black–Scholes model is the difference
of the two `europeanCall` values `value_europeanCall` already supplies. The proof is
`Contract.value_both` and `Contract.value_scale` applied to `value_europeanCall` twice,
closed by `ring` — no unfolding of `Contract.value`, no integral touched here at all; that
is the entire point of having reified `cappedCall` as a composed `Contract` rather than as
one more inline payoff lambda. -/
theorem value_cappedCall {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K₁ K₂ r σ : ℝ} {T : ℝ≥0} {Z : Ω → ℝ}
    (h₁ : BSCallHyp Q S_0 K₁ r σ T Z) (h₂ : BSCallHyp Q S_0 K₂ r σ T Z) :
    (cappedCall K₁ K₂ T).value Q (fun _ ↦ Real.exp (-r * T)) (assets S_0 r σ T Z)
      = (S_0 * Phi (bsd1 S_0 K₁ r σ T) - K₁ * Real.exp (-r * T) * Phi (bsd2 S_0 K₁ r σ T))
      - (S_0 * Phi (bsd1 S_0 K₂ r σ T) - K₂ * Real.exp (-r * T) * Phi (bsd2 S_0 K₂ r σ T)) := by
  have hX := (integrable_bsTerminal h₁.Z_law S_0 r σ T).const_mul (Real.exp (-r * T))
  have hi₁ : Integrable (fun ω ↦ (europeanCall K₁ T).pathPV (fun _ ↦ Real.exp (-r * T))
      (scenarioAt (assets S_0 r σ T Z) ω)) Q := integrable_europeanCall_pathPV hX
  have hi₂ : Integrable (fun ω ↦ (Contract.scale (-1) (europeanCall K₂ T)).pathPV
      (fun _ ↦ Real.exp (-r * T)) (scenarioAt (assets S_0 r σ T Z) ω)) Q := by
    simp only [Contract.pathPV_scale]
    exact (integrable_europeanCall_pathPV hX).const_mul _
  rw [cappedCall, Contract.value_both _ _ _ _ _ hi₁ hi₂,
    Contract.value_scale, value_europeanCall h₁, value_europeanCall h₂]
  ring

end MathFin.Contracts.BlackScholes
