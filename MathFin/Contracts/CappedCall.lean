/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Contracts.BlackScholes
public import MathFin.BlackScholes.CappedCall
public import MathFin.Foundations.BrownianMartingale

/-!
# The capped call, priced by composing two European calls

`MathFin/BlackScholes/CappedCall.lean` proves `cappedCall_eq_bull_spread` as a pointwise
real identity between two payoff formulas and stops there: there is no object on which to
say "the value of a sum of contracts is the sum of the values" until a contract exists to
carry that identity. This file supplies that object. `cappedCall K₁ K₂ T` is *defined* as a
composed `Contract Unit` — a long call at `K₁` combined with a short call at `K₂` — and its
Black–Scholes value is obtained by composing `value_europeanCall` twice through
`Contract.value_both` and `Contract.value_scale`, without evaluating a third integral.

Naming the definition `cappedCall` is a claim, and `value_cappedCall` alone would not earn
it: taken by itself, its statement is exactly the value of a bull call spread, whatever the
underlying contract happens to be called. `cappedCall_payoff_eq` is what earns the name —
for `K₁ ≤ K₂`, it proves the composed contract really pays `min(max(S − K₁, 0), K₂ − K₁)`,
via `cappedCall_eq_bull_spread`.

## Main definitions

* `cappedCall` — a long `europeanCall K₁ T` combined with a short `europeanCall K₂ T`.

## Main results

* `cappedCall_payoff_eq` — for `K₁ ≤ K₂`, `cappedCall K₁ K₂ T` really pays
  `min(max(S − K₁, 0), K₂ − K₁)`, the capped-call payoff `CappedCall.lean` names but never
  attaches to an object.
* `value_cappedCall` — its Black–Scholes value is the difference of the two call values, by
  linearity of `Contract.value` alone; the proof never unfolds `Contract.value` or touches
  an integral. The discounted payoff's integrability, which `Contract.value_both` needs, is
  discharged internally (`integrable_europeanCall_pathPV`) by domination against the
  terminal asset price, whose exponential moment is `integrable_exp_mul_of_hasLaw`'s
  Gaussian MGF transfer.

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

Compositional contract construction — building an instrument from simpler ones
and pricing it by composition — is the core of Bilokon's DSL and of Peyton
Jones, Eber and Seward before him; what is added here is that the composition
is priced through the library's own closed forms rather than left as a
denotational identity.

No code is copied from `lean_contracts`; every definition and proof here is
written for this library. See `docs/specs/2026-08-16-contracts-tower-design.md`
§6 for the full credit line.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace MathFin.Contracts

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- A capped call struck at `K₁` and capped at `K₂`, built as a long call at `K₁` and a
short call at `K₂`. `cappedCall_payoff_eq` proves this composed object really does pay
`min (max (S - K₁) 0) (K₂ - K₁)`. -/
noncomputable def cappedCall (K₁ K₂ : ℝ) (T : ℝ≥0) : Contract Unit :=
  .both (europeanCall K₁ T) (.scale (-1) (europeanCall K₂ T))

/-- The discounted payoff of a reified European call is integrable under `BSCallHyp`: it is
dominated by the terminal asset price `bsTerminal`, itself integrable via the Gaussian MGF
transfer `integrable_exp_mul_of_hasLaw`. This is what lets `value_cappedCall` below drop the
integrability hypotheses `Contract.value_both` would otherwise need supplied by hand. -/
private theorem integrable_europeanCall_pathPV {Q : Measure Ω} [IsProbabilityMeasure Q]
    {S_0 K r σ : ℝ} {T : ℝ≥0} {Z : Ω → ℝ} (h : BSCallHyp Q S_0 K r σ T Z) :
    Integrable (fun ω ↦ (europeanCall K T).pathPV
      (fun _ ↦ Real.exp (-r * T)) (scenarioAt (bsAssets S_0 r σ T Z) ω)) Q := by
  obtain ⟨hS_0, hK, _, _, hZ⟩ := h
  have h_asset_meas : Measurable (bsTerminal S_0 r σ T) := by unfold bsTerminal; fun_prop
  have h_asset_int : Integrable (fun ω ↦ bsTerminal S_0 r σ T (Z ω)) Q := by
    have h_split : bsTerminal S_0 r σ T = fun z ↦
        (S_0 * Real.exp ((r - σ ^ 2 / 2) * (T : ℝ))) * Real.exp (σ * Real.sqrt T * z) := by
      funext z; unfold bsTerminal; rw [Real.exp_add]; ring
    rw [h_split]
    exact (integrable_exp_mul_of_hasLaw hZ (σ * Real.sqrt T)).const_mul _
  have h_asset_pos (ω : Ω) : 0 < bsTerminal S_0 r σ T (Z ω) :=
    mul_pos hS_0 (Real.exp_pos _)
  have h_payoff_meas : AEStronglyMeasurable
      (fun ω ↦ max (bsTerminal S_0 r σ T (Z ω) - K) 0) Q :=
    ((h_asset_meas.sub measurable_const).max measurable_const).comp_aemeasurable
      hZ.aemeasurable |>.aestronglyMeasurable
  have h_payoff_int : Integrable (fun ω ↦ max (bsTerminal S_0 r σ T (Z ω) - K) 0) Q := by
    refine h_asset_int.mono' h_payoff_meas (ae_of_all _ fun ω ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    calc max (bsTerminal S_0 r σ T (Z ω) - K) 0
        ≤ max (bsTerminal S_0 r σ T (Z ω)) 0 := max_le_max (by linarith) le_rfl
      _ = bsTerminal S_0 r σ T (Z ω) := max_eq_left (h_asset_pos ω).le
  simp only [europeanCall, Contract.pathPV, Contract.cashflows, Payoff.eval,
    scenarioAt, bsAssets, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  exact h_payoff_int.const_mul _

/-- **The capped call really pays the capped payoff.** For `K₁ ≤ K₂`, `cappedCall K₁ K₂ T`,
the composed long-call/short-call contract, pays exactly `min(max(S − K₁, 0), K₂ − K₁)` along
any scenario — the identity `MathFin.cappedCall_eq_bull_spread` transported from a pointwise
real equation to the contract's own `pathPV`. This is what earns the definition its name. -/
theorem cappedCall_payoff_eq {K₁ K₂ : ℝ} (h : K₁ ≤ K₂) {T : ℝ≥0}
    (s : Scenario Unit) :
    (cappedCall K₁ K₂ T).pathPV (fun _ ↦ 1) s
      = min (max (s () T - K₁) 0) (K₂ - K₁) := by
  simp only [cappedCall, Contract.pathPV, Contract.cashflows, europeanCall, Payoff.eval,
    List.map_append, List.map_cons, List.map_nil, List.sum_append,
    List.sum_cons, List.sum_nil, one_mul, add_zero]
  linarith [MathFin.cappedCall_eq_bull_spread (s () T) K₁ K₂ h]

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
    (cappedCall K₁ K₂ T).value Q (fun _ ↦ Real.exp (-r * T)) (bsAssets S_0 r σ T Z)
      = (S_0 * Phi (bsd1 S_0 K₁ r σ T) - K₁ * Real.exp (-r * T) * Phi (bsd2 S_0 K₁ r σ T))
      - (S_0 * Phi (bsd1 S_0 K₂ r σ T) - K₂ * Real.exp (-r * T) * Phi (bsd2 S_0 K₂ r σ T)) := by
  have hi₁ := integrable_europeanCall_pathPV h₁
  have hi₂ : Integrable (fun ω ↦ (Contract.scale (-1) (europeanCall K₂ T)).pathPV
      (fun _ ↦ Real.exp (-r * T)) (scenarioAt (bsAssets S_0 r σ T Z) ω)) Q := by
    simp only [Contract.pathPV_scale]
    exact (integrable_europeanCall_pathPV h₂).const_mul _
  rw [cappedCall, Contract.value_both _ _ _ _ _ hi₁ hi₂,
    Contract.value_scale, value_europeanCall h₁, value_europeanCall h₂]
  ring

end MathFin.Contracts
