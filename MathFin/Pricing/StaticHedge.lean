/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Init
public import MathFin.Pricing.Parity
public import MathFin.Contracts.StaticHedge

/-!
# Static hedges in every model

`Contracts/StaticHedge.lean` compiles a piecewise-linear payoff `e` of the terminal observation to a
static portfolio, a bond, a forward and calls, and proves that along every scenario with
nonnegative terminal observation the portfolio has the present value of `pay T e`. This file
carries that to `Contract.value`. In any model whose underlying is nonnegative at `T`, under any
measure and any deflator, `pay T e` and its compiled portfolio have the same value
(`Contract.value_pay_eq_value_staticHedge`): the payoff is priced by the bond, the forward and the
calls, whatever the model.

Under a deterministic discount factor `D` and a probability measure with integrable discounted
underlying, the value of the portfolio is its amounts times the values of its pieces
(`StaticHedge.value_contract`): the bond is worth `D T`, the forward and each call are worth what
the model says. The only fact about the model that enters is the integrability of the discounted
underlying, which gives the integrability of the calls (`integrable_europeanCall_pathPV`).

## Main results

* `Contract.value_pay_eq_value_staticHedge`: in every model with a nonnegative underlying at `T`,
  `pay T e` is worth the compiled portfolio, for `e` in the piecewise-linear fragment.
* `StaticHedge.value_contract`: the value of a portfolio is the bond amount times `D T`, plus the
  forward amount times the forward's value, plus the weighted values of its calls.

## References

* [P. Carr and D. Madan, *Towards a theory of volatility trading*][CarrMadan1998]
* [P. Bilokon, *The Contract Is Not the Model*][Bilokon2026]

## Tags

static hedge, static replication, model-free pricing, piecewise linear payoff, contract value,
MSC 91G20, JEL G13
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace MathFin.Contracts

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **A piecewise-linear payoff is worth its static hedge in every model.** For any measure, any
deflator and any model whose underlying is nonnegative at `T`, the contract paying `e` at `T` and
the compiled portfolio of a bond, a forward and calls have the same value. Nothing is assumed of
the law: this is `Payoff.IsPiecewiseLinear.pathPV_staticHedge` integrated. -/
theorem Contract.value_pay_eq_value_staticHedge {Q : Measure Ω} (D : ℝ≥0 → Ω → ℝ)
    (X : Unit → ℝ≥0 → Ω → ℝ) {T : ℝ≥0} {e : Payoff Unit} (h : e.IsPiecewiseLinear T)
    (hX : ∀ ω, 0 ≤ X () T ω) :
    (Contract.pay T e).value Q D X = ((e.staticHedge T).contract T).value Q D X := by
  refine integral_congr_ae (ae_of_all _ fun ω ↦ ?_)
  exact (h.pathPV_staticHedge (fun t ↦ D t ω) (scenarioAt X ω) (hX ω)).symm

section Decomposition

variable {Q : Measure Ω} {D : ℝ≥0 → ℝ} {X : Unit → ℝ≥0 → Ω → ℝ} {T : ℝ≥0}

/-- The deflated payoff of a portfolio of calls is integrable when the discounted underlying is. -/
theorem integrable_callPortfolio_pathPV [IsFiniteMeasure Q]
    (hX : Integrable (fun ω ↦ D T * X () T ω) Q) (L : List (ℝ × ℝ)) :
    Integrable (fun ω ↦ (callPortfolio T L).pathPV D (scenarioAt X ω)) Q := by
  induction L with
  | nil => simpa [callPortfolio, Contract.pathPV, Contract.cashflows] using integrable_const (0 : ℝ)
  | cons p L ih =>
    simp only [callPortfolio, Contract.pathPV_both, Contract.pathPV_scale]
    exact ((integrable_europeanCall_pathPV hX).const_mul p.2).add ih

/-- A portfolio of calls is worth the weighted sum of the values of its calls, when the discounted
underlying is integrable. -/
theorem value_callPortfolio [IsFiniteMeasure Q] (hX : Integrable (fun ω ↦ D T * X () T ω) Q)
    (L : List (ℝ × ℝ)) :
    (callPortfolio T L).value Q (fun t _ ↦ D t) X
      = (L.map fun p ↦ p.2 * (europeanCall p.1 T).value Q (fun t _ ↦ D t) X).sum := by
  induction L with
  | nil => simp [callPortfolio, Contract.value, Contract.pathPV, Contract.cashflows]
  | cons p L ih =>
    have hcall : Integrable (fun ω ↦
        (Contract.scale p.2 (europeanCall p.1 T)).pathPV D (scenarioAt X ω)) Q := by
      simp only [Contract.pathPV_scale]
      exact (integrable_europeanCall_pathPV hX).const_mul _
    rw [callPortfolio, Contract.value_both Q (fun t _ ↦ D t) X
      (Contract.scale p.2 (europeanCall p.1 T)) (callPortfolio T L) hcall
      (integrable_callPortfolio_pathPV hX L), Contract.value_scale, ih, List.map_cons,
      List.sum_cons]

/-- **The bond is worth its discount factor**, under a probability measure and a deterministic
discount curve. -/
theorem value_pay_const_one [IsProbabilityMeasure Q] :
    (Contract.pay T (.const 1)).value Q (fun t _ ↦ D t) X = D T := by
  rw [Contract.value_pay]
  simp only [Payoff.eval, mul_one]
  rw [integral_const, probReal_univ, one_smul]

/-- **The value of a static hedge**: under a probability measure and a deterministic discount
curve `D`, with the discounted underlying integrable at `T`, the portfolio is worth its bond
amount times `D T`, plus its forward amount times the value of `pay T (obs () T)`, plus its
weighted call values. -/
theorem StaticHedge.value_contract [IsProbabilityMeasure Q]
    (hX : Integrable (fun ω ↦ D T * X () T ω) Q) (H : StaticHedge) :
    (H.contract T).value Q (fun t _ ↦ D t) X
      = H.bondAmount * D T
        + H.forwardAmount * (Contract.pay T (.obs () T)).value Q (fun t _ ↦ D t) X
        + (H.calls.map fun p ↦ p.2 * (europeanCall p.1 T).value Q (fun t _ ↦ D t) X).sum := by
  have hb : Integrable (fun ω ↦
      (Contract.scale H.bondAmount (Contract.pay T (.const 1))).pathPV D (scenarioAt X ω)) Q := by
    simp only [Contract.pathPV_scale, Contract.pathPV_pay, Payoff.eval]
    exact integrable_const _
  have hf : Integrable (fun ω ↦
      (Contract.scale H.forwardAmount (Contract.pay T (.obs () T))).pathPV D
        (scenarioAt X ω)) Q := by
    simp only [Contract.pathPV_scale, Contract.pathPV_pay, Payoff.eval, scenarioAt]
    exact hX.const_mul _
  have hrest : Integrable (fun ω ↦
      (Contract.both (Contract.scale H.forwardAmount (Contract.pay T (.obs () T)))
        (callPortfolio T H.calls)).pathPV D (scenarioAt X ω)) Q := by
    simp only [Contract.pathPV_both]
    exact hf.add (integrable_callPortfolio_pathPV hX _)
  rw [StaticHedge.contract, Contract.value_both Q (fun t _ ↦ D t) X _ _ hb hrest,
    Contract.value_scale, Contract.value_both Q (fun t _ ↦ D t) X _ _ hf
      (integrable_callPortfolio_pathPV hX _),
    Contract.value_scale, value_callPortfolio hX, value_pay_const_one]
  ring

end Decomposition

end MathFin.Contracts
