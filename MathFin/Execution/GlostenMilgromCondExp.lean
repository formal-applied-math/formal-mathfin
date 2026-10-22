/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib
public import MathFin.Execution.GlostenMilgrom

/-!
# Glosten–Milgrom quotes as conditional expectations

`MathFin.Execution.GlostenMilgrom` writes the market maker's quotes as integrals against
conditioned measures: the ask is `∫ V ∂μ[|B]` on the buy event `B`, the bid `∫ V ∂μ[|Bᶜ]` on the
sell event. This file identifies the quote process with Mathlib's conditional expectation
given the σ-algebra the trade direction generates, `σ(B) = generateFrom {B}`, and reads off the
martingale property of one trade.

## Results

* `generateFrom_singleton_compl`: a set and its complement generate the same σ-algebra.
* `condExp_payoff_eq_quote`: `μ[V | σ(B)]` is, `μ`-a.e., the ask on `B` and the bid on `Bᶜ`.
  The two posited quotes are exactly the conditional expectation of the value given the order's
  direction (Mathlib's `ProbabilityTheory.condExp_generateFrom_singleton`).
* `measureReal_mul_ask_add_measureReal_mul_bid`: `P(B) · ask + P(Bᶜ) · bid = E[V]`. The
  expected transaction price equals the expected value: the one-trade martingale property, from
  the tower property `integral_condExp`.
* `buyProb_mul_postBuy_add_sellProb_mul_postSell`: the same statement for the closed-form
  posteriors of `GlostenMilgrom`: weighting `postBuy` and `postSell` by the probabilities of a
  buy and a sell, `(1 ± p(2θ − 1))/2`, returns the prior `θ`.

## Scope

One trade. The quotes are posited as the conditioned integrals (as in `GlostenMilgrom`); the
zero-profit derivation of the competitive market maker, and the sequence of trades along which
Glosten–Milgrom prices form a martingale, are not formalized.
-/

@[expose] public section

namespace MathFin.Execution

open MeasureTheory ProbabilityTheory MeasurableSpace

variable {Ω : Type*}

/-- **A set and its complement generate the same σ-algebra**: observing a sell is observing
that there was no buy. -/
theorem generateFrom_singleton_compl (B : Set Ω) :
    generateFrom {Bᶜ} = generateFrom ({B} : Set (Set Ω)) := by
  refine le_antisymm (generateFrom_le fun t ht ↦ ?_) (generateFrom_le fun t ht ↦ ?_) <;>
    rw [Set.mem_singleton_iff.mp ht]
  · exact (measurableSet_generateFrom (Set.mem_singleton B)).compl
  · simpa using (measurableSet_generateFrom (Set.mem_singleton Bᶜ)).compl

variable [MeasurableSpace Ω] (μ : Measure Ω)

/-- **The quote is the conditional expectation given the trade direction.** For a finite
measure, `μ[V | σ(B)]` agrees `μ`-a.e. with the quote process: the ask `∫ V ∂μ[|B]` on the buy
event and the bid `∫ V ∂μ[|Bᶜ]` on the sell event. -/
theorem condExp_payoff_eq_quote [IsFiniteMeasure μ] {H B : Set Ω} [DecidablePred (· ∈ B)]
    (hH : MeasurableSet H) (hB : MeasurableSet B) (VL VH : ℝ) :
    μ[payoff H VL VH | generateFrom {B}] =ᵐ[μ]
      B.piecewise (fun _ ↦ ∫ ω, payoff H VL VH ω ∂μ[|B])
        (fun _ ↦ ∫ ω, payoff H VL VH ω ∂μ[|Bᶜ]) := by
  have hint : Integrable (payoff H VL VH) μ :=
    (integrable_const VL).add ((integrable_const (VH - VL)).indicator hH)
  have hsell := condExp_generateFrom_singleton hB.compl hint
  rw [generateFrom_singleton_compl] at hsell
  refine ae_of_ae_restrict_of_ae_restrict_compl B ?_ ?_
  · filter_upwards [condExp_generateFrom_singleton hB hint, ae_restrict_mem hB] with ω h hω
    rw [h, Set.piecewise_eq_of_mem _ _ _ hω]
  · filter_upwards [hsell, ae_restrict_mem hB.compl] with ω h hω
    rw [h, Set.piecewise_eq_of_notMem _ _ _ hω]

/-- **The expected transaction price is the expected value.** For a finite measure,
`P(B) · ask + P(Bᶜ) · bid = E[V]`: averaging the quote over the trade direction returns the
unconditional mean, the tower property of `condExp_payoff_eq_quote`. -/
theorem measureReal_mul_ask_add_measureReal_mul_bid [IsFiniteMeasure μ] {H B : Set Ω}
    (hH : MeasurableSet H) (hB : MeasurableSet B) (VL VH : ℝ) :
    μ.real B * ∫ ω, payoff H VL VH ω ∂μ[|B] + μ.real Bᶜ * ∫ ω, payoff H VL VH ω ∂μ[|Bᶜ]
      = ∫ ω, payoff H VL VH ω ∂μ := by
  classical
  rw [← integral_condExp (μ := μ) (f := payoff H VL VH) (generateFrom_singleton_le hB),
    integral_congr_ae (condExp_payoff_eq_quote μ hH hB VL VH),
    integral_piecewise hB (integrable_const _).integrableOn (integrable_const _).integrableOn,
    setIntegral_const, setIntegral_const, smul_eq_mul, smul_eq_mul]

/-- **One-step martingale identity for beliefs, in closed form.** Weighting the posterior after a buy and after a
sell by the probabilities of a buy and of a sell, `(1 + p(2θ − 1))/2` and `(1 − p(2θ − 1))/2`
(`spread_pos_of_model` derives these), returns the prior `θ`. -/
theorem buyProb_mul_postBuy_add_sellProb_mul_postSell {θ p : ℝ} (hb : 1 + p * (2 * θ - 1) ≠ 0)
    (hs : 1 - p * (2 * θ - 1) ≠ 0) :
    (1 + p * (2 * θ - 1)) / 2 * postBuy θ p + (1 - p * (2 * θ - 1)) / 2 * postSell θ p = θ := by
  rw [postBuy, postSell, div_mul_div_comm, div_mul_div_comm, mul_comm (1 + p * (2 * θ - 1)),
    mul_comm (1 - p * (2 * θ - 1)), mul_div_mul_right _ _ hb, mul_div_mul_right _ _ hs]
  ring

end MathFin.Execution
