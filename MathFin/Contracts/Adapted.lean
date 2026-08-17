/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import MathFin.Contracts.Core

/-!
# A payoff is measurable, and adapted to its observation times

A `Payoff` is data, not yet a random variable: `Payoff.eval` only produces one
once it is applied to a `Scenario`. This file supplies the missing link —
substitute a genuinely stochastic model `X : ι → ℝ≥0 → Ω → ℝ` for the
`Scenario`, and `fun ω ↦ e.eval (fun i t ↦ X i t ω)` is measurable
(`Payoff.measurable_eval`), and moreover `𝓕 u`-measurable as soon as every
observation the payoff makes is dated no later than `u`
(`Payoff.measurable_eval_of_obsTimes_le`). That second fact is what makes a
`Payoff` a legitimate integrand: it is the exact adaptedness hypothesis
`Contracts/Pricing.lean` needs to integrate a contract's cashflows against a
filtered probability space.

## Main definitions

* `Payoff.obsTimes` — the list of times a payoff's `obs` leaves read, found by
  walking the syntax tree. It is a *syntactic* over-approximation: a payoff
  can mention a time inside a branch that evaluation never takes (e.g. the
  `false` side of an `indicatorLt`), so `obsTimes` may list times the value
  does not actually depend on. Consequently the adaptedness theorem below is
  *sufficient*, not necessary — a payoff can be `𝓕 u`-adapted for reasons
  `obsTimes` does not see.

## Main results

* `Payoff.measurable_eval` — evaluating a payoff against a jointly-measurable
  model is measurable, unconditionally.
* `Payoff.measurable_eval_of_obsTimes_le` — if every time in `e.obsTimes` is
  `≤ u` and each `X i t` is `𝓕 t`-measurable, then evaluating `e` against `X`
  is `𝓕 u`-measurable. The filtration's monotonicity (`𝓕.mono`) does the work
  in the `obs` leaf; the six binary constructors combine two adapted pieces
  into one by the corresponding `Measurable.add`/`.sub`/`.mul`/`.max`/`.min`
  lemma, or `Measurable.ite` composed with `measurableSet_lt` for
  `indicatorLt`.

## Source

The layered separation of contract semantics from pricing semantics, and the
framing "the contract is not the model", are due to Paul Bilokon, *The Contract
Is Not the Model: Proof-Carrying Exotic Derivatives and the Economics of Model
Risk* (working paper, 9 August 2026; Mathematical Finance, Imperial College
London), with code at <https://github.com/thalesians/lean_contracts>
(Apache-2.0). That paper in turn builds on the compositional contract-DSL of
Peyton Jones, Eber and Seward (2000) and the certified-contract work of Bahr,
Berthold and Elsman (2015) and Annenkov (2018).

Bilokon's `Contract.observationTimes` exists to feed a syntactic chronology
check discharged `by decide`; the same function here carries content, as the
hypothesis of an adaptedness theorem. The measurability and adaptedness
results have no counterpart in the source.

No code is copied from `lean_contracts`; every definition and proof here is
written for this library. See `docs/specs/2026-08-16-contracts-tower-design.md`
§6 for the full credit line.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace MathFin.Contracts

variable {ι Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The times a `Payoff`'s `obs` leaves read, found syntactically. An
over-approximation: a payoff can mention a time on a branch evaluation never
takes, so this may list times the value does not actually depend on. -/
def Payoff.obsTimes : Payoff ι → List ℝ≥0
  | .const _ => []
  | .obs _ t => [t]
  | .add a b | .sub a b | .mul a b | .max a b | .min a b | .indicatorLt a b =>
      a.obsTimes ++ b.obsTimes

/-- Evaluating a payoff against a jointly-measurable model is measurable. -/
theorem Payoff.measurable_eval (e : Payoff ι) (X : ι → ℝ≥0 → Ω → ℝ)
    (hX : ∀ i t, Measurable (X i t)) :
    Measurable fun ω ↦ e.eval (fun i t ↦ X i t ω) := by
  induction e with
  | const c => exact measurable_const
  | obs i t => exact hX i t
  | add a b ha hb => exact ha.add hb
  | sub a b ha hb => exact ha.sub hb
  | mul a b ha hb => exact ha.mul hb
  | max a b ha hb => exact ha.max hb
  | min a b ha hb => exact ha.min hb
  | indicatorLt a b ha hb =>
      exact Measurable.ite (measurableSet_lt ha hb) measurable_const measurable_const

/-- If a hypothesis `∀ t ∈ l₁ ++ l₂, t ≤ u` holds, it holds on each summand
separately. Stated on the raw list (rather than on `Payoff.add`'s `obsTimes`)
so it is reusable, unconditionally, across all six binary constructors. -/
private theorem obsTimes_append_le {u : ℝ≥0} {l₁ l₂ : List ℝ≥0}
    (h : ∀ t ∈ l₁ ++ l₂, t ≤ u) :
    (∀ t ∈ l₁, t ≤ u) ∧ (∀ t ∈ l₂, t ≤ u) :=
  ⟨fun t ht ↦ h t (List.mem_append.mpr (.inl ht)),
    fun t ht ↦ h t (List.mem_append.mpr (.inr ht))⟩

/-- Evaluating a payoff against a filtration-adapted model `X` is adapted to
`𝓕 u`, as soon as every time the payoff observes is dated no later than `u`.
This is the theorem that makes a `Payoff` a legitimate integrand: it is the
adaptedness hypothesis `Contracts/Pricing.lean` needs. -/
theorem Payoff.measurable_eval_of_obsTimes_le
    {𝓕 : Filtration ℝ≥0 mΩ} {u : ℝ≥0} (e : Payoff ι) (X : ι → ℝ≥0 → Ω → ℝ)
    (hX : ∀ i t, Measurable[𝓕 t] (X i t))
    (hle : ∀ t ∈ e.obsTimes, t ≤ u) :
    Measurable[𝓕 u] fun ω ↦ e.eval (fun i t ↦ X i t ω) := by
  induction e generalizing u with
  | const c => exact measurable_const
  | obs i t => exact (hX i t).mono (𝓕.mono (hle t (by simp [obsTimes]))) le_rfl
  | add a b ha hb =>
      obtain ⟨hl, hr⟩ := obsTimes_append_le hle; exact (ha hl).add (hb hr)
  | sub a b ha hb =>
      obtain ⟨hl, hr⟩ := obsTimes_append_le hle; exact (ha hl).sub (hb hr)
  | mul a b ha hb =>
      obtain ⟨hl, hr⟩ := obsTimes_append_le hle; exact (ha hl).mul (hb hr)
  | max a b ha hb =>
      obtain ⟨hl, hr⟩ := obsTimes_append_le hle; exact (ha hl).max (hb hr)
  | min a b ha hb =>
      obtain ⟨hl, hr⟩ := obsTimes_append_le hle; exact (ha hl).min (hb hr)
  | indicatorLt a b ha hb =>
      obtain ⟨hl, hr⟩ := obsTimes_append_le hle
      exact Measurable.ite (measurableSet_lt (ha hl) (hb hr)) measurable_const measurable_const

end MathFin.Contracts
