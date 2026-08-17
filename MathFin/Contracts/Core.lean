/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Mathlib

/-!
# A reified payoff language

`Payoff ι` and `Contract ι` represent *what an instrument pays*, independently of
any stochastic model. Market outcomes enter through `Scenario ι = ι → ℝ≥0 → ℝ`;
a stochastic model is a law on that type, and appears only from
`Contracts/Pricing.lean` onward.

Every other payoff in this library — `BlackScholes/Call.lean`, `Digital.lean`,
`CappedCall.lean` — is written inline as a lambda inside the integral that prices
it, so the payoff and the model are the same syntactic object. This file
separates them, which is what lets `Contracts/CappedCall.lean` price a capped
call by *composing* two European call values rather than by evaluating a third
integral.

## Deliberately absent

Branching contracts (`ifThen`), currency, and the lifecycle layer (outstanding
notional, termination, partial redemption). Each is additive and each waits for
the corpus entry that forces it; see
`docs/specs/2026-08-16-contracts-tower-design.md` §2.3.

## Main results

* `Contract.pathPV_both`, `Contract.pathPV_scale` — `pathPV` is additive over
  `both` and homogeneous over `scale`. These are what `Contracts/Pricing.lean`
  integrates to get linearity of `value`.

## Source

The layered separation of contract semantics from pricing semantics, and the
framing "the contract is not the model", are due to Paul Bilokon, *The Contract
Is Not the Model: Proof-Carrying Exotic Derivatives and the Economics of Model
Risk* (working paper, 9 August 2026; Mathematical Finance, Imperial College
London), with code at <https://github.com/thalesians/lean_contracts>
(Apache-2.0). That paper in turn builds on the compositional contract-DSL of
Peyton Jones, Eber and Seward (2000) and the certified-contract work of Bahr,
Berthold and Elsman (2015) and Annenkov (2018).

This file takes his separation of the payoff object from the probability law.
The type design is ours: a typed underlying index rather than `String` keys, a
single inductive rather than a mutual `NumExpr` / `BoolExpr` pair, and `ℝ≥0` time
matching `Filtration ℝ≥0 mΩ`.

No code is copied from `lean_contracts`; every definition and proof here is
written for this library. See `docs/specs/2026-08-16-contracts-tower-design.md`
§6 for the full credit line.
-/

@[expose] public section

open scoped NNReal

namespace MathFin.Contracts

variable {ι : Type*}

/-- A market scenario: for each underlying `i : ι` and time `t : ℝ≥0`, its
realized value. A stochastic model is a probability law on this type. -/
abbrev Scenario (ι : Type*) := ι → ℝ≥0 → ℝ

/-- A payoff formula, reified as data rather than written inline as a lambda.
Independent of any scenario until `Payoff.eval` interprets it against one. -/
inductive Payoff (ι : Type*) where
  | const (c : ℝ)
  | obs (i : ι) (t : ℝ≥0)
  | add (a b : Payoff ι)
  | sub (a b : Payoff ι)
  | mul (a b : Payoff ι)
  | max (a b : Payoff ι)
  | min (a b : Payoff ι)
  | indicatorLt (a b : Payoff ι)

/-- Interpret a `Payoff` against a `Scenario`, producing its realized value. -/
noncomputable def Payoff.eval (s : Scenario ι) : Payoff ι → ℝ
  | .const c => c
  | .obs i t => s i t
  | .add a b => eval s a + eval s b
  | .sub a b => eval s a - eval s b
  | .mul a b => eval s a * eval s b
  | .max a b => Max.max (eval s a) (eval s b)
  | .min a b => Min.min (eval s a) (eval s b)
  | .indicatorLt a b => if eval s a < eval s b then 1 else 0

/-- A contract: what gets paid, when, built from `Payoff`s by combination. -/
inductive Contract (ι : Type*) where
  | zero
  | pay (t : ℝ≥0) (amount : Payoff ι)
  | both (a b : Contract ι)
  | scale (c : ℝ) (a : Contract ι)

/-- The list of `(time, amount)` cashflows a `Contract` generates along a
given `Scenario`. -/
noncomputable def Contract.cashflows (s : Scenario ι) :
    Contract ι → List (ℝ≥0 × ℝ)
  | .zero => []
  | .pay t a => [(t, a.eval s)]
  | .both a b => cashflows s a ++ cashflows s b
  | .scale c a => (cashflows s a).map fun p ↦ (p.1, c * p.2)

/-- The present value of a `Contract` along one scenario path, given a
discount factor `D : ℝ≥0 → ℝ`. -/
noncomputable def Contract.pathPV (D : ℝ≥0 → ℝ) (s : Scenario ι)
    (c : Contract ι) : ℝ :=
  ((c.cashflows s).map fun p ↦ D p.1 * p.2).sum

theorem Contract.pathPV_both (D : ℝ≥0 → ℝ) (s : Scenario ι)
    (a b : Contract ι) :
    (Contract.both a b).pathPV D s = a.pathPV D s + b.pathPV D s := by
  simp [pathPV, cashflows]

theorem Contract.pathPV_scale (D : ℝ≥0 → ℝ) (s : Scenario ι)
    (c : ℝ) (a : Contract ι) :
    (Contract.scale c a).pathPV D s = c * a.pathPV D s := by
  simp only [pathPV, cashflows, List.map_map]
  rw [← List.sum_map_mul_left]
  exact congrArg List.sum (List.map_congr_left fun p _ ↦ by simp; ring)

end MathFin.Contracts
