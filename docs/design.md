# Designing definitions and statements

[`architecture.md`](architecture.md) says where a result belongs, and [`patterns.md`](patterns.md)
how to prove it. This page is about the step in between: choosing the definitions and the shape of
the statement. The kernel checks that a proof is correct. It cannot check that `bsV` is the
Black–Scholes price, or that a theorem called a pricing formula prices anything. That
correspondence is a design question, and these principles are how we answer it.

Most of them are adapted from [MathEconLib's `DESIGN.md`](https://github.com/matheconlib/matheconlib/blob/main/DESIGN.md)
(Daniel Lyng and Scott Duke Kominers), which states them for economics. The examples here are ours.
They are strong defaults, not rules: a departure is fine when its reason can be written in the
docstring.

## 1. A definition holds what the concept needs, and nothing else

For each field or hypothesis of a definition, ask whether removing it would admit an object that no
longer deserves the name. If it would not, the field belongs in the theorems that use it, not in
the definition. Check the other direction too: a definition that admits something a probabilist
would reject is missing a condition.

`BinomialNoArb u d r` is exactly `0 < d < e^r < u`, the condition under which the one-period tree
has no arbitrage. It says nothing about strikes or payoffs, so every binomial result can use it.

The same holds for theorems. A hypothesis enters at the first statement whose proof uses it. One
the proof never consumes is a defect (`lake lint` catches the `unusedArguments` case; a hypothesis
that is used but stronger than needed is a review question). And a theorem's name and docstring say
what the statement proves: an algebraic identity on the way to a pricing result is not itself the
pricing result.

## 2. A junk value never gets a financial meaning

Lean makes partial operations total. `x / 0 = 0`, the Bochner integral of a non-integrable
function is `0`, `ENNReal.toReal ∞ = 0`, and `ProbabilityTheory.cond` on a null event returns the
zero measure. This is logically harmless, since none of it proves `False`. But the totalized value
looks exactly like a meaningful quantity, so a statement about it can be a true Lean theorem and a
false finance claim. The library has met this repeatedly:

- `crrUpProb u d r = (e^r − d)/(u − d)` is `0` when `u = d`, not a probability of anything.
- The Lévy-model exponent `κ(θ)` read as `𝔼[e^{θY}] = e^{κ(θ)τ}` without `∫ e^{θx} dν < ∞`: where
  the integral is infinite the Bochner integral is `0` and `κ(θ)` is junk (values review,
  2026-08-07).
- An Itô-process drift `A` that is not assumed measurable makes every drift integral `0`, and the
  theorem then says nothing about it (disclosed in `ItoFormulaAdapted.lean`).
- `cirBondA κ θ 0` is junk, while the true limit as `σ → 0` is the deterministic Vasicek-type
  loading.
- In Glosten–Milgrom, a prior at `θ = 1, p = 1` makes a trade event null. The quote is then the
  integral against the zero measure, `0`, and the closed-form spread returns the whole `V_H − V_L`
  at the one point where the true spread is `0`.

The rule:

- **A public theorem that calls a term a price, an expectation, a probability, a rate or a
  hedge carries, or derives, the conditions under which the term means that**: the integrability,
  the non-zero denominator, the `≠ ∞`, the non-null conditioning event. Low-level definitions may
  stay total; their docstrings say where the value is junk.
- **Prefer the formulation without the partial operation** when it says the same thing.
  `q · (u − d) = e^r − d` needs no `u ≠ d`; a weighted identity `w = f · φ` needs no non-zero
  density, while the quotient `φ = w / f` does.
- **Where a junk value is reachable at the edge of the parameters, say so, and prove it when that
  is cheap.** `GlostenMilgrom.spread_junk_at_corner` is the model: it evaluates the closed form at
  the excluded corner and shows the answer is wrong. That explains why the hypothesis is there
  better than any comment would.
- **The prose follows.** A docstring or corpus `description` never calls the term a price outside
  the conditions its statement carries. This is part of the standing first pass of the
  [values review](values-review.md).

## 3. Propositions are `Prop`, chosen objects are data

A hypothesis bundle is a `structure … : Prop` (`BinomialNoArb`, `BSCallHyp`), so it can appear
under `¬`, `∃` or in a set-builder. A chosen object that later definitions compute with (a measure,
a strategy, a density, a calibration) is an explicit argument or a structure in `Type`, with the
laws it must satisfy as fields. When only existence matters, state existence (`∃`, `Nonempty`).

Make something a `class` only when instance search should find it from context and a small set of
instances covers the uses, as Mathlib does for `IsProbabilityMeasure` or `IsFiniteMeasure`. No-
arbitrage, completeness or an integrability condition is part of the argument, so it is an ordinary
hypothesis passed by name.

## 4. A change of representation is a map with laws

When one object is another seen through different inputs, construct it from the original by an
explicit map rather than defining it a second time. Give the map its identity and composition
lemmas, a preservation lemma for each property it carries forward, and a reflection lemma (with
its extra hypothesis) for each property it carries back. Without the map, every pair of
representations needs its own bridge theorems, and the two definitions drift apart.

The library's bridges are this principle at the scale of modules
([`architecture.md`](architecture.md#the-bridge-methodology), [`bridges.md`](bridges.md)): a
constructor such as `BSCallHyp.of_isPreBrownian` turns a Foundations object into the
hypothesis a pricing module already consumes, instead of a second pricing module built on Brownian
motion. The same discipline applies to smaller changes: a discounted price process, a change of
numéraire, a pushforward of the pricing measure, an `Lp` class and its representative.

## 5. An abstraction comes with its interface

A reusable definition ships the lemmas that let a consumer use it without unfolding it: evaluation,
the characterization a finance reader expects, extensionality, and the bridges of principle 4. A
consumer that has to unfold three layers to state an inequality is a sign the interface is missing.
This does not mean publishing every projection; a lemma proved by `rfl` belongs in the API only
when it records a real contract of the construction. `@[simp]` is for rewrites toward one normal
form, never for both directions of an equation.

A named abstraction is expensive, because users must find it and maintainers must keep it. Add one
when it has a second consumer, supports a theorem shared by several applications, or lets one proof
replace several. Otherwise keep the expression local.

## 6. A headline result is shown to apply

A theorem whose hypotheses can never all hold proves nothing, and the build stays green. A headline
result is therefore exercised by a concrete case: build the model, prove every hypothesis for it,
and apply the theorem. `binomialNoArb_crr` is the example. It discharges the `hna` hypothesis of the
CRR → Black–Scholes limit whenever `|r|√T < σ`, so the limit is known to apply to every such tree.
Constructing only the inputs certifies that the hypotheses are satisfiable, not that the conclusion
says what the docstring claims. Where the definition has a boundary (the endpoints of
Glosten–Milgrom's prior, `u = d` in the binomial tree), a small counterexample at the boundary
shows the hypothesis is load-bearing.

These applications live in `MathFinExamples/`, built with the library, so they break when the
theorem changes. Not every README main result has one yet.
