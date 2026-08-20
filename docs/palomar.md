# Palomar registry submission

[Palomar](https://palomar-registry.org) is a registry of Lean-verified
mathematics incubated by the Lean FRO and ICARM. It records a fixed commit of a
public repository together with a small set of declarations that state a
result, re-checks the proof, and publishes the exact statement, the libraries it
trusts, and the review's comments. It is a registry, not a journal: its review
is a filter that either identifies a blocking problem or does not, and finding
none is neither endorsement nor a novelty claim.

Submission rules: [PalomarPolicy/CONTRIBUTING.md][policy].

## What this repository submits

The Lean evidence is a Challenge/Solution pair, checked by
[Comparator][comparator] under [`comparator.json`](../comparator.json):

| File | Role |
|---|---|
| [`Challenge.lean`](../Challenge.lean) | the statement of record — small, self-contained, **Mathlib-only** |
| [`Solution.lean`](../Solution.lean) | the same declarations, discharged against `MathFin/RiskMeasures/` |
| [`comparator.json`](../comparator.json) | which declarations are compared, and under which axioms |
| [`formalization.yaml`](../formalization.yaml) | the v0.4 self-report; its `project.description` is the public abstract |

Status: submitted as `abzuy8zzjtwg` at commit `06f88ca`. Mechanical
verification passed — Comparator accepted both declarations under
`propext`, `Quot.sound`, `Classical.choice`, with the Challenge recorded at
`trust_level: high` and no untrusted sources — and the editorial review
identified no blocking problem. *Registration is a separate, deliberate step*
(it publishes the review and creates preservation tags) and is the maintainer's
decision, so this document does not claim a registry record exists.

Two declarations are compared, both in namespace `ADEH`:

- `ADEH.coherentRisk_isLUB` — the Artzner–Delbaen–Eber–Heath representation
  theorem on a finite state space: a coherent risk measure is the *least upper
  bound* of expected loss over its representing set of probability vectors.
  Discharged against [`MathFin.coherentRisk_isLUB`](../MathFin/RiskMeasures/AcceptanceSet.lean).
- `ADEH.worstCase_isCoherentRisk` — worst-case loss satisfies the four
  coherence axioms. Discharged against
  [`MathFin.worstCase_isCoherent`](../MathFin/RiskMeasures/WorstCaseRisk.lean).

## Why the second declaration is there

The representation theorem is quantified over `IsCoherentRisk ρ`. A theorem
whose hypothesis nothing satisfies is vacuously true and asserts nothing, and no
axiom audit, kernel replay, or `sorry` gate can see that — each of them is
perfectly happy with an empty statement. Registering the worst-case witness
alongside it makes non-vacuity a *mechanically checked* part of the submission
rather than a claim in prose.

This is not hypothetical. Choosing what to submit is what uncovered it in this
library's own CRR→Black–Scholes convergence theorems, whose
`∀ n, BinomialNoArb (crrUp σ T n) …` hypothesis was unsatisfiable at `n = 0`
(`crrStep T 0 = T / 0 = 0`, so `u = d = 1` and no-arbitrage demands
`exp 0 < 1`) — all three were vacuously true, and every gate in the repository
passed them. Fixed on 2026-08-20; see [`docs/coverage.md`](coverage.md).

## The Challenge dependency rule

The Challenge's **transitive import closure** may contain only Lean core,
Mathlib, Tau Ceti, or CSLib — no project-specific source, and previous
registration does not make a repository an approved Challenge dependency. So
`Challenge.lean` may not import `MathFin`, and may not import
`BrownianMotion` either. It restates `IsCoherentRisk` and `representingSet`
with the same bodies as their `MathFin` counterparts; the bridge in
`Solution.lean` is definitional.

That rule is why this result was submitted first. Its statement is expressible
in Mathlib alone — finite index type, real-valued payoffs, `IsLUB` — whereas the
library's Itô, Girsanov and martingale-representation results would need a
Brownian motion *in the statement*, and inlining a surrogate definition of one
into the Challenge is exactly the move the policy warns about.

`Challenge.lean` leaves both theorems as `sorry`: that is the Comparator
contract — the Challenge states, the Solution proves. Both files are
`lake build` default targets, so a change that breaks the submission goes red
here rather than at intake. The library itself remains sorry-free;
[`MathFin/AxiomAudit.lean`](../MathFin/AxiomAudit.lean) and
`tests/test_values.py` are the enforced floor.

[policy]: https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md
[comparator]: https://github.com/leanprover/comparator
