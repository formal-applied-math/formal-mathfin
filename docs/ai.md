# How AI is used in this library

Much of formal-mathfin was written by AI agents working for its maintainer: Lean proofs and
definitions, corpus entries, documentation and the tools that check them. This page says who did
what, what the machine checks and what it does not, where the agents went wrong, and how the
library's work on open problems is organised around that. The provenance record for registries
is [`formalization.yaml`](../formalization.yaml).

## Who does what

- **The agents** are Claude Code sessions and the sub-agents they start, mostly on Claude models.
  They draft statements, write proofs, write corpus entries and docs, and build the checking
  tools. Every session works under the rules in [`CLAUDE.md`](../CLAUDE.md): search the library
  before writing, build on the existing objects instead of beside them, never claim more in prose
  than the statement proves.
- **The maintainer** decides what the library should contain and which results are worth
  stating, directs and reviews the agents' work, and commissions the values review
  ([values-review.md](values-review.md)) that closes each working session adding proof content.
  Changes reach `main` as pull requests; merging a green pull request is a step the maintainer has
  delegated to the agent session working for them, and a statement pinned for an open problem is
  accepted by the maintainer alone.
- **Outside contributors** are credited in the [README](../README.md#contributors) and in the
  header of every module they wrote. How each of them works is their own.
- **An automated pipeline** (the formal foundry) has opened pull requests for a few textbook-sized
  issues; a human reviewed and merged each one.

Some commits on `main` from August to October 2026 show `Claude` as their author: that was the
default identity of the cloud sessions that made them. Since then commits are authored by the
person the session works for.

## What the machine checks

- **Correctness of proofs**, by Lean's kernel, for every module on every build.
- **Axioms**: every constant the corpus cites depends only on `propext`, `Classical.choice` and
  `Quot.sound` ([`MathFin/AxiomAudit.lean`](../MathFin/AxiomAudit.lean) and its generated
  companion).
- **Below the elaborator**: a monthly `leanchecker` replay of every module, and a comparator check
  of the statements submitted to the Palomar registry ([palomar.md](palomar.md)).
- **The shape of the library**: no `sorry`, no forbidden tactics, every module in a layer with
  imports pointing one way, no duplicate statements, every count of known debt held by a ratchet
  that may only fall.

## What it does not check

Whether a statement says what its prose says. A kernel-checked theorem can be weaker than the
theorem it is named after, and the build stays green *because* it is weaker. This is the failure
the library has actually met: [faithfulness.md](faithfulness.md) records 107 cases from the
history where a description claimed more than its statement, by kind, with examples.

A pilot asked a model to judge those cases. Given each statement with its earlier or its corrected
prose, Claude Sonnet 5.5 flagged 60 of the 107 overclaims and called the other 47 faithful, while
passing 104 of the 107 faithful versions. So an AI reviewer does not close the gap: it misses the
overclaims quietly, which is the dangerous direction.

## Where the agents went wrong, and what changed

Each of these is recorded where it was found, and each left a rule or a gate behind.

- **Prose that outran the statement.** The 107 cases above. Since then every corpus entry carries
  a status and a published scope, a test catches the mechanical slice, and the last step of every
  session is to read the prose it touched against its statement.
- **Parallel developments.** An audit in October 2026 found about sixty places where an agent had
  built a new object beside an existing one: the Riemann–Itô sum defined five times, two forward
  measures, a binomial tower beside Mathlib's martingales. Each was green and sorry-free; none was
  connected. The rule since: survey the library, then BrownianMotion, then Mathlib, before writing
  a line, and generalise what exists rather than copy it. Duplicate statements are now a ratchet
  held at zero.
- **A hypothesis no model could meet.** A bundle called `ConditionalOnePeriodFTAP` asked for a
  bounded one-period density with conditional mean one, which an arbitrage-free market need not
  have; theorems assuming it said nothing about such markets. It was replaced by a weaker,
  satisfiable notion, and for one asset the hypothesis is now proved
  ([values-review.md](values-review.md), "One pasting trunk").
- **Conclusions hidden in hypotheses.** Some entries assumed a structure whose fields contain the
  textbook conclusion. Each is marked `reduced_core` and says so in the same field, and a `full`
  entry whose proof is a definitional `rfl` now fails a gate. Of the eleven such entries in
  November 2026, nine have since been replaced by proofs (the reflection principle, nowhere
  differentiability, Novikov's unit mean, the Markov theorems); two remain.
- **Islands.** Proved results that no proof tied to the rest of the library: 34 of them on
  7 November 2026, among them the equivalent martingale measures. A node now joins the tree only
  through a shared object or a bridge theorem, and the count of islands is a ratchet, now zero.

## The cátedra: agents on open problems

The [catalogue of open problems](research-problems/README.md) is worked by the cátedra
([design](specs/2026-11-20-catedra-design.md)): six agent roles, each a definition with the
library's rules in its brief.

| Chair | Its job |
|---|---|
| Scout | finds problems a dated source states as open, and searches for resolutions |
| Formalizer | states a problem in Lean |
| Referee | reads the Lean statement against the source, without seeing the Formalizer's reasoning |
| Prover | proves a stated problem |
| Disprover | looks for a proof of the negation, and for counterexamples |
| Builder | builds the definitions that blocked problems need |

The design follows from the two sections above. In mathematics the kernel checks proofs
perfectly, so review effort goes to the one thing it cannot check: whether the statement is the
problem. The rules: solved means a kernel-checked proof of a statement the maintainer has pinned;
pinning and merging stay human; attempts, rejections and gaps found in claimed proofs are recorded
with the successes. A chair never merges its own work.

The scaffolding was built on 26 November 2026, and the first Referee passes judged the Lean
statements of MF-OP-008, MF-OP-016 and MF-OP-017 faithful to their sources.
