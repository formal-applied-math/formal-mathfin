# Documentation

The documents, grouped by what a reader wants to do. The [glossary](glossary.md) explains the
library's own vocabulary; the [README](../README.md) gives the main results and how to build.

## Learn

| Document | What it is |
|---|---|
| [`beginners-manual.md`](beginners-manual.md) | Lean 4 and the library for mathematicians who have not used Lean: reading a file and a statement, finding a theorem, checked exercises. |
| [`../MathFinExamples/`](../MathFinExamples) | Worked examples: a tour of headline results, and applications from a capped call to a chain-ladder reserve, each saying what the library supplies and what it does not. |
| [`organization.md`](organization.md) | How the library organizes mathematical finance: one object, three questions, the model families, the tools. |
| [`mathematical-architecture.md`](mathematical-architecture.md) | The four methods the library's results are proved with, and the seams between them. |
| [`glossary.md`](glossary.md) | The words the library uses in a sense of its own. |
| [`american-put-boundary.md`](american-put-boundary.md) | The convexity of the American put's exercise boundary: statements, definitions, proof sketch. |

## Build

| Document | What it is |
|---|---|
| [`../CONTRIBUTING.md`](../CONTRIBUTING.md) | The rules for adding a result: search first, where it lives, headers, the doc standard, the corpus entry, the blueprint link, the gates. |
| [`onboarding.md`](onboarding.md) | A first contribution, from clone to merged pull request. |
| [`design.md`](design.md) | Principles for definitions and statements: minimal definitions, no financial meaning for junk values, interfaces, applied headline results. |
| [`architecture.md`](architecture.md) | The layers of the source tree, the direction of imports, and how the library is kept one graph. |
| [`patterns.md`](patterns.md) | Lean and Mathlib proof patterns, idioms and anti-patterns met in this library. |
| [`pin-bumps.md`](pin-bumps.md) | When the Lean, Mathlib and BrownianMotion pins move, and what must be true before a bump merges. |
| [`troubleshooting.md`](troubleshooting.md) | Symptom, cause and fix for build, environment and gate failures. |
| [`issue-labels.md`](issue-labels.md) | What each issue label means. |
| [`upstreaming.md`](upstreaming.md) | How results move upstream to BrownianMotion and Mathlib, and the record of what has. |
| [`../AGENTS.md`](../AGENTS.md) | For AI agents: using the library, and the rules for developing it. |

## Research

| Document | What it is |
|---|---|
| [`blueprint.md`](blueprint.md) | The map: every proved node with its Lean declaration, the frontier of results stated next, and their dependencies. |
| [`research-problems/`](research-problems/README.md) | The catalogue of open problems of the field (`MF-OP-NNN`): precise statements, sources, mathematical and Lean status. |
| [`open-problems.md`](open-problems.md) | The earlier survey and candidate pool the catalogue was drawn from. |
| [`hjm-program.md`](hjm-program.md) | The Heath–Jarrow–Morton program: what is proved and what remains. |
| [`ai.md`](ai.md) | How AI is used here: who does what, what the machine checks and what it does not, where the agents went wrong, and the cátedra. |
| [`faithfulness.md`](faithfulness.md) | When the prose said more than the Lean: 107 confirmed cases from the history, their kinds, and what catches them now. |
| [`coverage.md`](coverage.md) | The dated log of status changes and corrections to corpus entries. |
| [`sources.md`](sources.md) | Outside work the library draws on, and what was taken from each. |

## The program

| Document | What it is |
|---|---|
| [`status.md`](status.md) | Where the program stands and where the work is: the issue tracker by area. |
| [`roadmap.md`](roadmap.md) | Strategy: depth before breadth, and how a new area is admitted. |
| [`values-review.md`](values-review.md) | The judgment review that closes each session adding proof content, and its record. |
| [`palomar.md`](palomar.md) | The Palomar registry entry and the comparator check behind it. |
| [`hammer-pilot-2026-06-06.md`](hammer-pilot-2026-06-06.md) | The LeanHammer pilot, why its verdict has expired, and how to re-test it. |

## Data the tools read

[`taxonomy.toml`](taxonomy.toml) (the organization), [`blueprint_frontier.toml`](blueprint_frontier.toml)
and [`blueprint_retired.toml`](blueprint_retired.toml) (the frontier and the retired labels),
[`landmarks.toml`](landmarks.toml) (the headline results), [`references.bib`](references.bib) (one
bibliography), [`subjects.toml`](subjects.toml) (JEL and MSC codes).

## Records

[`specs/`](specs) holds the design records the code cites, and [`archive/`](archive) the documents
whose work is done: the phase log ([`archive/roadmap-history.md`](archive/roadmap-history.md)), the
v4.31 → v4.32 upstream-consumption review (its drift sweep is re-run at each pin bump), and the
Itô-integral deferral note the Itô modules cite. [`bridges.md`](bridges.md) is the 2026-05-22 audit
of the old foundation layer, kept because modules and corpus entries cite its rows. Earlier plans
and reviews are in git history.
