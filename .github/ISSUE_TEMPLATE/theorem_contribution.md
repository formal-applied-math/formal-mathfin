---
name: Theorem contribution
about: Propose formalizing a new theorem or upgrading a reduced_core entry to full
title: "Formalize: <theorem name>"
labels: "type:proof"
assignees: ""
---

## Theorem

<!-- State the mathematical result in plain prose + the standard reference (author, year, textbook section). -->

## Blueprint

<!-- The blueprint node(s) this advances (docs/blueprint.md, the program's map). Name an
existing node, or add a frontier node to docs/blueprint_frontier.toml and name it here.
A bot checks this line; keep it on its own line. -->

Blueprint: thm:<node-label>

## Lean location

<!-- Where does this belong in MathFin/? Which existing module is the closest neighbour? -->

**Proposed file:** `MathFin/<Section>/<Module>.lean`
**Benchmark id:** `<domain>-<id>`
**Proposed status:** `full` / `library_wrapper` / `reduced_core`

## Proof sketch

<!-- 3–5 sentences: the key steps and which Mathlib / BrownianMotion lemmas you expect to consume. -->

## Prerequisites

<!-- Any MathFin modules this depends on. Flag if it is blocked on upstream (Mathlib / Degenne). -->

## Scope honesty

<!-- Is this the full textbook theorem, or an honest narrowing? If narrowing, say exactly what is narrowed. -->

## Size estimate

<!-- Rough LOC and whether you expect one session or multiple. -->
