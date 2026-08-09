# 03 — formal-econometrics phase 0: one theorem end-to-end, then judge

**Repo:** `formal-econometrics` (create it) · **Trigger:** now · **Est. scope:**
2 weeks wall-clock, a few sessions
**Design sources:** `formal-mathfin/docs/applied-areas.md` §3.1, §6 (phase 0), §7
(kill criteria); `docs/program-architecture.md` §1 (the copy-then-genericize rule).

## Goal

Prove **one identification theorem end-to-end** — parallel trends ⇒ ATT identified
(difference-in-differences) — inside a scaffold that is a deliberate copy of
formal-mathfin's apparatus. This is a **probe, not a launch**: its purpose is to
find out whether the potential-outcomes definitional layer comes out idiomatic
over Mathlib's measure theory. The kill criterion is the deliverable as much as
the theorem is.

## Why this theorem first

It is the cheapest full test of the definitional layer: it needs potential
outcomes, treatment/time indexing, a conditional-expectation estimand, and one
identification argument — but no instrument, no continuity-at-cutoff, no
monotonicity. Everything it needs exists in Mathlib at the pin
(`condExp`, basic integrability; substrate audit in `applied-areas.md` §2).

## Repo bootstrap

1. Create the GitHub repo `raphaelrrcoelho/formal-econometrics` (ask the user to
   create it / confirm the name before pushing anywhere).
2. Scaffold **by deliberate copy** from formal-mathfin — this is the
   copy-then-genericize rule; do NOT try to share code with mathfin yet:
   - `lean-toolchain`, `lakefile.lean`, `lake-manifest.json` — **same pins
     exactly** (`leanprover/lean4:v4.32.0`, Mathlib `81a5d257c8…`). Drop the
     BrownianMotion / kolmogorov_extension4 deps (not needed; smaller closure).
   - `tools/` — copy `verify/` + `formalization_yaml.py` wholesale. Rename
     nothing yet. Adjust only: `mathfin.toml` → `econometrics.toml`
     (`local_project = "."`), the library name in `Router`/`corpus` config, and
     the benchmarks dir path. **Keep a log of every line you had to touch** in
     `docs/apparatus-divergence.md` — that log is the input runbook 04 consumes.
   - `tests/` — copy the three gate suites; same divergence-log rule.
   - `.github/workflows/build.yml` — copy, pointing at this repo's library.
     Skip the Docker/GHCR image for phase 0 (plain `lean-action` + `lake exe
     cache get` is enough at this size); note the omission in the divergence log.
   - `CLAUDE.md` — write fresh but short: pins, gates, memory doctrine pointer,
     and the phase-0 scope statement. Do not copy mathfin's wholesale (most of it
     describes machinery this repo doesn't have yet).
3. Library root: `Econometrics/` with `Econometrics.lean` umbrella; module-system
   rule applies (`module` header + `@[expose] public section` — copy the
   enforcing test).

## The mathematics

Module 1 — `Econometrics/Identification/PotentialOutcomes.lean`:
- A minimal potential-outcomes layer over a `MeasureSpace Ω`: outcome pair
  `Y₀ Y₁ : Ω → ℝ` (or time-indexed for DiD: `Y : Bool → Bool → Ω → ℝ`,
  treatment-arm × period), treatment `D : Ω → Bool`, observed outcome
  `Yobs = fun ω ↦ if D ω then Y₁ ω else Y₀ ω`.
- Design for the NEXT theorems while writing this one (IV/LATE need the same
  layer plus an instrument) but implement only what DiD consumes. No speculative
  generality — that is the same seams-guessed-wrong trap.

Module 2 — `Econometrics/Identification/DiD.lean`:
- State parallel trends as the conditional-expectation restriction
  `𝔼[Y₀(post) − Y₀(pre) | D = 1] = 𝔼[Y₀(post) − Y₀(pre) | D = 0]`
  (with the integrability hypotheses Mathlib's `condExp`/`integral` actually
  need — finding the *minimal* hypothesis set is part of the probe).
- Prove: ATT `= 𝔼[Y₁(post) − Y₀(post) | D = 1]` equals the DiD contrast of four
  observable conditional means. Every object on the right-hand side must be a
  functional of `(Yobs, D, period)` only — that *observability* discipline is the
  whole point of an identification library; state it as a definition, not a
  comment, if at all feasible.
- House style applies from day one: Mathlib house-style checklist
  (`formal-mathfin/docs/patterns.md` → "Mathlib house-style golf"), bare terms
  over `by exact`, minimal typeclasses, no hand-written coercions.

Benchmark — `benchmarks/identification.json`: one entry (`did-att-1`), domain
value permitted by the copied Router (add `econometrics` to the Domain enum —
divergence log), `formalization_status: full`, snippet importing the module.

## Verification path (phase 0, no Docker)

- `lake exe cache get && lake build` — Mathlib comes from the cache server, no
  local Mathlib build. **Memory doctrine: formal-mathfin's daemon must be DOWN
  first** (`docker ps` to confirm; one Lean process on the box, across repos).
- Gates host-side: `python3 -m pytest tests/ -q`, ledger init + status, coverage
  report. The ledger, audit generator, and `formalization.yaml` must actually run
  against this corpus of one — a copied gate that was never executed is scaffold
  theater.
- `Econometrics/AxiomAudit.lean` with the DiD theorem pinned to
  `[propext, Classical.choice, Quot.sound]`.

## Acceptance criteria

- [ ] `lake build` green from clean clone; zero `sorry`; axiom-pinned.
- [ ] All copied gates RUN and pass against the one-entry corpus.
- [ ] `docs/apparatus-divergence.md` lists every touched line of copied tooling.
- [ ] The DiD statement's hypotheses are the minimal ones Mathlib forced, and
      the README states the scope honestly (one theorem; a probe).
- [ ] Public repo, pushed, CI green.

## Kill criteria (from applied-areas.md §7 — these are the deliverable)

- **If the potential-outcomes layer needs bespoke measure-theoretic scaffolding
  rather than consuming `condExp` directly** — more than ~a screenful of adapter
  lemmas that Mathlib "should" have had — STOP. Write up exactly which lemmas
  were missing and why, in `docs/phase0-verdict.md`. That writeup redirects the
  program (maybe the layer wants a different encoding; maybe the missing lemmas
  are themselves the first `ForMathlib/` block). Do not grind through.
- If DiD closes but only via an unfaithful reduction (e.g. finite Ω hardcoded
  where the informal theorem is general), label it `reduced_core` honestly and
  report the obstruction — do NOT ship it as `full` to make phase 0 look green.

## After (not this runbook)

~20 entries → runbook 04 (genericize apparatus against the divergence log).
IV/LATE/RDD build-out per `applied-areas.md` §3.1. Foundry pack for econometrics
(runbook 02's contract) once pillars stabilize.
