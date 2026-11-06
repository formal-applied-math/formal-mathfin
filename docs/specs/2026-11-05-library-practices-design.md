# Library practices: what the best Lean libraries do that we do not — design

**Date:** 2026-11-05 · **Status:** design, Phase 0 in progress on `feat/library-practices`
**Corpus at design time:** 779 entries, 709 modules
**Companions:** [`design.md`](../design.md) (principle 5, "an abstraction comes with its
interface"), [`values-review.md`](../values-review.md),
[`plans/2026-08-09-program-execution/01-architecture-metrics.md`](../plans/2026-08-09-program-execution/01-architecture-metrics.md)
(subsumed by §2), [`upstreaming.md`](../upstreaming.md)

**Sources compared:** Mathlib, CSLib (`CONTRIBUTING.md`, `CODESTYLE.md`, `NOTATION.md`,
`ORGANISATION.md`), Physlib (README, `scripts/`), Formal Conjectures, Metamath `set.mm`,
MathComp + Hierarchy Builder, Isabelle AFP, FLT/Carleson.

---

## 0. Summary

The library's honesty apparatus — axiom audit, ledger, Comparator, necessity prober,
prose-vs-statement gate, one-graph architecture test — is ahead of most Lean projects. The gap is
on the *use* side: finding what exists, consuming it through automation, and keeping coherence
by mechanism rather than by audit. The October audit found ~60 parallel developments; each
practice below is aimed at the cause of that number.

The rule this design follows is the user's: **adopt in one coherent move, not patches over
patches.** So the practices are not added one gate at a time. They hang off four shared
pieces of infrastructure, each built once:

| spine | one object | what hangs off it |
|---|---|---|
| **A. Declaration index** | `lake exe mathfin_index` → `decl-index.json`, the environment's own account of every MathFin declaration | search, reverse dependencies, statement diff (Physlib `check_golf`), PR declaration summary (Physlib `pr_summary`), duplicate fingerprints, Mathlib-shaped private lemmas, debt and architecture metrics, the docs site |
| **B. One ratchet** | `ratchet.json` + `tools/verify/ratchet.py` | every debt count (heartbeat bumps, whole-Mathlib imports, long files, private Mathlib-shaped lemmas, modules missing doc sections, hub definitions without API) can fall and cannot rise |
| **C. One documentation standard** | the module-docstring layout + `docs/references.bib` | `## Tags` (keywords and JEL/MSC codes) for search and the HF dataset, citation keys for references, a host-side doc lint counted by the ratchet |
| **D. One home for conventions in Lean** | `MathFin/Init.lean`, imported by every module | the `pricing` grind set, attribute declarations, notation policy; checked like CSLib's `checkInitImports` |

The mathematical work — a structure hierarchy and an automation API for the hub definitions —
is then done *against* that infrastructure, which measures it (§5, §6).

## 1. A correction to the first-pass survey

The first-pass comparison said `lake lint` is dispatch-only. It is not: `lean-action` runs the
configured `lintDriver` inside `build.yml`'s build step, so the Batteries env-linter suite has
been a per-push gate all along (`lint.yml`'s header records this, learned at the 2026-07-27
bump). `scripts/nolints.json` (24 entries) is the existing baseline. No change is needed there
beyond counting nolints in the ratchet.

## 2. Spine A — the declaration index

### What it is

A Lean executable, `MathFinTools/Index.lean` (`lean_exe mathfin_index`), that imports the
umbrella `MathFin`, walks the environment, and emits one JSON object per MathFin declaration
(declared in a `MathFin.*` module, internal-detail names excluded):

| field | source |
|---|---|
| `name`, `kind`, `module`, `line` | `ConstantInfo`, `findDeclarationRanges?` |
| `private` | `isPrivateName` |
| `doc` | `findDocString?` |
| `type` | the statement, pretty-printed with fixed options |
| `type_hash` | `Expr.hash` of the type (binder-name independent; stable within a toolchain) |
| `uses` | MathFin constants referenced by the value/proof (`getUsedConstants`) |
| `type_uses_mathfin` | whether the *statement* mentions any MathFin constant |
| `attrs` | `simp`, `fun_prop`, `gcongr`, `grind`, `blueprint`, `instance` membership |

Reverse dependencies (`used_by`) are computed host-side from `uses`.

It replaces nothing that works: `tools/verify/mathfin_index.py` (textual, stdlib, needed host-side
where no Lean environment exists) stays, and gains a CI cross-check against the Lean index, so
its approximation can no longer drift silently. Runbook 01's edge extraction is this exe; its
leaf-fraction report becomes one metric of §2's consumers.

### Where it runs

On the runner, in `build.yml`, after `lake build` (the environment is already built; the load is
the same as `lake lint`'s). The index is uploaded as the `decl-index` artifact. Locally it runs
only with the daemon down (Memory doctrine rule 1).

### What consumes it (host-side Python, stdlib only)

- **`tools/verify/decl_index.py`** — load, `used_by`, queries.
- **`python3 -m tools.verify.find`** — search by name fragment, docstring words, statement
  substring, or constant mentioned. This is the first step of CLAUDE.md's "find what the
  library already has", made a command instead of a grep.
- **`python3 -m tools.verify.decl_diff BASE HEAD`** — the PR declaration diff: added, removed,
  renamed (same `type_hash`, new name), and **statement changed** (same name, new `type_hash`).
  A PR labelled as golf or refactor that changes a statement is visible at a glance; the rename
  list is the release-note input the no-alias rule requires. In CI the base is `main`'s latest
  `decl-index` artifact.
- **Duplicate fingerprints** — two MathFin declarations with one `type_hash` are a duplicate
  statement (the Riemann–Itô-five-times failure, caught at the PR that adds the fifth).
- **Mathlib-shaped private lemmas** — `private` and `type_uses_mathfin = false`: a general
  lemma hidden from search and reuse; a `Foundations/` or upstream candidate.
- **Metrics** — leaf fraction (runbook 01), dead ends (public, no `used_by`, not cited by the
  corpus), attribute coverage of hub definitions.

## 3. Spine B — one ratchet

`ratchet.json` records one count per debt metric. `python3 -m tools.verify.ratchet check` fails
when a count rises above its baseline; `... update` lowers the baseline after an improvement and
refuses to raise it. Counts computable host-side (heartbeat bumps, `public import Mathlib`
modules, files over 1500 lines, doc-section coverage, nolints) are checked in the Python gates
step; index-derived counts are checked after the index is built. One mechanism replaces the
alternative of a dozen exemption lists.

Initial metrics: `max_heartbeats`, `whole_mathlib_imports`, `long_files`, `nolints`,
`modules_without_tags`, `modules_without_references_section`, and (index-derived)
`private_mathlib_shaped`, `duplicate_statements`.

## 4. Spine C — one documentation standard

Every module docstring has the Mathlib layout, with two sections we do not yet use:

```
# Title
<summary>
## Main definitions / ## Main statements   (as now)
## Implementation notes                    (optional)
## References                              [Shreve2004], [KaratzasShreve1991]
## Tags                                    Black–Scholes, lognormal, call price, JEL G13, MSC 91G20
```

- `docs/references.bib` is the single bibliography; `## References` cites its keys. (Benchmark
  `reference` fields keep their prose; resolving them to keys is a follow-up.)
- `## Tags` carries the synonyms a reader searches for, plus classification codes written as
  tokens (`JEL G13`, `MSC 91G20`) — Formal Conjectures' classification, at module granularity,
  parseable host-side so the HF dataset can export a subject taxonomy without a Lean
  environment.
- A host-side doc lint (`test_values`) checks layout and resolves citation keys; coverage is a
  ratchet count, so the 709 existing modules are brought in by touching them, not by a wave.

## 5. Spine D — `MathFin/Init.lean`

One module every MathFin module imports (CSLib's `Cslib.Init`, checked by a test). It holds the
library's Lean-level conventions so that adding one later needs no new sweep:

- `register_grind_attr pricing` — the curated grind set for pricing identities (parity,
  discounting, forward prices), CSLib's per-domain grind sets;
- any MathFin attribute or scoped notation (policy below).

**Notation policy** (a new section of `design.md`, CSLib's `NOTATION.md`): notation shared across
types goes through a typeclass; otherwise it is `scoped` in its namespace. Nothing global.

## 6. The mathematical work the infrastructure measures

### 6a. Automation API for the hub definitions (`design.md` §5, made concrete)

48 `@[simp]`, 5 `@[fun_prop]`, 0 `@[gcongr]`, 0 `positivity` extensions, 1 grind use across
~1,100 definitions. For the hub definitions (ranked by `used_by` from the index): evaluation
lemmas as `@[simp]` (simpNF-clean), measurability/continuity/differentiability under
`@[fun_prop]`, monotonicity under `@[gcongr]` (`kinkedRate_monotone`, `borrowRate_monotone`),
sign facts as `positivity` extensions, identities in `grind [pricing]`. Pinned by
`MathFinTest/Automation.lean` (`example : 0 < … := by positivity`). CSLib's rule is adopted
verbatim into `design.md`: *if a simple fact needs a complicated proof, add the missing lemma,
improve the interface, or reconsider the abstraction.*

### 6b. A structure hierarchy (CSLib vertical reuse; MathComp)

One `structure … extends` in the library. The pilot is the clearest case: `IsEMM` is declared
three times — `Foundations/FTAP.lean` (time `ℕ`), `Foundations/ContinuousMarket.lean` (time
`ℝ≥0`), with identical fields `extends IsEquivProbMeasure P Q` + `martingale : Martingale (fun t ↦
S (min t T)) 𝓕 Q`, and `FTAPOnePeriodVector.lean` (the one-period case). The discrete and
continuous ones become one `IsEMM` over a time index `ι` with `[LinearOrder ι]`, and every caller
moves to it (no alias, per CLAUDE.md). Then the market-model ladder (numéraire market →
arbitrage-free → complete → named models) is designed as its own spec, with the index's `used_by`
counts deciding what each level carries. Hub APIs move into their object's namespace as they are
touched, so dot notation becomes the search (`h.price_eq`, not `price_eq_of_isEMM h`).

### 6c. Imports

359 of 709 modules `public import Mathlib` whole. `lake shake --add-public --keep-implied`
(core Lake) narrows them on a runner, in a PR the workflow opens; the ratchet then holds
`whole_mathlib_imports` down. Whether narrower closures bring kernel replay under the 16 GB
runner is measured after, not promised.

### 6d. Metamath's two practices

- **Used-by pages** — the docs site (§7) shows each declaration's `used_by`.
- **Minimisation after a lift** — when a general lemma lands, the values review's coherence lens
  runs the duplicate/near-duplicate report from the index over its candidates. This is a review
  step, not a gate.

## 7. The docs site

A GitHub Pages site generated from `decl-index.json` + module docstrings: per-module pages,
per-declaration statement + docstring + source link + used-by, Tags/JEL browse, and the search
index. doc-gen4 is spiked first (it documents every imported module, Mathlib included, which may
be prohibitive on a runner); if it is, the index-driven site is the site, not a fallback.

### The blueprint as the program's map (FLT, Carleson) — delivered 2026-11-06

The blueprint and the issue tracker are one system, always connected (the maintainer's
requirement, 2026-11-06). The link is stored once, in the issue: a body line
`Blueprint: <label>, …`. Everything else is derived from it.

- **Nodes.** Proved nodes are the `@[blueprint]` tags (`MathFin/Blueprint.lean` →
  `docs/blueprint_nodes.json`). Frontier nodes — results the open issues work towards, stated,
  not formalized — live in `docs/blueprint_frontier.toml` (label, title, one honest
  statement, uses, area). LeanArchitect's `discussion :=` holds one number, and a frontier
  result has no declaration to tag (the library is sorry-free), so neither carries the link.
- **Invariants** (`tools/verify/blueprint_issues.py`): every open issue labelled
  `type:proof` / `type:research` / `open-problem` / `frontier` names a node (`tracking`
  exempt); every named label is a node; every frontier or partial node has an open issue;
  every proved node is named by an issue or PR, open or closed — its delivery record (#438
  records the 26 nodes pushed before the tracker existed, with their commits).
- **Enforcement.** `build.yml` runs the check on every push; `blueprint-sync.yml` runs it on
  every issue event and nightly, and the bot comments on an issue missing its line (one
  comment, edited when fixed). Static halves (frontier file well formed, exported nodes =
  Lean tags, rendered page current) are `tests/test_blueprint_issues.py`.
- **Views.** `docs/blueprint.md` renders the frontier in per-area subgraphs and a table that
  links each node to a live GitHub search for its label, so no issue list is copied.
- **Templates.** The theorem issue template and the PR template carry the `Blueprint:` line.
- **Backfill (2026-11-06).** 128 open math issues were given their line (103 frontier nodes,
  4 bundle issues split into one node per result); #187 was a tooling issue labelled
  `type:proof` and is relabelled — it is the module-docstring gate of §4 (CONTRIBUTING's
  `## Result` rule), which Phase 1 reconciles with the Mathlib heading layout.

## 8. What we are not adopting, and why

| practice | source | why not |
|---|---|---|
| deprecated aliases | Mathlib | CLAUDE.md: an alias keeps the duplicate it was meant to remove; renames go in release notes (now generated by `decl_diff`) |
| a lower-bar staging library | Physlib Alpha | the 2026-10-21 rule: an unconnected module gets a bridge, never a quarantine. `test_architecture.STAGING` already gives an issue-bounded, short-lived exception |
| in-source TODO tags with their own page | Physlib | a second backlog beside the issue tracker is a parallel object |
| `informal_lemma` | Physlib | `placeholder` / `reduced_core` statuses already carry unproved and narrowed claims, with disclosure |
| working groups, governance docs | CSLib | not at one maintainer's scale |
| global proof minimisation as a gate | Metamath | Lean proofs are not uniformly minimisable; kept as a review step (§6d) |

## 9. Phases

| phase | content | Lean slot |
|---|---|---|
| **0** | spec; index exe + consumers (`find`, `decl_diff`, duplicates, metrics); ratchet; CI artifact + PR diff summary; first baseline | one local run (daemon down) or runner |
| **1** | doc standard + `references.bib` + doc lint (#187); docs site (doc-gen4 spike first) | runner |
| **1′** | blueprint ↔ issues, always connected — **delivered** (§7) | none |
| **2** | `MathFin/Init.lean` + import check; `grind [pricing]`; automation pass on the top hubs + `MathFinTest/Automation.lean`; notation policy in `design.md` | daemon |
| **3** | `lake shake` PR from a runner workflow; ratchet `whole_mathlib_imports` | runner |
| **4** | `IsEMM` unification; market-model ladder spec; hub namespaces | daemon |

Each phase ends with the session-closing prose-against-statement check and, where it changes
proof content, the values review.
