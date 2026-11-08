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
  The first run found 12 groups, and all 12 were removed in the PR that adds the index. In each
  group the survivor is the copy whose module every user of the others already imports. Two
  groups were Mathlib's `max_zero_sub_max_neg_zero_eq_self` under a library name. That reverses
  an earlier review's decision to keep `max_sub_max_neg` as "the finance name": a name is not
  worth a duplicate. One group was lifted into the namespace of the type it is about
  (`ProbabilityTheory.SimpleProcess.coe_finset_sum`). Removed → survivor:
  `normalized_rates_admissible` → `Boundary.normalized_dividend_regime`;
  `Cox.defaultTimeLaw_const` → `PoissonInterarrival.map_firstArrival_eq_expMeasure`;
  `itoSimpleProcess_continuous` → `ItoIntegralProcess.itoSimpleProcess_pathContinuous`;
  `coe_finsetSum_apply`, `coe_simpleProcess_sum` → `SimpleProcess.coe_finset_sum`;
  `binomial_martingale_identity` → `crrUpProb_mul_up_add`;
  `merton_equity_eq_bs_call`, `merton_equity_eq_bs_call_via_brownian` → `bs_call_formula`;
  `garman_kohlhagen_call_formula` → `bs_dividends_call_formula` (`q = r_f`);
  `condExp_exp_increment_of_expMartingale` → `IsExpQMartingale.condExp_exp_increment`;
  `crr_drift_limit_h` → `tendsto_crr_drift_quotient`;
  `max_sub_max_neg`, `positivePart_sub_negativePart` → `max_zero_sub_max_neg_zero_eq_self`;
  `measurableSet_timeBand` → `measurableSet_band`.
- **Mathlib-shaped private lemmas** — `private` and `type_uses_mathfin = false`: a general
  lemma hidden from search and reuse; a `Foundations/` or upstream candidate. Each one resolves
  one of three ways: upstream already has it (call that), it is a one- or two-step application
  of upstream (write it inline where it is used), or it is a genuine fact (make it public under
  a name that says what it proves). Publishing a one-liner trades a hidden helper for a public
  wrapper, which the coherence lens forbids.
- **Metrics** — leaf fraction (runbook 01), dead ends (public, no `used_by`, not cited by the
  corpus), attribute coverage of hub definitions.

## 3. Spine B — one ratchet

`ratchet.json` records one count per debt metric. `python3 -m tools.verify.ratchet check` fails
when a count rises above its baseline; `... update` lowers the baseline after an improvement and
refuses to raise it. Counts computable host-side (heartbeat bumps, `public import Mathlib`
modules, files over 1500 lines, doc-section coverage, nolints) are checked in the Python gates
step; index-derived counts are checked after the index is built. One mechanism replaces the
alternative of a dozen exemption lists.

Metrics: `max_heartbeats`, `whole_mathlib_imports`, `long_files`, `long_lines`, `nolints`, the
doc standard's coverage counts (`modules_without_main_results`: declares a theorem, lists no
main results; `modules_without_main_definitions`: declares a definition, lists none;
`modules_with_uncited_sources`: a work its corpus entries formalize is missing from its
References; `modules_without_tags`), and (index-derived) `private_mathlib_shaped`,
`duplicate_statements`. A count measures what a module owes: a helper module no source covers
is not asked to cite one.

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

- `docs/references.bib` is the single bibliography, for the corpus and the library alike:
  `## References` cites its keys, and each benchmark entry's `metadata.citations` resolves its
  prose `reference` to keys and locators.
- `## Tags` carries the synonyms a reader searches for, plus classification codes written as
  tokens (`JEL G13`, `MSC 91G20`) — Formal Conjectures' classification, at module granularity,
  parseable host-side so the HF dataset can export a subject taxonomy without a Lean
  environment.
- A host-side doc lint (`test_values`) checks layout and resolves citation keys; coverage is a
  ratchet count.

## 5. Spine D — `MathFin/Init.lean`

One module every MathFin module imports (CSLib's `Cslib.Init`, checked by a test). It holds the
library's Lean-level conventions so that adding one later needs no new sweep:

- `register_grind_attr pricing` — the curated grind set for pricing identities (put–call
  parity, the trees' risk-neutral probabilities), CSLib's per-domain grind sets;
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

Delivered 2026-11-06: no module imports Mathlib whole (`whole_mathlib_imports` 0). Two rounds:
`lake shake` narrowed 182 modules, and the other 177 came back as a block of a dozen unrelated
Mathlib leaves. The block is shake's own: Mathlib marks every module that registers a
`positivity`, `norm_num`, `inclusion` or `echelon` extension as an *extra reverse use* (extension
use is not tracked), and shake keeps such a module in every file whose imports reach it.
`lake exe mathfin_shake` (`MathFinTools/Shake.lean`, Lake's shake with that preservation limited
to the library's own modules) narrowed the rest. Where a file relied on an upstream extension the
rebuild failed and the file names the module (`BlackLitterman`: `Positivity.Basic`, kept with a
note); `WienerIntegralL2`'s endpoint identity, which needed Mathlib's whole simp set, is now
proved by cases on `min` and `max`.

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

Delivered 2026-11-06 as the index-driven site (`tools/verify/docs_site.py`, assets in
`tools/verify/site_assets/`, published by `docs-site.yml`). Every page is drawn from the library's
own records, so the site cannot drift from the library:

- **Home**: the map of the library — its sections as a graph (sized by declarations, an edge
  for each section whose modules import another's, foundations at the centre) with a table
  view — and the blueprint landmarks, the proved results the most other results build on.
- **Section pages**: the section's module graph (imports, transitively reduced) and its modules.
- **Module pages**: docstring, subject chips, the import neighbourhood, the corpus entries that
  formalize it, and every public declaration — its statement with each name linked (library
  names to their page, upstream names to Mathlib's docs), docstring, source and used-by.
- **Blueprint**: the proved spine and the frontier nodes on it as a dependency graph, each node
  opening its statement, declaration and issues; the unconnected frontier by area.
- **Corpus** by area and status (stacked bars with a table view), **Subjects** (JEL and MSC
  counts), **References** with the modules that cite each work, and a ranked search.

Graphs are Cytoscape (dagre layout), math is KaTeX; both load from cdnjs/jsdelivr. The generator
itself stays pure stdlib.

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
| **0** | spec; index exe + consumers (`find`, `decl_diff`, duplicates, metrics); ratchet; CI artifact + PR diff summary; first baseline — **delivered**, and the first run's 12 duplicate groups removed (§2) | one local run (daemon down) or runner |
| **1** | doc standard + `references.bib` + doc lint (#187); docs site (doc-gen4 spike first) — **delivered** (below) | runner |
| **1′** | blueprint ↔ issues, always connected — **delivered** (§7) | none |
| **2** | `MathFin/Init.lean` + import check; `grind [pricing]`; automation pass on the top hubs (positivity extensions for `Phi` and `zcb`, `gcongr` and `fun_prop` tags on `Phi`) + `MathFinTest/Automation.lean`; notation policy in `design.md` — **delivered** | daemon |
| **3** | `lake shake` from a runner workflow; ratchet `whole_mathlib_imports` — workflow **delivered** (`import-shake.yml`) | runner |
| **4** | `IsEMM` unification — **delivered**; market-model ladder spec; hub namespaces | daemon |

### What was delivered, and the decisions taken on the way (2026-11-06)

- **Doc standard.** `tools/verify/doc_standard.py`. The hard rules are gated in `test_values`:
  a title comes first, standard sections use their standard names, References and Tags close
  the docstring, every reference carries a bibliography key, and every subject code is in the
  vocabulary. Missing sections are ratchet counts. The five spellings of the results heading
  became `## Main results` in one mechanical pass (320 modules), and the 22 existing References
  sections were keyed to `docs/references.bib`. #187 (the `## Result` gate) is this rule in
  Mathlib's spelling.
- **Subjects as a controlled vocabulary.** A free-form `JEL`/`MSC` token can be misspelt or
  invented; `docs/subjects.toml` lists each admitted code with its official name, the lint
  rejects any other, and the HF export carries the codes as `subjects` (745 of 779 entries;
  the rest import only Mathlib). Every module got a `## Tags` section in this PR: drafted per
  module from its docstring, checked against the vocabulary, and screened for tags naming a
  result the module says it does not prove.
- **`Init`.** `register_grind_attr pricing` is core Lean (v4.35), so the set needs no Mathlib.
  An edge to `Init` connects a module to nothing, so `test_architecture` ignores it when it
  checks that the library is one graph. `Init` is marked `shake: keep-downstream`, so import
  narrowing keeps it. `box_spread_identity`'s proof is now `grind [pricing]`: two applications
  of parity, which is what the proof says.
- **`IsEMM`.** One structure over `[LinearOrder ι]`, in `Foundations/EquivMartingaleMeasure.lean`.
  The ℕ copy (`FTAP.lean`) and the ℝ≥0 copy (`ContinuousMarket.lean`) are gone, together with the
  `adapted` / `integrable` / `condExp_eq` lemmas each had restated. `of_martingale` now comes
  from `martingale_min_iff` directly, and `IsEMM.increment` holds at any time index with a least
  element. `IsEMM.sampled` and `.increment` live in the shared namespace, so dot notation finds
  them. The one-period `OnePeriodVector.IsEMM` remains, as a different presentation (a centred
  increment) with its bridge `isEMM_one_iff_onePeriod`. Rename for the release notes:
  `ContinuousMarket.IsEMM` → `IsEMM`, `ContinuousMarket.IsEMM.{of_martingale, adapted,
  integrable, condExp_eq, sampled, increment}` → `IsEMM.…`.
- **Docs site.** `tools/verify/docs_site.py` builds it from the `decl-index` artifact and the
  module docstrings: module pages, used-by lists, a subject browse, the bibliography and a
  search. `docs-site.yml` publishes it after each green build on main. `docgen-spike.yml` is the
  dispatch-only doc-gen4 measurement; the spike's verdict decides whether doc-gen4 ever replaces
  the generated site.
- **Import narrowing.** `import-shake.yml` runs `lake exe mathfin_shake --fix --add-public --keep-implied`
  over the library's modules, not the umbrella (shake would prune the umbrella's re-exports).
  It rebuilds the result, lowers the ratchet and commits. Snippets that saw a Mathlib name only
  through a module's whole-Mathlib re-export surface in the next ledger sweep.

- **One host-side library model.** `tools/verify/library.py` is the one parser of what the
  host knows about the library: the module files, the aggregators, `Init`, what a file or a
  snippet imports, where a module docstring is. The ledger, the doc standard, the ratchet, the
  HF export, the axiom-audit generator, the host index, the docs site and the architecture,
  router and values tests all read through it, where each used to carry its own list and
  regex. The ledger's import closures are unchanged by the move (checked entry by entry), so
  no input hash moved. `tests/test_library.py` pins the parser and keeps
  `MathFinTools/Index.lean`'s aggregator list in step with it. The bibliography has one parser
  (`doc_standard.bib_entries`), which the docs site reads too.
- **One bibliography for corpus and library.** The corpus's 665 distinct `reference` strings
  name 186 works. Each entry's `metadata.citations` lists them as keys with locators; the HF
  export publishes `reference` and the resolved `citations`. A module's References cite every
  work its corpus entries formalize (351 modules gained bullets); `modules_with_uncited_sources`
  holds that at zero, and `test_doc_standard` checks every corpus key resolves. Where a string
  named a book only by author ("Fabozzi Ch 9", "Shreve 4.5"), the key is the book the same file
  names in full for the same chapters (*Fixed Income Mathematics*; *Stochastic Calculus for
  Finance II*). Works the strings give only as "Author (Year)" are recorded that way, with no
  title invented.
- **Main definitions and Main results everywhere.** Drafted per module from its declarations
  (493 modules), each bullet checked against the statement it names, and validated against the
  host index: a module gets a Main definitions list only when it declares a definition, and a
  bullet naming a theorem under definitions was dropped. Every heading is followed by a blank
  line and the standard sections come in Mathlib's order (both now hard rules).
- **Nolints to zero.** The 16 definitions named with underscores are renamed in Mathlib's
  style, with every name built from them (88 identifiers) and every caller, snippet and doc;
  no alias remains. `SmoothTrunc`'s data fields have docstrings. Renames for the release
  notes: `HasArbitrage_two_state` → `HasArbitrageTwoState`, `HasArbitrage_multi_state` →
  `HasArbitrageMultiState`, `HasEMM_two_state` → `HasEMMTwoState`, `HasEMM_multi_state` →
  `HasEMMMultiState`, `pricingKernel_two_state` → `pricingKernelTwoState`,
  `statePrices_two_state` → `statePricesTwoState`, `hitsLevel_inhabited_above` →
  `hitsLevelEquivAbove`, `reflectionPrincipleEquiv_below` → `reflectionPrincipleEquivBelow`;
  the horizon-`T` versions of an unrestricted object take `Horizon` (`iocSP_T`,
  `itoAssembly_T`, `simpleAssembly_T`, `simpleProcessL2_T`, `timeMeasure_T` →
  `…Horizon`), and the ones with no unrestricted version drop the suffix (`itoIntegralCLM_T`
  → `itoIntegralCLM`, `trimMeasure_T` → `trimMeasure`, `itoIsometry_T` → `itoIsometry`); the
  lemmas named after them follow (`itoIntegralCLM_T_apply` → `itoIntegralCLM_apply`, …).
- **Long lines.** Lean's 100-character linter only warns, so 93 lines had accumulated. They are
  rewrapped (prose by paragraph with code spans kept whole, code at the shallowest bracket
  depth), and `long_lines` is a ratchet count at zero.
- **The `pricing` set holds rewrites grind can use.** `binomialPrice_callPut_parity` was
  tagged and rejected by the build: its strike occurs only inside the payoff lambdas, so no
  pattern binds it. The tag is gone, and the tree identities in the set are the
  risk-neutral-probability ones.
- **Mathlib-shaped private lemmas.** The Lean index counted 193 private lemmas whose
  statement mentions no MathFin constant; the host-side approximation, which reads statements
  as text, found 170 of them. Two are upstream lemmas under a local name and are
  gone: `obsTimes_append_le` is core's `List.forall_mem_append`, and `disjoint_prod_time` is
  `Set.disjoint_prod`. The others are public, under names that say what they prove
  (`integral_lin_comb3` → `setIntegral_const_mul_sub_const_mul_add_const_mul`,
  `callPayoff_le_exp` → `abs_max_exp_sub_zero_le_exp`, …), each with a docstring. Making them
  public exposed a second copy: `PointwiseBracket`'s private increment lemma
  (`condExp_func_increment`) was the Brownian-martingale one at the natural filtration, so
  `PointwiseBracket` now imports `IsFilteredPreBrownian.condExp_comp_increment_eq_const` and
  the copy is deleted. The index's first run found 24 the text scan had missed (a docstring
  or `omit … in` on the line above `private`); they are public too, and the count is zero. A
  private lemma that mentions a MathFin constant is a file-local helper and stays private.
- **Heartbeat bumps stay at their baseline (9).** Each is a long proof (89 to 614 lines) that
  needs splitting into lemmas, and that work needs Lean in the loop. The count can only fall.

Each phase ends with the session-closing prose-against-statement check and, where it changes
proof content, the values review.
