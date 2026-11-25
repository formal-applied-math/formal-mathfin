# Contributing

This is a Lean 4 library of formally verified mathematical-finance theorems. A plain
`lake build` from the repository root is the canonical verification. Please follow the
[Code of Conduct](CODE_OF_CONDUCT.md).

This file holds the rules. [`docs/onboarding.md`](docs/onboarding.md) walks through a first
contribution from clone to merged pull request, and
[`docs/troubleshooting.md`](docs/troubleshooting.md) lists setup failures with their fixes.
Issues labelled
[`good first issue`](https://github.com/formal-applied-math/formal-mathfin/issues?q=is%3Aopen+label%3A%22good+first+issue%22)
are the entry points; [`docs/issue-labels.md`](docs/issue-labels.md) explains the labels.
Terms such as corpus, entry, frontier and ledger are defined in
[`docs/glossary.md`](docs/glossary.md).

## 1. Find what the library already has

Before writing a theorem, a definition, a tool or a doc, search for it. Search in this order:

1. The library itself. The declaration index is the environment's own record of every MathFin
   declaration (statement, docstring, uses). Search it with
   `python3 -m tools.verify.find forward measure`, `--mentions IsEMM` or
   `--used-by MathFin.X`; `python3 -m tools.verify.find --help` shows where to get a current
   index. Then grep `MathFin/` and read the module docstrings of the area you are entering.
2. BrownianMotion, Degenne's package, which the Brownian and Itô material builds on.
3. Mathlib (`scripts/loogle.sh`, or grep the pinned sources).

New work extends or instantiates what it finds. If an existing statement is too narrow,
generalise it and make the old one an instance. Do not build a parallel object beside it. When a
duplicate is removed, every caller moves to the surviving name, benchmark snippets included, and
no alias is left behind.

## 2. Where a result lives

One concept has one home. The source tree is layered, and imports point one way
(`tools/verify/layers.py`, enforced by `tests/test_architecture.py`):

- `Probability/`: the roots (martingales, Brownian and Itô calculus, Girsanov, jumps, Gaussian
  and other laws, dependence). It imports only Mathlib, BrownianMotion and itself, and is
  Mathlib-shaped.
- `Contracts/`: the payoff language, with no model.
- `Pricing/`: the pricing functional (EMMs, the FTAPs, state prices, numéraires, replication,
  superhedging, the value of a contract).
- the limbs `Models/`, `Risk/`, `Choice/`, `Insurance/`, `Markets/`.

A limb imports another limb only through a declared edge in `layers.EDGES`. A theorem that joins
two places lives in the module that uses it; there is no bridges directory.
[`docs/organization.md`](docs/organization.md) explains the organization.

Every module imports a library module or is imported by one, and is imported by another module
or cited by a corpus entry. A new module stands on what the library has (the normal law `Phi`,
`valueAtRisk`, `bsV`, the numéraire, `zcb`, and so on). A formula the library can derive is
derived, not posited. A module that connects to nothing needs a bridge: a proved theorem tying it
to the library's objects.

Worked demonstrations go in `MathFinExamples/` and API checks in `MathFinTest/`. Both import only
`MathFin`, and nothing in `MathFin/` imports them. [`docs/design.md`](docs/design.md) states the
rules for definitions and statements: a term called a price, an expectation or a probability
carries the conditions that make it one.

## 3. Module header and attribution

A module opens with the copyright block, then the `module` keyword, its `public import`s, the
module docstring, and `@[expose] public section`. `MathFin/Models/Binomial/Model.lean` is a
complete example. Without `@[expose] public section` the declarations are module-private:
importers see nothing while the build stays green (`tests/test_router.py` checks this). A module
that imports no other library module starts with `public import MathFin.Init`.

Put your own name on both the `Copyright (c) YEAR <name>` and the `Authors: <name>` line. The
copyright is yours, and a header copied from a neighbouring module carries someone else's name.
Commit under your own name. Contributions are merged with a merge commit, never squashed, so the
history credits you. If your git name differs from the one in your headers, add a line to
`.mailmap`. Add yourself under Contributors in `README.md` in your first pull request
(`tests/test_attribution.py` checks both).

## 4. The documentation standard

Every module docstring has Mathlib's layout, checked by `tools/verify/doc_standard.py`:
`# Title`, a summary, `## Main definitions` and `## Main results` listing the public
declarations, then `## References` and `## Tags`. A reference cites a key of
`docs/references.bib` as `* [Author, *Title*][Key], §2.3`. Tags are search terms followed by
subject codes from `docs/subjects.toml`, for example `MSC 91G20, JEL G13`. A missing section
raises a ratchet count and fails CI.

## 5. The corpus entry

A theorem that belongs in the corpus gets an entry in the benchmark file for its area
(`benchmarks/*.json`, for example `black_scholes.json` or `risk_measures.json`). The proof stays in
`MathFin/`; the entry is a 5 to 25 line snippet that imports the module, restates the statement and
cites the library lemma. Only a single-line wrapper may stay inline.

- `metadata.formalization_status` is `full`, `library_wrapper` or `reduced_core`. `full` is derived
  from honest hypotheses. `library_wrapper` applies a named Mathlib or BrownianMotion lemma whose
  statement matches. `reduced_core` is a narrower check and says so. A `full` entry whose proof is
  a definitional `rfl` is rejected.
- `description` states what the Lean proves, not the textbook theorem it is named after, and
  `metadata.formalization_scope` discloses any narrowing in full. Both are published in the
  dataset, so neither may claim more than the statement.
- The verification ledger (`verification_ledger.json`) records the input hash under which each
  entry last verified. After any `MathFin/` or benchmark edit, run
  `python3 -m tools.verify.ledger status`; re-verify stale rows with
  `python3 -m tools.verify.ledger verify` (the REPL daemon must be up).
- A `library_wrapper` entry also needs a row in `UPSTREAM_CITATIONS`
  (`tools/verify/axiom_audit_gen.py`) naming, fully qualified, the upstream theorems it uses.
- Regenerate the exhaustive axiom audit after any benchmark edit:
  `python3 -m tools.verify.axiom_audit_gen --write`.
- Every `full` theorem depends only on `propext`, `Classical.choice` and `Quot.sound`. Check with
  `#print axioms myTheorem`; `sorryAx` means a gap.

`python3 -m tools.verify.coverage_report` prints the current split by status.

## 6. The blueprint link

The [blueprint](docs/blueprint.md) is the map of results. A math issue (`type:proof`,
`type:research`, `open-problem`) carries a body line `Blueprint: <label>` naming the node it
advances. A result that is not on the blueprint gets an entry in `docs/blueprint_frontier.toml`
first. A pull request that delivers a frontier node tags the declaration in
`MathFin/Blueprint.lean` under the same label and deletes the frontier entry.
`python3 -m tools.verify.blueprint_issues check` holds both directions.

## 7. Gates

Run the whole `tests/` directory (`python3 -m pytest tests/ -q`, inside the Docker image or in a
Python 3.12 environment) and `lake build && lake lint`. CI runs the tests and
`ledger status` before the Lean build, then the declaration index and ratchet checks. The main
files:

- `tests/test_router.py`: Lean-only code, no `sorry`, `@[expose] public section`, a declared
  `formalization_status` on every entry.
- `tests/test_values.py`: no forbidden tactics or text in `MathFin/`, no `rfl`-backed `full`
  entry, the blueprint spine inside the curated audit, and a byte-fresh `AxiomAuditGen.lean`.
- `tests/test_ledger.py`: every entry has a ledger row, and ids are unique.
- `tests/test_architecture.py`: every module in a layer, imports pointing one way, every module
  connected and used.
- `tests/test_doc_standard.py`: the docstring layout of section 4.
- `tests/test_ratchet.py`: no debt count (long files, duplicate statements, off-blueprint entries,
  layer violations) rises above its baseline in `ratchet.json`.
- `tests/test_attribution.py`: header names and the Contributors list, from git history.
- `tests/test_blueprint_issues.py` and `tests/test_taxonomy.py`: the issue and taxonomy links.

The pull request run summary lists the declarations a change adds, removes and renames, and whose
statements it changes. A golf or refactor change should change no statement. Use the pull request
template (`.github/PULL_REQUEST_TEMPLATE.md`).

A change to a pin file (`lean-toolchain`, `lakefile.lean`, `lake-manifest.json`) follows
[`docs/pin-bumps.md`](docs/pin-bumps.md).

## 8. Style

- One theorem per file when it is non-trivial; helper lemmas live in the same file as `private`.
- Write no comments by default. Add one when the reason is not visible: a hidden invariant, a
  workaround for a specific Mathlib behaviour. Identifiers carry the what.
- Match the surrounding tactic style. [`docs/patterns.md`](docs/patterns.md) catalogues the
  patterns and the Mathlib house-style golf idioms (a bare proof term over `by exact`, no
  hand-written coercions, minimal typeclass assumptions, fewer `have`s).
- Automation (`grind`, `nlinarith`, search tools) scouts; the merged proof shows why the statement
  is true. An opaque premise dump is not merged.
- Before finishing, read each docstring and description you touched against its statement. The
  build is green when the prose claims more than the statement proves, so nothing else catches it.

## 9. Upstream contributions

Drafts for Mathlib and BrownianMotion are written in a worktree of the target repository.
[`docs/upstreaming.md`](docs/upstreaming.md) records what has been submitted. Keep the in-tree
copy until the upstream pull request lands.
