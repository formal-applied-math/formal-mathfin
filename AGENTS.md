# AGENTS.md

This file is for agents that work with this repository. Part one is for an agent that wants to read,
cite or depend on the library. Part two is for an agent that changes the repository.

## Using the library

MathFin is a Lean 4 library of formally verified mathematical finance, built on Mathlib and the
BrownianMotion package. It has no `sorry`, and every theorem the corpus cites is pinned by the build
to `propext`, `Classical.choice` and `Quot.sound`. The site
(<https://formal-applied-math.github.io/formal-mathfin/>) is generated from the library's
declaration index and publishes [`llms.txt`](https://formal-applied-math.github.io/formal-mathfin/llms.txt),
which carries the same summary with current counts.

**Pins and dependency.** `lean-toolchain` fixes the Lean version and `lake-manifest.json` the Mathlib
and BrownianMotion revisions. To depend on the library, add a `[[require]]` entry named `MathFin`
with `git = "https://github.com/formal-applied-math/formal-mathfin"` and `rev` set to a release tag,
then `lake update`, `lake exe cache get`, `lake build`, and `import MathFin`. The README section
"Using the library in a project" has the exact lines.

**Finding a theorem.**

- The site search matches names, statements and docstrings; `search.json` at the site root is the same
  data.
- `python3 -m tools.verify.find <words>` searches the declaration index (`decl-index.json`, produced
  by `lake exe mathfin_index`, and the `decl-index` artifact of the latest `build` run on `main`);
  `--mentions <name>` and `--used-by <module>` follow the dependency graph.
- `grep -rn` over `MathFin/` works, and the module docstrings (`## Main results`) name each file's
  theorems.

**Checking a statement.** The statement is the claim, not the prose around it. Read it in the Lean
source or on the module page, check it with `#check`, and run `#print axioms <name>` in a file that
imports `MathFin`; the result should list only the three standard axioms.

**Citing a corpus entry.** Each entry in `benchmarks/*.json` (and the Hugging Face dataset) has
`metadata.formalization_status`:

- `full`: the theorem as stated.
- `library_wrapper`: restates a Mathlib or BrownianMotion lemma.
- `reduced_core`: proves less than the result it is named after.

Cite only `full` and `library_wrapper` entries as the named theorem. Read the entry's `description`
and `metadata.formalization_scope` for what it proves and what it leaves out. The terms used here are
defined in `docs/glossary.md`.

## Developing the library

The full rules for agents that change this repository are in [`CLAUDE.md`](CLAUDE.md); read it first.
Five of them matter most.

1. Search before building: the declaration index, then `MathFin/`, then BrownianMotion, then Mathlib. Extend or instantiate what exists; never write a parallel object.
2. Claims never outrun the Lean: every docstring, corpus `description` and doc paragraph says no more than the statement proves.
3. The gates in `tests/` (router, ledger, values, architecture, ratchet, doc standard) must pass; they are run by CI before the Lean build.
4. The verification ledger records what each corpus entry last verified under; after any `MathFin/` or benchmark edit, run `python3 -m tools.verify.ledger status`.
5. Take no hard-to-reverse action (pushing, merging, deleting, force operations, spending shared compute) without the maintainer's say-so.

Lean runs are memory-heavy: one Lean-loaded process at a time, and Docker images are built by CI,
not locally; `CLAUDE.md` has the commands.
