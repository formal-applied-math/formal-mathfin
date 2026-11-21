# First contribution

This walkthrough takes one contribution from clone to merged pull request. It assumes you read
Lean 4 but not this codebase. Each step links to [CONTRIBUTING.md](../CONTRIBUTING.md) for the
rule it applies instead of repeating it. Terms such as corpus, frontier and ledger are in the
[glossary](glossary.md).

## 1. Pick a task

- Open issues labelled
  [`good first issue`](https://github.com/formal-applied-math/formal-mathfin/issues?q=is%3Aopen+label%3A%22good+first+issue%22).
  [`issue-labels.md`](issue-labels.md) explains the other labels.
- The [frontier](glossary.md#frontier): results stated on the blueprint and not yet formalized,
  listed in [`blueprint_frontier.toml`](blueprint_frontier.toml) and drawn on the
  [blueprint page](https://formal-applied-math.github.io/formal-mathfin/blueprint.html). Each node
  names the nodes it builds on and has an open issue.
- [`research-problems/`](research-problems/README.md): sourced open questions, some already
  stated in Lean.
- Documentation, tooling and test improvements need no Lean build.

Comment on the issue before you start. If your result is not on the blueprint, add a frontier
entry first (CONTRIBUTING, section 6).

## 2. Set up

Clone the repository, then pick one of two ways to work.

Plain `lake build` with elan is the simplest and matches CI. Install
[elan](https://github.com/leanprover/elan) and open the repository root in an editor with the Lean 4
extension; the toolchain is pinned by `lean-toolchain`.

```bash
lake exe cache get   # Mathlib's prebuilt oleans
lake build
```

The Docker image plus the persistent REPL daemon gives a fast edit-check loop. The daemon loads
Mathlib once and then checks a file in seconds, where a cold `lake build` of a changed
dependency chain takes minutes. Choose it when you iterate on many small edits or work without an
editor. The image is public:

```bash
docker compose -f docker/docker-compose.yml pull verify
```

Then, for either route, set up the merge driver and hook once per clone. The ledger merges through
a custom driver, and the hook blocks a push to main whose ledger is stale:

```bash
git config merge.mathfin-ledger.name "semantic merge for verification_ledger.json"
git config merge.mathfin-ledger.driver "python3 tools/verify/ledger_merge.py %O %A %B %L %P"
git config core.hooksPath .githooks
```

Run Python gates in Python 3.12 (`pip install -e ".[dev]"`) or inside the image. Run one
Lean-loaded process at a time; [troubleshooting](troubleshooting.md) covers memory problems.

## 3. Search before you write

Find what the library has (CONTRIBUTING, section 1):

```bash
python3 -m tools.verify.find --help          # where to get the declaration index
python3 -m tools.verify.find forward measure
```

Then read the module docstrings of the area you are entering. Extend or instantiate what exists.

## 4. Write the module

The layers and the one-home rule are in CONTRIBUTING, section 2. The tree:

```
MathFin/
  Probability/   Contracts/   Pricing/                      the roots, the payoffs, the pricing functional
  Models/   Risk/   Choice/   Insurance/   Markets/          the limbs
MathFinExamples/   worked demonstrations (Tour.lean first)
MathFinTest/       API checks
```

A module has this shape. `MathFin/Models/Binomial/Model.lean` is a full example; the docstring
sections are specified in CONTRIBUTING, section 4.

```lean
/-
Copyright (c) 2026 Your Name. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Your Name
-/
module

public import MathFin.Init
public import Mathlib.Algebra.CharP.Defs

/-!
# Title of the module

One paragraph saying what the module proves.

## Main definitions

* `myDef`: what it is.

## Main results

* `myTheorem`: what it states.

## References

* [A. Author, *Title*][Key], §1.2

## Tags

search terms, MSC 91G20, JEL G13
-/

@[expose] public section

/-- The main result. -/
theorem myTheorem ... := by
  ...
```

Import the library modules you build on instead of `public import MathFin.Init` alone. Add the
module to the umbrella `MathFin.lean`.

Check the file as you go. In the daemon route:

```bash
docker compose -f docker/docker-compose.yml up -d lean-repl
docker compose -f docker/docker-compose.yml logs lean-repl     # repeat until READY appears
./scripts/lean-check.sh MathFin/Models/Binomial/Model.lean     # JSON: success, errors, sorry_count
./scripts/bench-check.sh benchmarks/black_scholes.json mf-put-call-parity
docker compose -f docker/docker-compose.yml down lean-repl
```

With elan, `lake build MathFin.Models.Binomial.Model` builds one module. Finish with
`lake build && lake lint`; CI runs the linter, and a green build alone still fails on a missing
definition docstring.

## 5. Add the corpus entry

If the theorem belongs in the corpus, add an entry to the benchmark file for its area with an
honest `description` and `formalization_status` (CONTRIBUTING, section 5). Then:

```bash
python3 -m tools.verify.axiom_audit_gen --write
python3 -m tools.verify.ledger status
python3 -m tools.verify.ledger verify        # stale rows only; the daemon must be up
```

## 6. Run the gates

```bash
python3 -m pytest tests/ -q
```

The whole directory must pass. CONTRIBUTING, section 7, names what each main file enforces.
Read your docstrings and descriptions against your statements once more before you push.

## 7. Open the pull request

Use the template in `.github/PULL_REQUEST_TEMPLATE.md`. Put `Blueprint: <label>` on its own line
and tick what applies. If you add yourself under Contributors in `README.md` and name yourself in
your module headers, the attribution gate passes. CI runs the tests and `ledger status`, then the
Lean build, the declaration index and the ratchet checks; a maintainer reviews, and the pull
request is merged with a merge commit so your commits stay under your name.

## Getting help

Comment on the issue you are working on, or open a new one. [`patterns.md`](patterns.md) collects
the proof patterns used in the library, and [`troubleshooting.md`](troubleshooting.md) covers setup
failures.
