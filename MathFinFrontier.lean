/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import MathFin

/-!
# MathFinFrontier: Lean statements of frontier results and open problems

This library holds Lean statements, each closed by `sorry`, of two kinds of result that the
`MathFin` library has not proved. A statement either completes the blueprint (a
[frontier](docs/glossary.md#frontier) node of `docs/blueprint_frontier.toml` that joins a part
of the library to the rest of it: a model family to the market, a limb to the trunk, a tower to
its summit) or is an open problem of the field recorded in `docs/research-problems/problems.json`
(`MF-OP-NNN`). Because a statement elaborates, both sides of it name real declarations and the
types fit: a missing link cannot be vague and cannot point at nothing
(`docs/specs/2026-11-08-chain-design.md` §3.5). The older name for a statement of the first kind
is a frontier connector (see the glossary).

`MathFin` never imports this library, the axiom audits do not see it, and `tests/test_values.py`
keeps `MathFin/` free of `sorry`. It is a default `lean_lib` target of `lakefile.lean`, like
`Challenge`, so a plain `lake build` checks that every statement still elaborates against the
library and prints one `declaration uses 'sorry'` warning per statement, which is the list of what
is open.

Each statement is a theorem in `MathFinFrontier/`, named by exactly one frontier node (its `lean`
field), and that node is carried by an open issue. A statement of an open problem is also named by
the `lean` field of its record's `formalization.lean_statement`. The index of this library
(`lake exe mathfin_index frontier-index.json 1 MathFinFrontier`) is what
`tools/verify/chain_reach.py` reads to say how much each statement would chain, and what the
program tree reads to draw it as a phantom between the parts it joins.

Delivering a statement moves it into `MathFin/`, proves it, tags it in `MathFin/Blueprint.lean`
under the same label, and deletes it here and from the frontier file. The catalogue record, if
there is one, becomes `solved`.

## References

* [Research problems](docs/research-problems/README.md): which artefact owns what, how a
  problem is admitted, and how a solution is recorded.
* [Blueprint](docs/blueprint.md): the nodes the statements attach to.
* [Glossary](docs/glossary.md).
-/
