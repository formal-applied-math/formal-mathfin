/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
import MathFin
import MathFinFrontier.MarketValuation
import MathFinFrontier.ModelFree
import MathFinFrontier.Microstructure
import MathFinFrontier.Credit
import MathFinFrontier.Insurance
import MathFinFrontier.American
import MathFinFrontier.Rates

/-!
# Connectors: the bridges the library does not prove yet, stated exactly

A **connector** is a theorem that would join a part of the library to the rest of it (a model
family to the market, a limb to the trunk, a tower to its summit) and has not been proved. It is
stated here, as Lean, closed by `sorry`. Since the statement elaborates, both sides name real
declarations and the types fit: a missing link cannot be vague and cannot point at nothing
(docs/specs/2026-11-08-chain-design.md §3.5).

This library is apart from the proofs. `MathFin` never imports it, the axiom audits do not see
it, and `tests/test_values.py` keeps `MathFin/` free of `sorry` as before. It is a default build
target, like `Challenge`, so a plain `lake build` checks that every connector still elaborates
against the library, and prints one `declaration uses 'sorry'` warning per connector, which is
the list of what is open.

Each connector is a theorem in `MathFinFrontier/`, named by exactly one frontier node of
`docs/blueprint_frontier.toml` (its `lean` field), and that node is carried by an open issue. The
index of this library (`lake exe mathfin_index frontier-index.json 1 MathFinFrontier`) is what
`tools/verify/chain_reach.py` reads to say how much each connector would chain, and what the
program tree reads to draw it as a phantom between the parts it joins.

Delivering a connector moves the statement into `MathFin/`, proves it, tags it in
`MathFin/Blueprint.lean` under the same label, and deletes it here and from the frontier file.
-/
