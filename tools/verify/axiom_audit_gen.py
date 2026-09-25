"""Generate ``MathFin/AxiomAuditGen.lean`` — the exhaustive axiom audit.

The curated ``MathFin/AxiomAudit.lean`` pins the *headliner* theorems with
dated, storied sections. This generator closes the complement: every constant
declared in ``MathFin/`` that a benchmark snippet's proof cites gets a
``#guard_msgs``-pinned ``#print axioms`` check, so no benchmark-cited theorem
can pick up ``sorryAx`` (a ``sorry``) or a non-standard axiom without
breaking ``lake build``.

Citations are resolved by declaration, not by spelling
(``tools/verify/mathfin_index.py``): a snippet may ``open MathFin`` and cite a
name unqualified, use dot notation on a typed hypothesis, or cite a theorem a
MathFin file declares in ``namespace ProbabilityTheory`` or
``namespace MeasureTheory``. Until 2026-09-25 this generator matched only the
spelling ``MathFin.…``, and five theorems cited by ``full`` entries escaped
both audit files.

Scope (documented, deliberate):

* *proof position*: identifiers in the proof bodies of a snippet, from each
  declaration's top-level ``:=`` to the next declaration. Statement-position
  defs are exercised by elaboration + the verification ledger; names that
  resolve to Mathlib or BrownianMotion are upstream's contract.
* expected messages default to the three standard axioms; results that need
  fewer are recorded in ``EXPECTED_OVERRIDES`` (built empirically from build
  output — the build is the oracle).

Usage::

    python3 -m tools.verify.axiom_audit_gen --check   # exit 1 if stale
    python3 -m tools.verify.axiom_audit_gen --write   # regenerate in place

Freshness is enforced by ``tests/test_values.py::test_axiom_audit_gen_is_fresh``
(the blueprint anti-restale pattern: generated artifacts are never hand-edited
and regeneration must be a no-op).
"""

from __future__ import annotations

import sys
from pathlib import Path

from tools.verify.corpus import iter_entries
from tools.verify.mathfin_index import cited_constants, declaration_index

GEN_PATH = Path("MathFin/AxiomAuditGen.lean")
GEN_NAMESPACE = "MathFin.AxiomAuditGen"

STANDARD_AXIOMS = "[propext, Classical.choice, Quot.sound]"

# name -> full #guard_msgs doc-comment body, for results whose axiom set is a
# strict subset of the standard three (pure-algebra theorems). Populated from
# build output; the build is the oracle for these strings.
EXPECTED_OVERRIDES: dict[str, str] = {}


def collect_proof_position_names() -> list[str]:
    index = declaration_index()
    names: set[str] = set()
    for _path, theorem in iter_entries():
        names |= cited_constants(theorem.get("code", {}).get("lean", ""), index)
    _check_unambiguous(names, index)
    return sorted(names)


def _check_unambiguous(names: set[str], index) -> None:
    """`#print axioms N` runs inside `namespace MathFin.AxiomAuditGen`, where Lean
    tries `MathFin.AxiomAuditGen.N` and `MathFin.N` before `N`. A name outside
    `MathFin` (say `MeasureTheory.maximal_ineq_Lp`) would silently print a
    different constant if MathFin declared the same name under its namespace."""
    parts = GEN_NAMESPACE.split(".")
    prefixes = [".".join(parts[:k]) for k in range(len(parts), 0, -1)]
    shadowed = sorted(f"{name} (shadowed by {p}.{name})" for name in names
                      for p in prefixes if f"{p}.{name}" in index)
    if shadowed:
        raise SystemExit("ambiguous #print axioms targets: " + ", ".join(shadowed))


def _guard_block(name: str) -> str:
    info = EXPECTED_OVERRIDES.get(
        name, f"info: '{name}' depends on axioms: {STANDARD_AXIOMS}"
    )
    return (
        f"/-- {info} -/\n"
        f"#guard_msgs (whitespace := lax) in #print axioms {name}\n"
    )


def generate() -> str:
    names = collect_proof_position_names()
    header = f"""/-
  GENERATED FILE — do not edit by hand.

  Exhaustive axiom audit: every constant declared in MathFin/ that a benchmark
  snippet's proof cites is #guard_msgs-pinned to its exact axiom set, so no
  benchmark-cited theorem can pick up `sorryAx` (a `sorry`) or a non-standard
  axiom without breaking `lake build`.

  The curated, storied audit is MathFin/AxiomAudit.lean (headliners + dated
  narrative); THIS file is its machine-written closure over the benchmark
  corpus ({len(names)} constants). Citations are resolved by declaration
  (tools/verify/mathfin_index.py), so a name cited unqualified under `open`,
  by dot notation on a hypothesis, or declared outside the MathFin namespace
  is pinned like any other. Statement-position defs are exercised by
  elaboration + the verification ledger, and upstream names are upstream's.

  Regenerate:  python3 -m tools.verify.axiom_audit_gen --write
  Freshness:   tests/test_values.py::test_axiom_audit_gen_is_fresh
  (Excluded from CI kernel replay like AxiomAudit: whole-library closure.)
-/
import MathFin

namespace {GEN_NAMESPACE}

"""
    body = "\n".join(_guard_block(name) for name in names)
    return header + body + f"\nend {GEN_NAMESPACE}\n"


def main(argv: list[str]) -> int:
    mode = argv[0] if argv else "--check"
    content = generate()
    if mode == "--write":
        GEN_PATH.write_text(content)
        print(f"wrote {GEN_PATH} ({len(collect_proof_position_names())} guards)")
        return 0
    if mode == "--check":
        on_disk = GEN_PATH.read_text() if GEN_PATH.exists() else ""
        if on_disk != content:
            print(f"STALE: {GEN_PATH} does not match the generator output; "
                  "run `python3 -m tools.verify.axiom_audit_gen --write`")
            return 1
        print(f"fresh: {GEN_PATH}")
        return 0
    print(__doc__)
    return 2


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
