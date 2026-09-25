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
  defs are exercised by elaboration + the verification ledger.
* upstream constants (Mathlib, BrownianMotion) are pinned when a
  ``library_wrapper`` entry's proof cites them, from the explicit list
  ``UPSTREAM_CITATIONS``. Those entries count as delivered, and BrownianMotion
  at the current pin has ``sorry``s of its own, so "upstream's contract" is not
  enough for them. Upstream names inside other entries' proofs are not pinned.
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

import re
import sys
from pathlib import Path

from tools.verify.corpus import iter_entries
from tools.verify.mathfin_index import cited_constants, declaration_index, strip_comments

GEN_PATH = Path("MathFin/AxiomAuditGen.lean")
GEN_NAMESPACE = "MathFin.AxiomAuditGen"

STANDARD_AXIOMS = "[propext, Classical.choice, Quot.sound]"

# name -> full #guard_msgs doc-comment body, for results whose axiom set is a
# strict subset of the standard three (pure-algebra theorems). Populated from
# build output; the build is the oracle for these strings. The five below are
# upstream constants cited by library_wrapper entries (build.yml run
# 36151826318, 2026-09-25).
EXPECTED_OVERRIDES: dict[str, str] = {
    "Eq.symm": "info: 'Eq.symm' does not depend on any axioms",
    "LT.lt.ne'": "info: 'LT.lt.ne'' does not depend on any axioms",
    "Pi.add_apply": "info: 'Pi.add_apply' does not depend on any axioms",
    "inferInstance": "info: 'inferInstance' does not depend on any axioms",
    "min_eq_left": "info: 'min_eq_left' depends on axioms: [propext]",
}

# The upstream constants each `library_wrapper` entry's proof cites, fully
# qualified, including lemmas reached by dot notation (`hf.smul` is
# `MeasureTheory.Integrable.smul`). `mathfin_index` resolves only MathFin
# declarations, so this list is kept by hand. The names were checked against
# the pinned sources on 2026-09-25 (Mathlib 0434c033, BrownianMotion 314f04a).
# `test_library_wrapper_citations_are_pinned` fails if an entry is missing, a
# name no longer appears in its proof, or a name is not pinned.
UPSTREAM_CITATIONS: dict[str, tuple[str, ...]] = {
    "bm-prop-5.1.2": ("ProbabilityTheory.IsGaussianProcess.isPreBrownianReal_of_covariance",
                      "min_eq_left"),
    "bm-thm-5.1.5": ("ProbabilityTheory.IsPreBrownianReal.isMartingale",),        # BrownianMotion
    "bm-thm-5.3.2": ("ProbabilityTheory.IsPreBrownianReal.memHolder_mk",),        # BrownianMotion
    "ce-prop-2.1.11-independence": ("MeasureTheory.condExp_indep_eq",),
    "ce-prop-2.1.11-jensen": ("ConvexOn.map_condExp_le_of_finiteDimensional",
                              "MeasureTheory.Measure.trim",
                              "MeasureTheory.SigmaFinite",
                              "inferInstance"),
    "ce-prop-2.1.11-pull-out": ("MeasureTheory.condExp_mul_of_stronglyMeasurable_left",),
    "ce-prop-2.1.11-tower": ("MeasureTheory.condExp_condExp_of_le",),
    "ce-prop-2.1.5-linearity": ("MeasureTheory.condExp_add",
                                "MeasureTheory.condExp_smul",
                                "MeasureTheory.Integrable.smul",
                                "Pi.add_apply"),
    "cm-thm-4.3.7": ("MeasureTheory.Martingale.stoppedProcess_indicator",),       # BrownianMotion
    "cm-thm-4.3.9": ("ProbabilityTheory.maximal_ineq_nonneg",),                   # BrownianMotion
    "cv-cond-exp-tower": ("MeasureTheory.condExp_condExp_of_le",),
    "cv-prob-space": ("MeasureTheory.IsProbabilityMeasure.measure_univ",
                      "MeasureTheory.measure_empty"),
    "dist-thm-B.1.2-affine": ("ProbabilityTheory.gaussianReal_add_const",
                              "ProbabilityTheory.gaussianReal_const_mul"),
    "dist-thm-B.1.2-marginal": ("MeasureTheory.MeasurePreserving.map_eq",
                                "ProbabilityTheory.measurePreserving_eval_multivariateGaussian"),
    "mart-prop-2.5.5": (
        "MeasureTheory.Submartingale.mul_integral_upcrossingsBefore_le_integral_pos_part",),
    "mart-thm-2.4.3": ("MeasureTheory.maximal_ineq",),
    "mart-thm-2.5.3": ("MeasureTheory.Submartingale.ae_tendsto_limitProcess",),
    "mf-carr-madan-log": ("Eq.symm", "LT.lt.ne'", "Real.log_div"),
}

_IMPORT_RE = re.compile(r"(?m)^import\s+(\S+)")


def collect_proof_position_names() -> list[str]:
    index = declaration_index()
    names: set[str] = set()
    for _path, theorem in iter_entries():
        names |= cited_constants(theorem.get("code", {}).get("lean", ""), index)
    _check_unambiguous(names, index)
    return sorted(names)


def collect_upstream_names() -> list[str]:
    names = {name for cited in UPSTREAM_CITATIONS.values() for name in cited}
    _check_unambiguous(names, declaration_index())
    return sorted(names)


def upstream_imports() -> list[str]:
    """The non-MathFin modules the `library_wrapper` snippets import. `import
    MathFin` brings in all of Mathlib, but not every BrownianMotion module."""
    modules: set[str] = set()
    for _path, theorem in iter_entries():
        if theorem.get("metadata", {}).get("formalization_status") != "library_wrapper":
            continue
        code = strip_comments(theorem.get("code", {}).get("lean", ""))
        modules |= {m for m in _IMPORT_RE.findall(code)
                    if m != "Mathlib" and not m.startswith("MathFin")}
    return sorted(modules)


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
    upstream = collect_upstream_names()
    imports = "".join(f"import {m}\n" for m in ["MathFin", *upstream_imports()])
    header = f"""/-
  GENERATED FILE — do not edit by hand.

  Exhaustive axiom audit: every constant declared in MathFin/ that a benchmark
  snippet's proof cites is #guard_msgs-pinned to its exact axiom set, so no
  benchmark-cited theorem can pick up `sorryAx` (a `sorry`) or a non-standard
  axiom without breaking `lake build`.

  The curated, storied audit is MathFin/AxiomAudit.lean (headliners + dated
  narrative); THIS file is its machine-written closure over the benchmark
  corpus ({len(names)} MathFin constants, {len(upstream)} upstream). Citations
  are resolved by declaration (tools/verify/mathfin_index.py), so a name cited
  unqualified under `open`, by dot notation on a hypothesis, or declared
  outside the MathFin namespace is pinned like any other. Statement-position
  defs are exercised by elaboration + the verification ledger. The second
  section pins the Mathlib and BrownianMotion constants that library_wrapper
  entries cite (UPSTREAM_CITATIONS in the generator).

  Regenerate:  python3 -m tools.verify.axiom_audit_gen --write
  Freshness:   tests/test_values.py::test_axiom_audit_gen_is_fresh
  (Excluded from CI kernel replay like AxiomAudit: whole-library closure.)
-/
{imports}
namespace {GEN_NAMESPACE}

"""
    body = "\n".join(_guard_block(name) for name in names)
    upstream_section = """
/-! ## Upstream constants cited by `library_wrapper` entries

A `library_wrapper` entry re-exports a Mathlib or BrownianMotion theorem, and it
counts as delivered. BrownianMotion at the current pin has `sorry`s of its own,
so these are pinned here rather than left to upstream. -/

""" + "\n".join(_guard_block(name) for name in upstream)
    return header + body + upstream_section + f"\nend {GEN_NAMESPACE}\n"


def main(argv: list[str]) -> int:
    mode = argv[0] if argv else "--check"
    content = generate()
    if mode == "--write":
        GEN_PATH.write_text(content)
        count = len(collect_proof_position_names()) + len(collect_upstream_names())
        print(f"wrote {GEN_PATH} ({count} guards)")
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
