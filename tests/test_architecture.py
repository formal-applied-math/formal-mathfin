"""Architecture gates: every module is part of the library's graph.

The values gates (``test_values.py``) are keyed to the benchmark corpus: they audit what the
corpus cites. On 2026-10-21 a coherence pass found that growth had started to go around the
corpus. A batch of 42 modules came with 7 corpus entries; 38 of the modules were cited by no
entry, and 15 of them imported nothing from the library and were imported by nothing. They
were honest, but the honesty gates could not see them, and they did not connect to anything.
The repair was to build the missing bridges, not to fence the modules off. These tests keep
the library one graph:

* ``test_foundations_imports_only_foundations``: ``Foundations/`` is the layer the pricing
  sections stand on, so it imports nothing above it. A model lives in its market's section;
  a module that joins a foundation to a model lives in ``Bridges/``.
* ``test_every_module_is_connected``: every module has an edge in the import graph. It
  imports a library module, or a library module imports it.
* ``test_every_module_is_used``: every module is imported by another library module or by a
  corpus entry. A result that nothing uses and nothing cites is a claim nobody checks.
* ``test_every_module_reaches_init``: ``MathFin/Init.lean`` holds the library's conventions
  (its attributes, the ``pricing`` grind set), and every module sees it: a module importing no
  library module imports it directly (CSLib's ``Cslib.Init``). An edge to ``Init`` connects a
  module to nothing, so the two tests above do not count it.
* ``test_notation_is_scoped``: notation is ``scoped`` or ``local``, never global
  (``docs/design.md`` §5).

``STAGING`` admits a module whose consumer is being built in an open issue. It names the
issue, and it is meant to stay short-lived. It is not a place to park a module that does
not connect: that module needs a bridge.
"""

from __future__ import annotations

import re

from tools.verify import library
from tools.verify.corpus import iter_entries
from tools.verify.library import INIT

NOTATION_RE = re.compile(r"^[ \t]*(?:@\[[^\]]*\][ \t]*)?(?:(scoped|local)[ \t]+)?"
                         r"(?:notation|infixl|infixr|infix|prefix|postfix)\b[ \t]*[\"(:]", re.M)

# module -> open issue whose work adds its consumer. Keep it short-lived.
STAGING: dict[str, str] = {}


def _all_modules() -> dict[str, list[str]]:
    """Every library module (aggregators, `Init` and the umbrella `MathFin` included) and its
    library imports."""
    paths = [library.UMBRELLA] + library.modules(aggregators=True)
    return {library.module_name(p): library.library_imports(p.read_text(encoding="utf-8"))
            for p in paths}


def _modules() -> dict[str, list[str]]:
    """The library's graph: aggregators (`library.AGGREGATORS`) and `Init` are not nodes, and
    edges to `Init` are dropped."""
    graph = _all_modules()
    return {m: [i for i in imps if i != INIT] for m, imps in graph.items()
            if m not in library.AGGREGATORS and m not in {INIT, "MathFin"}}


def _importers(mods: dict[str, list[str]]) -> dict[str, set[str]]:
    importers: dict[str, set[str]] = {m: set() for m in mods}
    for m, imps in mods.items():
        for i in imps:
            if i in importers:
                importers[i].add(m)
    return importers


def _cited_by_corpus() -> set[str]:
    cited = set()
    for _, entry in iter_entries():
        cited.update(library.library_imports(entry["code"]["lean"]))
    return cited


def test_foundations_imports_only_foundations() -> None:
    bad = {
        m: [i for i in imps if not i.startswith("MathFin.Foundations.")]
        for m, imps in _modules().items()
        if m.startswith("MathFin.Foundations.")
    }  # `_modules` has dropped the edges to `Init`, which every layer imports
    bad = {m: v for m, v in bad.items() if v}
    assert not bad, (
        "Foundations/ imports only Foundations/. Move the module to the section of the model "
        "it uses, or to Bridges/ if it joins a foundation to a model:\n"
        + "\n".join(f"  {m} imports {', '.join(v)}" for m, v in sorted(bad.items()))
    )


def test_every_module_is_connected() -> None:
    mods = _modules()
    importers = _importers(mods)
    islands = sorted(
        m for m, imps in mods.items()
        if m not in STAGING and not any(i in mods for i in imps) and not importers[m]
    )
    assert not islands, (
        "these modules import no library module and no library module imports them. Build "
        "the bridge: a proved lemma tying the module's objects to the library's (one normal "
        "law, `valueAtRisk`, `bsV`, the numéraire, the bond lemma, ...), placed so that one "
        "module imports the other:\n  " + "\n  ".join(islands)
    )


def test_every_module_is_used() -> None:
    mods = _modules()
    importers = _importers(mods)
    cited = _cited_by_corpus()
    unused = sorted(m for m in mods if m not in STAGING and not importers[m] and m not in cited)
    assert not unused, (
        "nothing imports these modules and no corpus entry cites them. Give the headline "
        "result a corpus entry, or let the module that needs it import it:\n  "
        + "\n  ".join(unused)
    )


def test_every_module_reaches_init() -> None:
    mods = _all_modules()
    reach: dict[str, bool] = {INIT: True}

    def sees_init(m: str) -> bool:  # the import graph is acyclic
        if m not in reach:
            reach[m] = any(sees_init(i) for i in mods.get(m, ()))
        return reach[m]

    blind = sorted(m for m in mods if m != INIT and not sees_init(m))
    assert not blind, (
        "these modules do not import `MathFin.Init`, directly or through another library "
        "module. A module that imports no library module starts with "
        "`public import MathFin.Init`:\n  " + "\n  ".join(blind))


def test_notation_is_scoped() -> None:
    from tools.verify.mathfin_index import strip_comments

    glob = sorted(f"{p}:{m.group(0).strip()}" for p in library.modules(aggregators=True)
                  for m in NOTATION_RE.finditer(strip_comments(p.read_text(encoding="utf-8")))
                  if not m.group(1))
    assert not glob, (
        "global notation: make it `scoped` in the namespace of the object it writes, or "
        "`local` (docs/design.md §5):\n  " + "\n  ".join(glob))


def test_staging_entries_name_an_issue_and_exist() -> None:
    mods = _modules()
    for m, issue in STAGING.items():
        assert m in mods, f"STAGING lists {m}, which no longer exists"
        assert re.search(r"/issues/\d+$", issue), f"STAGING entry {m} must name an issue URL"
