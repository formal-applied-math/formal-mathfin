"""The literature atlas: the field's map of each taxonomy cell beside the library's own.

`docs/atlas.json` is the field side, written by the private corpus tools (`mathfin-corpus`,
`mathfin_corpus/field.py`) and committed by hand when the corpus is refreshed. For each cell it
has the number of corpus papers, their growth, the citations they receive inside the corpus, the
ten works they cite most (bibliographic metadata only), and how well the classifier that placed
the papers agrees with its labels in that cell. The design is
`docs/specs/2026-11-25-literature-atlas-design.md`.

The library side is not in the file. `literature` reads it from what the build records, so it is
never stale: the corpus entries in each cell (`program_tree.place_corpus`), its proved and frontier
blueprint nodes, and its modules (`taxonomy.cell_of`). The docs site's program tree draws the join
as its Literature layer.

A cell's **gap** is its share of the field's papers minus its share of the library's corpus
entries, in percentage points. A large gap marks a roadmap candidate, not a verdict: a cell can be
dense with empirical work the library does not set out to formalise.
"""

from __future__ import annotations

import json
from collections import Counter
from pathlib import Path

ATLAS = Path("docs/atlas.json")
AGREEMENT_BAR = 0.7  # the spec's bar; a cell under it carries a warning


def load(path: Path = ATLAS) -> dict | None:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else None


def literature(atlas: dict, entries: Counter, proved: Counter, frontier: Counter,
               modules: Counter) -> dict:
    """Per cell of `atlas`, the field's numbers beside the library's counts and the gap."""
    cells = atlas["cells"]
    papers = sum(c["papers"] for c in cells.values()) or 1
    total = sum(entries[k] for k in cells) or 1
    out = {}
    for k, c in cells.items():
        field_share = c["papers"] / papers
        lib_share = entries[k] / total
        a = c.get("agreement") or {}
        out[k] = {"papers": c["papers"], "growth": c.get("growth"),
                  "cited": c.get("cited_in_corpus", 0),
                  "field": round(100 * field_share, 1), "library": round(100 * lib_share, 1),
                  "gap": round(100 * (field_share - lib_share), 1),
                  "entries": entries[k], "proved": proved[k], "frontier": frontier[k],
                  "modules": modules[k], "recall": a.get("recall"),
                  "warn": a.get("recall") is None or a["recall"] < AGREEMENT_BAR,
                  "founding": [{x: f.get(x) for x in ("title", "year", "doi", "authors",
                                                      "cited_by_cell")}
                               for f in c.get("founding", [])]}
    return out


def largest_gaps(lit: dict, n: int = 3) -> list[str]:
    return sorted(lit, key=lambda k: -lit[k]["gap"])[:n]
