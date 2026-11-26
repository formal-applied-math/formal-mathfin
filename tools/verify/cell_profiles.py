"""Each taxonomy cell described in the library's own words, and the sources the library cites in it.

    python3 -m tools.verify.cell_profiles --out <profiles.json>

The literature atlas (`docs/specs/2026-11-25-literature-atlas-design.md`) classifies the papers of
a local corpus into the cells of `docs/taxonomy.toml`. This is the library's half: for every cell,
its title and blurb, the docstrings of the modules in it, the descriptions of the corpus entries
placed in it, and the names of the JEL and MSC codes its modules carry. Those make up the profile
a paper's abstract is scored against, whole (`profile`) and piece by piece (`pieces`, one per
module docstring and per entry description, each with its cell). It also lists every bibliography entry with the cells of the
modules and entries that cite it. A cited paper found in the corpus has a known cell, and those
papers are the classifier's ground truth.

Nothing here reads the corpus. The output is derived from the tree and is not committed.
"""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

from . import doc_standard, hf_dataset, library, taxonomy


def _module_docs() -> dict[str, doc_standard.ModuleDoc]:
    docs = {}
    for path in library.modules():
        doc = doc_standard.module_doc(path)
        if doc:
            docs[library.module_name(path)] = doc
    return docs


def _plain(text: str) -> str:
    """Docstring prose without Lean code, links or reference keys."""
    text = re.sub(r"`[^`]*`", " ", text)
    text = re.sub(r"\[([^\]]*)\]\[[^\]]*\]", r"\1", text)
    text = re.sub(r"\[([^\]]*)\]\([^)]*\)", r"\1", text)
    return " ".join(text.split())


def profiles() -> dict:
    cells = {c["key"]: {"title": c["title"], "blurb": c.get("blurb", ""), "modules": [],
                        "subjects": set(), "text": []}
             for c in taxonomy.load()["cell"]}
    names = doc_standard.subject_names()
    cited: dict[str, set[str]] = {}
    pieces: list[dict] = []
    for module, doc in _module_docs().items():
        cell = taxonomy.cell_of(module)
        if cell not in cells:
            continue
        c = cells[cell]
        c["modules"].append(module)
        c["subjects"].update(doc.subjects)
        body = " ".join(b for h, b in doc.sections if h not in ("References", "Tags"))
        c["text"].append(_plain(f"{doc.title or ''}. {body}"))
        pieces.append({"cell": cell, "kind": "module", "id": module, "text": c["text"][-1]})
        c["text"].extend(t for t in doc.tags if not t.startswith(("JEL ", "MSC ")))
        for key in doc.citations:
            cited.setdefault(key, set()).add(cell)
    for row in hf_dataset.build_rows():
        cell = row["cell"]
        if cell in cells:
            cells[cell]["text"].append(_plain(f"{row['name']}. {row['description']}"))
            pieces.append({"cell": cell, "kind": "entry", "id": row["id"],
                           "text": cells[cell]["text"][-1]})
            for c in row["citations"]:
                cited.setdefault(c["key"], set()).add(cell)
    bib = doc_standard.bib_entries()
    out_cells = {}
    for key, c in cells.items():
        subj = sorted(c["subjects"])
        out_cells[key] = {
            "title": c["title"], "blurb": c["blurb"], "modules": sorted(c["modules"]),
            "subjects": subj,
            "profile": " ".join([c["title"], c["blurb"], *(names.get(s, "") for s in subj),
                                 *c["text"]])}
    sources = [{"key": k, "kind": f.get("kind"), "title": f.get("title"),
                "author": f.get("author"), "year": f.get("year"), "doi": f.get("doi"),
                "eprint": f.get("eprint"), "cells": sorted(cited.get(k, ()))}
               for k, f in sorted(bib.items())]
    return {"cells": out_cells, "sources": sources, "pieces": pieces}


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(prog="cell_profiles")
    ap.add_argument("--out", type=Path, required=True)
    args = ap.parse_args(argv)
    data = profiles()
    args.out.write_text(json.dumps(data, ensure_ascii=False, indent=1), encoding="utf-8")
    empty = [k for k, c in data["cells"].items() if not c["modules"]]
    print(json.dumps({"cells": len(data["cells"]), "cells without modules": empty,
                      "sources": len(data["sources"]),
                      "sources with a cell": sum(bool(s["cells"]) for s in data["sources"])}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
