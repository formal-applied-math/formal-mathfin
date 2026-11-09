"""Build the Hugging Face dataset files from the benchmark corpus.

Vendored (and made count-honest) from the original one-off
``build_dataset.py`` that published
https://huggingface.co/datasets/formal-applied-math/formal-mathfin-theorems —
this repo is the single source of truth; CI (`hf-publish.yml`) rebuilds and
uploads on every push that touches ``benchmarks/``. The dataset card's
counts are COMPUTED here at build time (the originally-published card had
already rotted to a 261-theorem snapshot — generated artifacts, never
hand-maintained).

Emits into ``--out DIR``:

* ``formal-mathfin-theorems.jsonl`` — one row per theorem: id, name, domain,
  formalization_status, description, formalization_scope, lean_code,
  source_file, subjects, cell, family, reference, citations.

  ``formalization_scope`` was added 2026-08-07. It had existed on every entry
  and been withheld from the export, so the *claim* (``description``) shipped
  while the *disclosure* stayed private — which is exactly the asymmetry that
  let 15 of 36 textbook-framed descriptions drift into claiming more than their
  Lean proved. Publish both or neither.

  ``subjects`` (2026-11-06) are the JEL/MSC codes of the ``## Tags`` sections of the
  MathFin modules the snippet imports, from the controlled vocabulary
  ``docs/subjects.toml`` (``tools/verify/doc_standard.py``).

  ``cell`` and ``family`` (2026-11-08) place the entry in the library's organization
  (``docs/organization.md``): the cell and model family of the MathFin modules the snippet
  imports, read from ``docs/taxonomy.toml``.

  ``reference`` and ``citations`` (2026-11-06): the entry's source as its author wrote it, and
  the works it names resolved against ``docs/references.bib``, the bibliography the library's
  module docstrings cite from too (key, locator, author, title, year).
* ``README.md`` — the dataset card, counts and toolchain pin computed.

Pure stdlib; safe on the host.

Usage::

    python3 -m tools.verify.hf_dataset --out dist/hf
"""

from __future__ import annotations

import argparse
import json
from collections import Counter
from functools import cache
from pathlib import Path

from tools.verify import doc_standard, library, taxonomy
from tools.verify.corpus import iter_entries

DATASET_FILE = "formal-mathfin-theorems.jsonl"



@cache
def _module_subjects(module: str) -> tuple[str, ...]:
    path = library.module_path(module)
    doc = doc_standard.module_doc(path) if path.exists() else None
    return tuple(doc.subjects) if doc else ()


def subjects(lean: str | None) -> list[str]:
    """The subject codes of the MathFin modules a snippet imports directly."""
    return sorted({c for m in library.library_imports(lean or "") for c in _module_subjects(m)})


@cache
def _bibliography() -> dict[str, dict[str, str]]:
    return doc_standard.bib_entries()


def citations(cites: list[dict]) -> list[dict]:
    """An entry's `metadata.citations`, each resolved to its bibliography fields."""
    bib = _bibliography()
    return [{"key": c["key"], "locator": c.get("locator", ""),
             **{f: bib.get(c["key"], {}).get(f, "") for f in ("author", "title", "year")}}
            for c in cites]


def entry_place(t: dict) -> tuple[str, str | None]:
    """An entry's (cell, family): its `metadata.cell`/`family` when it states them, else the
    place of the MathFin modules its snippet imports. A snippet citing only Mathlib or
    BrownianMotion is a probability tool."""
    meta = t.get("metadata") or {}
    code = t.get("code") or {}
    lean = code.get("lean") if isinstance(code, dict) else None
    cell, family = taxonomy.place_of(library.library_imports(lean or ""))
    return meta.get("cell", cell or "probability"), meta.get("family", family)


def build_rows() -> list[dict]:
    rows = []
    for path, t in iter_entries():
        code = t.get("code") or {}
        rows.append({
            "id": t.get("id"),
            "name": t.get("name"),
            "domain": t.get("domain"),
            "formalization_status":
                (t.get("metadata") or {}).get("formalization_status"),
            "description": t.get("description", ""),
            "formalization_scope":
                (t.get("metadata") or {}).get("formalization_scope", ""),
            "lean_code": code.get("lean") if isinstance(code, dict) else None,
            "source_file": path.name,
            "subjects": subjects(code.get("lean") if isinstance(code, dict) else None),
            **dict(zip(("cell", "family"), entry_place(t))),
            "reference": (t.get("metadata") or {}).get("reference", ""),
            "citations": citations((t.get("metadata") or {}).get("citations", [])),
        })
    return rows


def _toolchain() -> str:
    raw = Path("lean-toolchain").read_text().strip()
    return raw.split(":", 1)[1] if ":" in raw else raw


def render_card(rows: list[dict]) -> str:
    counts = Counter(r["formalization_status"] for r in rows)
    full = counts.get("full", 0)
    wrap = counts.get("library_wrapper", 0)
    reduced = counts.get("reduced_core", 0)
    total = len(rows)
    ready = full + wrap
    return f"""---
license: apache-2.0
task_categories:
  - other
language:
  - en
tags:
  - lean4
  - theorem-proving
  - autoformalization
  - formal-verification
  - mathematical-finance
  - quantitative-finance
pretty_name: Formally Verified Mathematical Finance (Lean 4)
size_categories:
  - n<1K
configs:
  - config_name: default
    data_files: {DATASET_FILE}
---

# Formally Verified Mathematical Finance (Lean 4)

This dataset comprises {total} machine-checked theorems in mathematical
finance, formalized using Lean 4 atop Mathlib and Rémy Degenne's
BrownianMotion package. Each entry includes a theorem's formal statement,
its proof, subject area, and a "faithfulness tier" indicating alignment
between the mathematical and formal claims.

Sourced from the [`formal-mathfin`](https://github.com/formal-applied-math/formal-mathfin)
library, this collection serves as training and evaluation material for
autoformalization and automated theorem proving focused on quantitative
finance — a domain underrepresented in existing mathematical benchmarks.

## Data Structure

The dataset provides these fields for each theorem:

- **id**: theorem identifier
- **name**: human-readable title
- **domain**: subject classification
- **formalization_status**: faithfulness category
- **description**: the theorem **as this entry proves it**. Where an entry
  delivers less than the source theorem it is named after, the description says
  so — it describes the Lean, not the textbook target. The citation for the
  target is in the source text referenced by `id`.
- **formalization_scope**: per-entry disclosure — what was derived, from which
  primitives, by what method, and what is explicitly out of scope
- **lean_code**: compilable Lean 4 implementation
- **source_file**: benchmark origin
- **subjects**: JEL and MSC2020 codes (`JEL G13`, `MSC 91G20`) of the library modules the
  entry imports, from their documentation's `Tags`; empty where those modules carry none yet
- **cell**: where the entry sits in the library's organization: a tool (`probability/...`,
  `statistics`), the trunk (`market`), or a branch of one of the three questions
  (`valuation/...`, `choice/...`, `risk/...`); see `docs/organization.md` in the repository
- **family**: the model family the entry is about (`trees`, `diffusions`, `volatility`, `jumps`,
  `term`, `default`, `insurance`, `mechanisms`, `model-free`), or null for general theory
- **reference**: the source the entry formalizes, as written
- **citations**: the works `reference` names, as `key`, `locator`, `author`, `title`, `year`,
  from the same bibliography the library's module docstrings cite (`docs/references.bib`)

## Faithfulness Classifications

Results are categorized by how faithfully the formal statement captures the
mathematical claim: "full" ({full} theorems), "library_wrapper" ({wrap}),
and "reduced_core" ({reduced}). The first two categories comprise the
delivery-ready collection ({ready} of {total}).

## Dependencies

Compilation requires Lean {_toolchain()}, specific Mathlib and
BrownianMotion commits, accessible via the reproducible Docker image — see
the source repository for pins and instructions.

## Attribution

Licensed under Apache-2.0. Users should cite the underlying library
(DOI: 10.5281/zenodo.20477781, which resolves to the latest release) and associated paper
([arXiv:2606.01356](https://arxiv.org/abs/2606.01356)).

*(This card and the data file are regenerated by the source repository's CI
on every push that changes the benchmark corpus — counts are computed, not
hand-maintained.)*
"""


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", default="dist/hf", help="output directory")
    args = parser.parse_args()

    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    rows = build_rows()

    with (out / DATASET_FILE).open("w", encoding="utf-8") as f:
        for r in rows:
            f.write(json.dumps(r, ensure_ascii=False) + "\n")
    (out / "README.md").write_text(render_card(rows), encoding="utf-8")

    counts = dict(Counter(r["formalization_status"] for r in rows))
    missing = [r["id"] for r in rows if not r["lean_code"]]
    print(f"wrote {len(rows)} rows -> {out / DATASET_FILE}")
    print(f"wrote dataset card -> {out / 'README.md'}")
    print("by formalization_status:", counts)
    print("rows missing lean_code:", len(missing))
    return 1 if missing else 0


if __name__ == "__main__":
    raise SystemExit(main())
