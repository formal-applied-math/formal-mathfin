"""One ratchet for every debt count: it may fall, it may not rise.

Mathlib tracks its technical debt (heartbeat bumps, ``erw``, nolints, …) as counts and
watches the trend. Here each count has a baseline in ``ratchet.json``; ``check`` fails
when a count rises above it, and ``update`` lowers a baseline after an improvement (it
refuses to raise one). This is the single mechanism behind every "do not add more of
X" rule, instead of an exemption list per rule.

Two families of metrics, one file:

* **source** metrics, computed from ``MathFin/`` text on the host, checked by
  ``tests/test_ratchet.py`` in the Python gates step;
* **index** metrics, computed from the declaration index (``decl_index.py``), checked
  in ``build.yml`` after ``lake exe mathfin_index`` builds it.

    python3 -m tools.verify.ratchet check [--index decl-index.json]
    python3 -m tools.verify.ratchet update [--index decl-index.json]
    python3 -m tools.verify.ratchet show [--index decl-index.json]
"""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

from . import doc_standard, library
from .mathfin_index import strip_comments

RATCHET_FILE = Path("ratchet.json")
LONG_FILE_LINES = 1500  # Mathlib's `linter.style.longFile` default
LINE_LIMIT = 100  # Mathlib's `linter.style.longLine`

_HEARTBEATS = re.compile(r"\bset_option\s+maxHeartbeats\b")
_WHOLE_MATHLIB = re.compile(r"^(?:public\s+)?import\s+Mathlib\s*$", re.M)


def source_metrics() -> dict[str, int]:
    heartbeats = whole = long_files = long_lines = 0
    for p in library.modules():  # aggregators: size and imports are their job
        src = p.read_text(encoding="utf-8")
        code = strip_comments(src)
        heartbeats += len(_HEARTBEATS.findall(code))
        whole += bool(_WHOLE_MATHLIB.search(code))
        long_files += src.count("\n") + 1 > LONG_FILE_LINES
        long_lines += sum(len(line) > LINE_LIMIT for line in src.split("\n"))
    nolints = len(json.loads(Path("scripts/nolints.json").read_text(encoding="utf-8")))
    return {
        "max_heartbeats": heartbeats,
        "whole_mathlib_imports": whole,
        "long_files": long_files,
        "long_lines": long_lines,
        "nolints": nolints,
    } | doc_standard.coverage(doc_standard.all_docs())


def index_metrics(index_path: str | Path) -> dict[str, int]:
    from .decl_index import DeclIndex

    from .program_tree import load_nodes, place_corpus

    idx = DeclIndex.load(index_path)
    return {
        "private_mathlib_shaped": len(idx.mathlib_shaped_private()),
        "duplicate_statements": sum(len(g) - 1 for g in idx.duplicate_statements()),
        # corpus entries in no relation the program map records (tools/verify/program_tree.py)
        "corpus_off_blueprint": sum(p.kind == "off-map"
                                    for p in place_corpus(idx, load_nodes())),
    }


def load_baseline() -> dict[str, int]:
    return json.loads(RATCHET_FILE.read_text(encoding="utf-8"))["baseline"]


def current(index: str | None) -> dict[str, int]:
    vals = source_metrics()
    if index:
        vals |= index_metrics(index)
    return vals


def check(vals: dict[str, int], baseline: dict[str, int]) -> list[str]:
    """Messages for every metric that rose above its baseline."""
    return [f"{k}: {v} > baseline {baseline[k]}" for k, v in vals.items()
            if k in baseline and v > baseline[k]]


def improvements(vals: dict[str, int], baseline: dict[str, int]) -> list[str]:
    return [f"{k}: {v} < baseline {baseline[k]}" for k, v in vals.items()
            if k in baseline and v < baseline[k]]


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(prog="python3 -m tools.verify.ratchet")
    ap.add_argument("cmd", choices=["check", "update", "show"])
    ap.add_argument("--index", help="decl-index.json, for the index metrics")
    args = ap.parse_args(argv)
    vals = current(args.index)
    data = json.loads(RATCHET_FILE.read_text(encoding="utf-8"))
    baseline = data["baseline"]

    if args.cmd == "show":
        for k, v in vals.items():
            print(f"{k:32} {v:6}   baseline {baseline.get(k, '—')}")
        return 0
    if args.cmd == "check":
        rose = check(vals, baseline)
        for m in rose:
            print(f"ratchet: {m}")
        for m in improvements(vals, baseline):
            print(f"ratchet: improved, {m} (run `python3 -m tools.verify.ratchet update`)")
        return 1 if rose else 0
    # update: lower, never raise; record new metrics the first time they are measured
    rose = check(vals, baseline)
    if rose:
        for m in rose:
            print(f"ratchet: refusing to raise {m}")
        return 1
    for k, v in vals.items():
        if k not in baseline or v < baseline[k]:
            baseline[k] = v
    RATCHET_FILE.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n",
                            encoding="utf-8")
    print("ratchet: baseline updated")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
