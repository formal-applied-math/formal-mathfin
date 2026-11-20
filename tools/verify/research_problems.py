"""The research-problem catalogue and the blueprint stay connected.

Every record of ``docs/research-problems/problems.json`` says whether its question can be
stated in Lean against the library (``formalization.lean_statement``). A problem the library
cannot state yet stays in the catalogue: its ``needs`` name the frontier nodes it waits for,
so the catalogue tells the library what to build next. ``check`` holds the links; ``needs``
ranks the missing objects by how many problems each one blocks.

    python3 -m tools.verify.research_problems check
    python3 -m tools.verify.research_problems needs
"""

from __future__ import annotations

import argparse
import json
from collections import Counter
from pathlib import Path

from . import blueprint_issues as bi

PROBLEMS_JSON = Path("docs/research-problems/problems.json")
STATUSES = frozenset({"stated", "statable", "blocked", "not_a_proposition", "proved"})


def load(path: Path = PROBLEMS_JSON) -> list[dict]:
    return json.loads(path.read_text(encoding="utf-8"))["problems"]


def problems(records: list[dict], nodes: dict[str, bi.Node],
             stated: set[str] | None = None) -> list[str]:
    """What is wrong with the records' ``lean_statement`` fields, as messages."""
    stated = bi.connector_names() if stated is None else stated
    out = []
    for r in records:
        rid = r["id"]
        ls = r.get("formalization", {}).get("lean_statement")
        if ls is None:
            out.append(f"{rid}: no formalization.lean_statement")
            continue
        status, needs, lean, node = ls.get("status"), ls.get("needs", []), ls.get("lean"), \
            ls.get("blueprint")
        if status not in STATUSES:
            out.append(f"{rid}: lean_statement.status `{status}` is not one of {sorted(STATUSES)}")
        if node is not None and node not in nodes:
            out.append(f"{rid}: blueprint `{node}` is not a node")
        for label in needs:
            if label not in nodes:
                out.append(f"{rid}: needs `{label}`, which is not a node")
            elif nodes[label].status != "frontier":
                out.append(f"{rid}: needs `{label}`, which is already proved; "
                           "the problem is statable now")
        if status == "blocked" and not needs:
            out.append(f"{rid}: blocked, but `needs` names nothing")
        if status in ("stated", "statable", "proved") and needs:
            out.append(f"{rid}: {status}, but still lists needs {needs}")
        if status == "stated":
            if lean not in stated:
                out.append(f"{rid}: stated, but `{lean}` is not a theorem of MathFinFrontier/")
            elif node is None or nodes.get(node, bi.Node("", "", "")).lean != lean:
                out.append(f"{rid}: `{lean}` must be the `lean` of its blueprint node `{node}`")
        elif lean:
            out.append(f"{rid}: `lean` is set, but the status is {status}")
    return out


def needs_ranking(records: list[dict]) -> list[tuple[str, list[str]]]:
    """The missing objects, most-blocking first, with the problems each one holds back."""
    by: dict[str, list[str]] = {}
    for r in records:
        for label in r["formalization"]["lean_statement"].get("needs", []):
            by.setdefault(label, []).append(r["id"])
    count = Counter({k: len(v) for k, v in by.items()})
    return [(k, by[k]) for k, _ in count.most_common()]


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(prog="research_problems")
    ap.add_argument("cmd", choices=["check", "needs"])
    args = ap.parse_args(argv)
    records = load()
    if args.cmd == "check":
        errs = problems(records, bi.load_nodes())
        for e in errs:
            print(e)
        print(f"research problems ↔ blueprint: {len(records)} records, {len(errs)} problem(s)")
        return 1 if errs else 0
    for label, ids in needs_ranking(records):
        print(f"{len(ids):3d}  {label}  ({', '.join(ids)})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
