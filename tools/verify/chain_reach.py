"""Chain reach: how far each finance theorem's statement is from the trunk, in statements.

The measure of whether the library is one structure (docs/specs/2026-11-08-chain-design.md §4).
It is computed from the declaration index alone (``lake exe mathfin_index decl-index.json``),
from what declarations *state* and what definitions are *built from*. Nothing else creates an
edge: not a module's directory, an import, a docstring, a blueprint tag or a taxonomy entry. So
moving, renaming or relabelling leaves every number where it was; only a theorem whose
statement joins two objects, or a definition built from another, moves it.

* **Concepts** are the public ``def``/``structure``/``inductive`` declarations of the finance
  cells, i.e. outside the tool cells (``probability/*``, ``statistics``) of
  ``docs/taxonomy.toml``. The **spine** is the concepts of the trunk (``market``) and of arbitrage
  theory (``valuation/general``): positions, markets, pricing measures, the fundamental theorems.
  The taxonomy decides only these two sets, never an edge.
* **Edges** (undirected) join two concepts that one public theorem's statement mentions (at most
  15 concepts in the statement), and a non-Prop definition to each concept its body uses. A
  Prop-valued definition (a hypothesis bundle) joins nothing: assuming two things together is not
  a theorem about them. With ``guard`` (the default) a theorem joins its concepts only when its
  proof uses at least two library declarations besides them, so a definitional restatement does
  not count as a bridge.
* The **distance** of a concept is its breadth-first distance from the spine. A finance
  theorem's **hop** is one more than the least distance among the concepts its statement
  mentions, infinite if it mentions none.
* **R3** is the share of finance theorems outside the spine with hop at most 3, **R2** at most 2.
  **Sockets** are the model families with a theorem stating that some measure prices a
  ``Market`` (its statement mentions ``Market.IsPricingMeasure``) in a module of that family.
  **Joint span** counts, for each pair of limbs, the theorems whose statements mention concepts
  of both.

    python3 -m tools.verify.chain_reach decl-index.json            # the report (markdown)
    python3 -m tools.verify.chain_reach decl-index.json --json     # the numbers
    python3 -m tools.verify.chain_reach decl-index.json --unguarded

Host-side, stdlib only.
"""

from __future__ import annotations

import argparse
import json
import re
from collections import Counter, defaultdict, deque
from dataclasses import dataclass, field
from typing import Callable
from pathlib import Path

from . import taxonomy

PRICING_MEASURE = "MathFin.Market.IsPricingMeasure"
MAX_CONCEPTS = 15
_TOKEN = re.compile(r"\.?[A-Za-z_][A-Za-z0-9_'.]*")
_LIMBS = {"market": "valuation", "valuation": "valuation", "choice": "choice", "risk": "risk"}


def _is_tool(cell: str | None) -> bool:
    return cell is None or taxonomy.part_of(cell) in ("probability", "statistics")


def _is_spine(cell: str | None) -> bool:
    return cell in ("market", "valuation/general")


def _prop_valued(decl: dict) -> bool:
    return decl["type"].rstrip().endswith("Prop")


@dataclass
class Reach:
    hops: dict[str, float]  # finance theorem -> hop (inf when unreached)
    cell: dict[str, str]  # finance theorem -> its cell
    sockets: set[str]  # model families with a pricing-measure theorem
    joint_span: Counter  # (limb, limb) -> theorems
    dist: dict[str, int] = field(default_factory=dict)  # concept -> distance from the spine
    mentioned: Callable[[dict], set[str]] = lambda d: set()  # the concepts a record states

    def hop_of(self, d: dict) -> float:
        """The hop of a node's declaration: a theorem's hop, a concept's distance plus one
        (a spine theorem or concept sits at 1); infinite when unreached or not a finance
        declaration (the caller decides what a tool is)."""
        if d["name"] in self.hops:
            return self.hops[d["name"]]
        if d["name"] in self.dist:
            return 1 + self.dist[d["name"]]
        return 1 if d["kind"] == "theorem" and d["name"] in self.spine_theorems else float("inf")

    spine_theorems: frozenset[str] = frozenset()

    def share(self, k: int, cell: str | None = None) -> float:
        hs = [h for t, h in self.hops.items() if cell is None or self.cell[t] == cell]
        return sum(h <= k for h in hs) / len(hs) if hs else 0.0


def compute(decls: list[dict], *, guard: bool = True,
            connectors: list[dict] = ()) -> Reach:
    """The reach of the library; with ``connectors`` (records of the ``MathFinFrontier``
    index), as if those statements were proved: each joins the concepts it mentions."""
    by = {d["name"]: d for d in decls}
    cell = {d["name"]: taxonomy.cell_of(d["module"]) for d in decls}
    concepts = {n for n, d in by.items() if d["kind"] in ("def", "structure", "inductive")
                and not d["private"] and not _is_tool(cell[n])}
    spine = {n for n in concepts if _is_spine(cell[n])}

    # `(M).IsPricingMeasure T Q`, `M.price Q c`: dot notation prints a method by its last
    # components only. Such a token names the concept ending in it, when exactly one concept
    # does, or else the one whose namespace is a concept the statement names in full.
    by_suffix: dict[str, list[str]] = defaultdict(list)
    for n in concepts:
        parts = n.split(".")
        for k in range(1, len(parts)):
            by_suffix[".".join(parts[-k:])].append(n)

    def mentioned(d: dict) -> set[str]:
        tokens = _TOKEN.findall(d["type"])
        full = {t for t in tokens if t in concepts}
        out = set(full)
        for t in tokens:
            if t in concepts:
                continue
            if t.startswith("."):  # `(e).method`
                rest = t[1:]
            elif "." in t and not t.startswith("MathFin"):  # `x.method` on a local `x`
                rest = t.split(".", 1)[1]
            else:
                continue
            cands = by_suffix.get(rest, [])
            if len(cands) > 1:
                cands = [c for c in cands if c.rsplit(".", rest.count(".") + 1)[0] in full]
            if len(cands) == 1:
                out.add(cands[0])
        return out - {d["name"]}

    theorems = [d for d in decls if d["kind"] == "theorem" and not d["private"]]
    stated = {d["name"]: mentioned(d) for d in theorems}

    adj: dict[str, set[str]] = defaultdict(set)
    for d in theorems:
        ns = stated[d["name"]]
        if len(ns) > MAX_CONCEPTS:
            continue
        if guard and len(set(d["uses"]) - ns - {d["name"]}) < 2:
            continue
        for a in ns:
            adj[a] |= ns - {a}
    for d in connectors:
        ns = mentioned(d)
        for a in ns:
            adj[a] |= ns - {a}
    for n in concepts:
        d = by[n]
        if d["kind"] != "def" or _prop_valued(d):
            continue
        for u in d["uses"]:
            if u in concepts and u != n:
                adj[n].add(u)
                adj[u].add(n)

    dist = {n: 0 for n in spine}
    queue = deque(spine)
    while queue:
        a = queue.popleft()
        for b in adj[a]:
            if b not in dist:
                dist[b] = dist[a] + 1
                queue.append(b)

    hops: dict[str, float] = {}
    tcell: dict[str, str] = {}
    sockets: set[str] = set()
    span: Counter = Counter()
    spine_theorems: set[str] = set()
    for d in theorems:
        c = cell[d["name"]]
        if _is_tool(c):
            continue
        ns = stated[d["name"]]
        if PRICING_MEASURE in ns:
            fam = taxonomy.family_of(d["module"])
            if fam:
                sockets.add(fam)
        limbs = {_LIMBS[taxonomy.part_of(cell[n])] for n in ns if cell[n]}
        for pair in {tuple(sorted((a, b))) for a in limbs for b in limbs if a < b}:
            span[pair] += 1
        if _is_spine(c):
            spine_theorems.add(d["name"])
            continue
        hops[d["name"]] = 1 + min((dist.get(n, float("inf")) for n in ns),
                                  default=float("inf"))
        tcell[d["name"]] = c
    return Reach(hops=hops, cell=tcell, sockets=sockets, joint_span=span, dist=dist,
                 mentioned=mentioned, spine_theorems=frozenset(spine_theorems))


def connector_gains(decls: list[dict], connectors: list[dict], *,
                    guard: bool = True) -> dict[str, int]:
    """For each connector, how many more finance theorems it would put within 3 hops of the
    spine, were it proved (alone), and the same for all of them together (key ``*``)."""
    def reached(cs) -> int:
        return sum(h <= 3 for h in compute(decls, guard=guard, connectors=cs).hops.values())

    base = reached([])
    out = {c["name"]: reached([c]) - base for c in connectors
           if c["kind"] == "theorem" and not c["private"]}
    out["*"] = reached([c for c in connectors if c["kind"] == "theorem"]) - base
    return out


def load(path: str | Path) -> list[dict]:
    return json.loads(Path(path).read_text(encoding="utf-8"))["decls"]


def summary(r: Reach) -> dict:
    cells = sorted(set(r.cell.values()), key=list(taxonomy.cells()).index)
    return {
        "theorems": len(r.hops),
        "R2": round(100 * r.share(2), 1),
        "R3": round(100 * r.share(3), 1),
        "sockets": sorted(r.sockets),
        "families": len(taxonomy.families()),
        "joint_span": {f"{a}+{b}": n for (a, b), n in sorted(r.joint_span.items())},
        "cells": {c: {"theorems": sum(v == c for v in r.cell.values()),
                      "R3": round(100 * r.share(3, c), 1)} for c in cells},
    }


def report(s: dict) -> str:
    lines = ["## Chain reach", "",
             f"{s['theorems']} finance theorems outside the spine: **R3 {s['R3']}%**, "
             f"R2 {s['R2']}% (share within 3 and 2 statement hops of the spine). "
             f"Sockets: {len(s['sockets'])} of {s['families']} families "
             f"({', '.join(s['sockets']) or 'none'}). Joint span: "
             + ", ".join(f"{k} {v}" for k, v in s["joint_span"].items()) + ".", "",
             "| cell | theorems | R3 |", "|---|---|---|"]
    lines += [f"| {taxonomy.label(c)} | {v['theorems']} | {v['R3']}% |"
              for c, v in s["cells"].items()]
    return "\n".join(lines) + "\n"


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(prog="python3 -m tools.verify.chain_reach")
    ap.add_argument("index", nargs="?", default="decl-index.json")
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--unguarded", action="store_true")
    ap.add_argument("--frontier", help="the connector library's index (frontier-index.json)")
    args = ap.parse_args(argv)
    decls = load(args.index)
    s = summary(compute(decls, guard=not args.unguarded))
    if args.frontier and Path(args.frontier).exists():
        s["connectors"] = connector_gains(decls, load(args.frontier), guard=not args.unguarded)
    if args.json:
        print(json.dumps(s, indent=2, ensure_ascii=False))
        return 0
    print(report(s), end="")
    if s.get("connectors"):
        print("\n| connector | theorems it would bring within 3 hops |\n|---|---|")
        for name, g in sorted(s["connectors"].items(), key=lambda kv: -kv[1]):
            if name != "*":
                print(f"| `{name}` | {g} |")
        print(f"| all together | {s['connectors']['*']} |")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
