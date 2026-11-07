"""Where the corpus sits on the blueprint: the data behind the program tree.

The blueprint (``docs/blueprint.md``) is the program's map: proved nodes tagged in
``MathFin/Blueprint.lean`` and frontier nodes in ``docs/blueprint_frontier.toml``. The corpus is
what the library delivers. This module places every corpus entry relative to the map, using the
declaration index (``lake exe mathfin_index``):

* an entry **rests on** a node when a MathFin constant its proof cites depends on the node's
  declaration, through the index's ``uses`` (the same proof-term walk that draws the
  blueprint's edges, ``Architect.collectUsed``, stopping at tagged constants);
* it **feeds** a node when the node's declaration depends on a constant the entry cites;
* it is **upstream only** when its proof cites no MathFin constant (a ``library_wrapper``);
* otherwise it is **off the map**: proved, and connected to the library by imports, but in no
  relation the program map records.

``off_map_count`` is a ratchet count (``ratchet.json``: ``corpus_off_blueprint``); the docs site
draws the whole picture as the program tree (``tree.html``, ``tree_data``).

    python3 -m tools.verify.program_tree decl-index.json            # summary by area
    python3 -m tools.verify.program_tree decl-index.json --off risk # the off-map entries of an area
"""

from __future__ import annotations

import argparse
import json
import tomllib
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path

from .corpus import iter_entries
from .decl_index import DeclIndex
from .mathfin_index import cited_constants, declaration_index

NODES_JSON = Path("docs/blueprint_nodes.json")
FRONTIER_TOML = Path("docs/blueprint_frontier.toml")

# A section of the library (`MathFin.<Section>.…`) and the `area:*` label its work carries.
SECTION_AREA = {
    "Foundations": "foundations", "Bridges": "foundations", "BlackScholes": "black-scholes",
    "Binomial": "binomial", "FixedIncome": "fixed-income", "Portfolio": "portfolio",
    "Performance": "portfolio", "RiskMeasures": "risk", "Actuarial": "actuarial",
    "DeFi": "defi", "Futures": "futures", "Execution": "execution", "Contracts": "contracts",
    "Commodities": "commodities",
}

KINDS = ("rests-on-node", "feeds-node", "upstream-only", "off-map")


def area_of_module(module: str) -> str:
    parts = module.split(".")
    sec = parts[1] if len(parts) > 2 else ""
    return SECTION_AREA.get(sec, sec.lower() or "upstream")


@dataclass(frozen=True)
class Placement:
    entry: str
    name: str
    status: str
    kind: str  # one of KINDS
    area: str
    rests_on: tuple[str, ...]  # node labels, all of them
    nearest: str | None  # the deepest node it rests on: where the tree hangs it


def _depths(nodes: list[dict]) -> dict[str, int]:
    by = {n["label"]: n for n in nodes}
    memo: dict[str, int] = {}

    def depth(label: str, stack: frozenset[str] = frozenset()) -> int:
        if label in memo:
            return memo[label]
        if label in stack or label not in by:
            return 0
        uses = [u for u in by[label].get("uses", ()) if u in by]
        memo[label] = 1 + max((depth(u, stack | {label}) for u in uses), default=-1)
        return memo[label]

    return {label: depth(label) for label in by}


def place_corpus(idx: DeclIndex, nodes: list[dict]) -> list[Placement]:
    """Every corpus entry, placed relative to the Lean-backed blueprint nodes."""
    tagged = {n["name"]: n["label"] for n in nodes if n.get("name")}
    depth = _depths(nodes)

    rests: dict[str, frozenset[str]] = {}

    def rests_on(name: str) -> frozenset[str]:
        # iterative post-order walk; a cycle (mutual recursion) contributes nothing extra
        if name in rests:
            return rests[name]
        stack, onstack = [(name, False)], set()
        while stack:
            x, done = stack.pop()
            if x in rests:
                continue
            d = idx.decls.get(x)
            if not done:
                onstack.add(x)
                stack.append((x, True))
                for u in (d.uses if d else ()):
                    if u not in tagged and u not in rests and u not in onstack:
                        stack.append((u, False))
                continue
            acc: set[str] = set()
            for u in (d.uses if d else ()):
                if u in tagged:
                    acc.add(tagged[u])
                else:
                    acc |= rests.get(u, frozenset())
            rests[x] = frozenset(acc)
            onstack.discard(x)
        return rests[name]

    below: set[str] = set()  # everything a tagged declaration depends on
    stack = list(tagged)
    while stack:
        x = stack.pop()
        if x in below:
            continue
        below.add(x)
        d = idx.decls.get(x)
        stack.extend(d.uses if d else ())

    source = declaration_index()
    out = []
    for _, t in iter_entries():
        cited = cited_constants(t.get("code", {}).get("lean", ""), source)
        on: set[str] = set()
        for c in cited:
            on |= {tagged[c]} if c in tagged else rests_on(c)
        if not cited:
            kind = "upstream-only"
        elif on:
            kind = "rests-on-node"
        elif cited & below:
            kind = "feeds-node"
        else:
            kind = "off-map"
        mods = sorted({idx.decls[c].module for c in cited if c in idx.decls})
        out.append(Placement(
            entry=t["id"], name=t.get("name", ""),
            status=t.get("metadata", {}).get("formalization_status", ""), kind=kind,
            area=area_of_module(mods[0]) if mods else "upstream", rests_on=tuple(sorted(on)),
            nearest=max(on, key=lambda label: (depth.get(label, 0), label)) if on else None))
    return out


def load_nodes(path: Path = NODES_JSON) -> list[dict]:
    return json.loads(path.read_text(encoding="utf-8")) if path.exists() else []


def load_frontier(path: Path = FRONTIER_TOML) -> list[dict]:
    return tomllib.loads(path.read_text(encoding="utf-8")).get("node", []) if path.exists() else []


def off_map_count(index_path: str | Path) -> int:
    """The ratchet count: corpus entries that cite MathFin but sit off the program map."""
    places = place_corpus(DeclIndex.load(index_path), load_nodes())
    return sum(p.kind == "off-map" for p in places)


def _plain(text: str) -> str:
    """Node prose for a tooltip: TeX delimiters and spacing commands dropped."""
    for a, b in (("$", ""), (r"\tfrac", ""), (r"\,", " "), (r"\mid", "|"), ("\n", " ")):
        text = text.replace(a, b)
    return " ".join(text.split())


def tree_data(idx: DeclIndex, nodes: list[dict], frontier: list[dict],
              issues: list[dict] | None = None) -> dict:
    """Everything the tree page draws, as one JSON-ready dict."""
    places = place_corpus(idx, nodes)
    nearest = Counter(p.nearest for p in places if p.nearest)
    named: dict[str, list[list]] = defaultdict(list)
    for i in issues or ():
        from .blueprint_issues import named_nodes

        for label in named_nodes(i.get("body")):
            status = [x.split(":", 1)[1] for x in i.get("labels", ()) if x.startswith("status:")]
            named[label].append([i["number"], i["state"][0], int(bool(i.get("is_pr"))),
                                 i["title"][:120], status[:1]])
    out_nodes = []
    for n in nodes:
        status = ("upstream" if not n.get("module", "").startswith("MathFin")
                  else "proved" if n.get("leanOk", True) else "partial")
        out_nodes.append(dict(
            l=n["label"], t=n.get("title") or n["label"], s=status, u=n.get("uses", []),
            a=area_of_module(n.get("module", "")) if status != "upstream" else "upstream",
            x=_plain(n.get("text", ""))[:480], d=n.get("name"), m=n.get("module"),
            e=nearest.get(n["label"], 0), i=named.get(n["label"], [])))
    for f in frontier:
        out_nodes.append(dict(
            l=f["label"], t=f["title"], s="frontier", u=f.get("uses", []), a=f.get("area", ""),
            x=f.get("statement", ""), ground=f.get("ground", ""), core=f.get("core", []),
            e=0, i=named.get(f["label"], [])))
    by_area: dict[str, Counter] = defaultdict(Counter)
    off: dict[str, list[list[str]]] = defaultdict(list)
    for p in places:
        by_area[p.area][p.kind] += 1
        if p.kind == "off-map":
            off[p.area].append([p.entry, p.name[:90]])
    return dict(nodes=out_nodes, areas={a: dict(c) for a, c in by_area.items()},
                off={a: v for a, v in off.items()}, issues=issues is not None,
                corpus=len(places))


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(prog="python3 -m tools.verify.program_tree")
    ap.add_argument("index", help="decl-index.json (lake exe mathfin_index)")
    ap.add_argument("--off", metavar="AREA", help="list the off-map entries of an area")
    args = ap.parse_args(argv)
    places = place_corpus(DeclIndex.load(args.index), load_nodes())
    if args.off:
        for p in places:
            if p.kind == "off-map" and p.area == args.off:
                print(f"{p.entry}\t{p.name}")
        return 0
    by_area: dict[str, Counter] = defaultdict(Counter)
    for p in places:
        by_area[p.area][p.kind] += 1
    total = Counter(p.kind for p in places)
    print(f"{'area':<16}" + "".join(f"{k:>15}" for k in KINDS))
    for a in sorted(by_area, key=lambda a: -sum(by_area[a].values())):
        print(f"{a:<16}" + "".join(f"{by_area[a][k]:>15}" for k in KINDS))
    print(f"{'all':<16}" + "".join(f"{total[k]:>15}" for k in KINDS))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
