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

``off_map_count`` is a ratchet count (``ratchet.json``: ``corpus_off_blueprint``), and so is the
number of ``islands`` of the proved blueprint (``blueprint_islands``); the docs site
draws the whole picture as the program tree (``tree.html``, ``tree_data``), laid out on the map in
``tree_map.toml``: four roots, the pricing functional as the trunk, five limbs. The map is a way of
drawing the library and nothing else reads it.

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
TREE_MAP = Path(__file__).with_name("tree_map.toml")
FRONTIER_TOML = Path("docs/blueprint_frontier.toml")

# Where a module sits (`MathFin.<Layer>.<Sub>.…`, longest prefix first) and the `area:*` label
# its work carries.
SECTION_AREA = {
    "Probability": "foundations", "Pricing": "foundations", "Contracts": "contracts",
    "Models": "black-scholes", "Models.StochVol": "stoch-vol", "Models.Binomial": "binomial",
    "Models.Rates": "fixed-income", "Models.Credit": "credit", "Models.Forwards": "futures",
    "Risk": "risk", "Choice": "portfolio", "Insurance": "actuarial", "Markets": "execution",
    "Markets.DeFi": "defi",
}

KINDS = ("rests-on-node", "feeds-node", "upstream-only", "off-map")

# Where the tree puts a node the map does not name, and an area's fallen leaves: by directory.
AREA_PLACE = {
    "foundations": "pricing", "contracts": "pricing", "black-scholes": "models/black-scholes",
    "binomial": "models/discrete", "stoch-vol": "models/stoch-vol", "fixed-income": "models/rates",
    "credit": "models/credit", "futures": "models/fx-futures", "commodities": "models/fx-futures",
    "fx": "models/fx-futures", "portfolio": "choice", "risk": "risk/measures",
    "actuarial": "insurance", "execution": "markets/execution", "defi": "markets/amm",
    "upstream": "brownian",
}


def load_map(path: Path = TREE_MAP) -> dict:
    """The tree's map: its parts in drawing order, branch names, and each named node's place."""
    raw = tomllib.loads(path.read_text(encoding="utf-8"))
    return dict(parts=raw.get("part", []), branch=raw.get("branch", {}), place=raw.get("place", {}))


# Where the tree puts a module's nodes by default: its directory, longest prefix first. The map
# names only the nodes that sit elsewhere.
DIR_PLACE = {
    "Probability": "pricing", "Probability.Discrete": "discrete",
    "Probability.Brownian": "brownian", "Probability.BrownianMotion": "brownian",
    "Probability.Martingales": "brownian", "Probability.Gaussian": "analysis",
    "Probability.Analysis": "analysis", "Probability.Laws": "analysis",
    "Probability.Jumps": "jumps", "Probability.Dependence": "risk/dependence",
    "Contracts": "pricing", "Pricing": "pricing",
    "Models.BlackScholes": "models/black-scholes", "Models.Bachelier": "models/black-scholes",
    "Models.Binomial": "models/discrete", "Models.Jumps": "models/jumps",
    "Models.StochVol": "models/stoch-vol", "Models.LocalVol": "models/local-vol",
    "Models.ModelFree": "models/model-free", "Models.Rates": "models/rates",
    "Models.Credit": "models/credit", "Models.Forwards": "models/fx-futures",
    "Risk": "risk/measures", "Risk.Credit": "risk/dependence",
    "Choice": "choice/static", "Choice.Performance": "choice/performance",
    "Insurance": "insurance/survival",
    "Markets": "markets/execution", "Markets.DeFi": "markets/amm",
    "Markets.Microstructure": "markets/price-formation",
}


def dir_place(module: str) -> str | None:
    parts = module.split(".")[1:-1]
    return next((DIR_PLACE[sec] for k in range(len(parts), 0, -1)
                 if (sec := ".".join(parts[:k])) in DIR_PLACE), None)


def map_place(label: str, area: str, tree_map: dict, module: str = "") -> tuple[str, str]:
    """(part, branch) of a node: the map's place for it, else its directory's, else its area's."""
    where = (tree_map["place"].get(label) or (module and dir_place(module))
             or AREA_PLACE.get(area, "pricing"))
    part, _, branch = where.partition("/")
    return part, branch


def area_of_module(module: str) -> str:
    parts = module.split(".")[1:-1]
    for k in range(len(parts), 0, -1):
        if (sec := ".".join(parts[:k])) in SECTION_AREA:
            return SECTION_AREA[sec]
    return parts[0].lower() if parts else "upstream"


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


def islands(nodes: list[dict]) -> list[list[str]]:
    """The proved blueprint's connected components other than the one holding Brownian motion.

    Proved and upstream nodes are joined by their recorded uses, in either direction. A node in an
    island is proved, but no recorded edge ties it to the rest of the program: the tree draws it
    beside the trunk. The count is a ratchet (``ratchet.json``: ``blueprint_islands``); a shared
    object or a bridge theorem, tagged, joins an island to the tree."""
    wood = {n["label"] for n in nodes if n.get("leanOk", True)}
    parent = {label: label for label in wood}

    def find(x: str) -> str:
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for n in nodes:
        if n["label"] in wood:
            for u in n.get("uses", ()):
                if u in wood:
                    parent[find(n["label"])] = find(u)
    comps: dict[str, list[str]] = defaultdict(list)
    for label in sorted(wood):
        comps[find(label)].append(label)
    main = find("def:brownian-motion") if "def:brownian-motion" in wood else max(
        comps, key=lambda k: len(comps[k]), default=None)
    return sorted((c for k, c in comps.items() if k != main), key=lambda c: (-len(c), c))


def off_map_count(index_path: str | Path) -> int:
    """The ratchet count: corpus entries that cite MathFin but sit off the program map."""
    places = place_corpus(DeclIndex.load(index_path), load_nodes())
    return sum(p.kind == "off-map" for p in places)


def _statement(text: str, limit: int = 480) -> str:
    """Node prose for the side panel, TeX kept for the page to typeset.

    Whitespace is collapsed; a cut at `limit` falls back to before an unclosed `$`, so the
    page never receives half a formula."""
    text = " ".join(text.split())
    if len(text) <= limit:
        return text
    cut = text[:limit].rsplit(" ", 1)[0]
    if cut.count("$") % 2:
        cut = cut[:cut.rindex("$")].rstrip()
    return cut + " …"


def tree_data(idx: DeclIndex, nodes: list[dict], frontier: list[dict],
              issues: list[dict] | None = None) -> dict:
    """Everything the tree page draws, as one JSON-ready dict."""
    places = place_corpus(idx, nodes)
    tree_map = load_map()
    nearest = Counter(p.nearest for p in places if p.nearest)
    named: dict[str, list[list]] = defaultdict(list)
    open_problem: set[str] = set()  # nodes an open `open-problem` issue carries
    for i in issues or ():
        from .blueprint_issues import named_nodes

        for label in named_nodes(i.get("body")):
            status = [x.split(":", 1)[1] for x in i.get("labels", ()) if x.startswith("status:")]
            named[label].append([i["number"], i["state"][0], int(bool(i.get("is_pr"))),
                                 i["title"][:120], status[:1]])
            if i["state"][0] == "o" and "open-problem" in i.get("labels", ()):
                open_problem.add(label)
    out_nodes = []
    for n in nodes:
        status = ("upstream" if not n.get("module", "").startswith("MathFin")
                  else "proved" if n.get("leanOk", True) else "partial")
        out_nodes.append(dict(
            l=n["label"], t=n.get("title") or n["label"], s=status, u=n.get("uses", []),
            a=area_of_module(n.get("module", "")) if status != "upstream" else "upstream",
            x=_statement(n.get("text", "")), d=n.get("name"), m=n.get("module"),
            e=nearest.get(n["label"], 0), i=named.get(n["label"], [])))
    for f in frontier:
        out_nodes.append(dict(
            l=f["label"], t=f["title"], s="frontier", u=f.get("uses", []), a=f.get("area", ""),
            x=f.get("statement", ""), ground=f.get("ground", ""), core=f.get("core", []),
            e=0, i=named.get(f["label"], []), op=int(f["label"] in open_problem)))
    for n in out_nodes:
        n["p"], n["b"] = map_place(n["l"], n["a"], tree_map, n.get("m") or "")
    by_area: dict[str, Counter] = defaultdict(Counter)
    off: dict[str, list[list[str]]] = defaultdict(list)
    for p in places:
        by_area[p.area][p.kind] += 1
        if p.kind == "off-map":
            off[p.area].append([p.entry, p.name[:90]])
    return dict(nodes=out_nodes, areas={a: dict(c) for a, c in by_area.items()},
                off={a: v for a, v in off.items()}, issues=issues is not None,
                corpus=len(places), parts=tree_map["parts"], branch=tree_map["branch"],
                pile={a: "/".join(filter(None, map_place("", a, tree_map))) for a in by_area})


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
