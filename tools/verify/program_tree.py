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
draws the whole picture as the program tree (``tree.html``, ``tree_data``). Where a node sits is
read from ``docs/taxonomy.toml`` (``tools/verify/taxonomy.py``): a proved node in the cell of its
declaration module, a frontier node in its ``area``, both with a family; ``tree_map.toml`` lists
the few proved nodes whose declaration module is not their conceptual cell.

Height on the tree is measured, not ordered: a node on a limb sits at its **hop**, the distance
in statements from the trunk that ``chain_reach`` computes from the same index (a theorem's hop;
for a definition, its concept distance plus one). A node of infinite hop is an **island**, drawn
beside its limb under its cluster's name (a declared ``[[standalone]]`` of the taxonomy, else its
cell) and ringed when nothing reaches it. A ``[[tower]]`` of the taxonomy is one node. A
**connector** (a frontier node with a ``lean`` field) is a phantom: placed between the nodes its
statement mentions, at the hop it would have if proved, sized by ``connector_gains``.

    python3 -m tools.verify.program_tree decl-index.json                    # summary by cell
    python3 -m tools.verify.program_tree decl-index.json --off risk/credit  # a cell's off-map
"""

from __future__ import annotations

import argparse
import json
import tomllib
from collections import Counter, defaultdict
from dataclasses import dataclass
from pathlib import Path

from .corpus import iter_entries
from . import chain_reach, taxonomy
from .decl_index import DeclIndex
from .mathfin_index import cited_constants, declaration_index

NODES_JSON = Path("docs/blueprint_nodes.json")
TREE_MAP = Path(__file__).with_name("tree_map.toml")
FRONTIER_TOML = Path("docs/blueprint_frontier.toml")

KINDS = ("rests-on-node", "feeds-node", "upstream-only", "off-map")

UPSTREAM = "upstream"  # the cell of an entry that cites no MathFin module


def load_map(path: Path = TREE_MAP) -> dict[str, str]:
    """The per-node exceptions: blueprint label -> cell key."""
    return tomllib.loads(path.read_text(encoding="utf-8")).get("place", {})


def cell_of_module(module: str) -> str:
    """The taxonomy cell of a MathFin module (the trunk for the library's own machinery)."""
    return taxonomy.cell_of(module) or "market"


def place_node(n: dict, exceptions: dict[str, str]) -> tuple[str, str | None]:
    """(cell, family) of a node of the tree: a proved node by its exception, else by its
    declaration module; a frontier node by its ``area`` and ``family``; upstream in the soil."""
    if n["s"] == "frontier":
        return n["area"], n.get("family") or None
    module = n.get("m") or ""
    if n["s"] == "upstream":
        return "probability/brownian", None
    return exceptions.get(n["l"]) or cell_of_module(module), taxonomy.family_of(module)


@dataclass(frozen=True)
class Placement:
    entry: str
    name: str
    status: str
    kind: str  # one of KINDS
    cell: str
    family: str | None
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
            cell=cell_of_module(mods[0]) if mods else UPSTREAM,
            family=taxonomy.family_of(mods[0]) if mods else None, rests_on=tuple(sorted(on)),
            nearest=max(on, key=lambda label: (depth.get(label, 0), label)) if on else None))
    return out


def load_nodes(path: Path = NODES_JSON) -> list[dict]:
    """The exported Lean-tagged nodes, minus any label retired since the export.

    An export older than a retirement still lists the retired node. The graph the next export
    draws walks through an untagged declaration to what it uses, so a retired node is removed
    here the same way: its users inherit its own `uses`."""
    from .blueprint_issues import load_retired

    gone = set(load_retired(path.parent / "blueprint_retired.toml"))
    nodes = json.loads(path.read_text(encoding="utf-8")) if path.exists() else []
    if not gone:
        return nodes
    by = {n["label"]: n for n in nodes}

    def through(label: str, seen: frozenset[str] = frozenset()) -> list[str]:
        if label not in gone:
            return [label]
        if label in seen or label not in by:
            return []
        return [u for v in by[label].get("uses", ()) for u in through(v, seen | {label})]

    out = []
    for n in nodes:
        if n["label"] in gone:
            continue
        uses = list(dict.fromkeys(u for v in n.get("uses", ()) for u in through(v)))
        out.append({**n, "uses": uses})
    return out


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


def _records(idx: DeclIndex) -> list[dict]:
    """The index in the shape ``chain_reach`` reads."""
    return [dict(name=d.name, kind=d.kind, module=d.module, private=d.private, type=d.type,
                 uses=list(d.uses)) for d in idx.decls.values()]


def tree_data(idx: DeclIndex, nodes: list[dict], frontier: list[dict],
              issues: list[dict] | None = None, connectors: list[dict] = ()) -> dict:
    """Everything the tree page draws, as one JSON-ready dict. ``connectors`` are the records
    of the connector library's index (``MathFinFrontier.*``)."""
    places = place_corpus(idx, nodes)
    exceptions = load_map()
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
            x=_statement(n.get("text", "")), d=n.get("name"), m=n.get("module"),
            e=nearest.get(n["label"], 0), i=named.get(n["label"], [])))
    for f in frontier:
        out_nodes.append(dict(
            l=f["label"], t=f["title"], s="frontier", u=f.get("uses", []),
            area=f["area"], family=f.get("family", ""),
            x=f.get("statement", ""), ground=f.get("ground", ""), core=f.get("core", []),
            e=0, i=named.get(f["label"], []), op=int(f["label"] in open_problem),
            **({"ln": f["lean"]} if f.get("lean") else {})))
    joint_of = {j["node"]: j["limbs"] for j in taxonomy.joints()}
    for n in out_nodes:
        cell, family = place_node(n, exceptions)
        n["p"], _, n["b"] = cell.partition("/")
        if family:
            n["f"] = family
        if n["l"] in joint_of:
            n["j"] = joint_of[n["l"]]
        n.pop("area", None)
        n.pop("family", None)
    # the measure: heights, towers, islands, phantoms
    records = _records(idx)
    reach = chain_reach.compute(records)
    by_rec = {r["name"]: r for r in records}
    hops = {r["name"]: reach.hop_of(r) for r in records}
    part_kind = {p["key"]: p["kind"] for p in taxonomy.parts()}
    assign_hops(out_nodes, hops)
    out_nodes = collapse_towers(out_nodes, sorted({r["module"] for r in records}),
                                taxonomy.towers())
    by_conn = {c["name"]: c for c in connectors}
    gains = chain_reach.connector_gains(records, list(connectors)) if connectors else {}
    conn_nodes = [(n["l"], by_conn[n["ln"]]) for n in out_nodes if n.get("ln") in by_conn]
    phantom = phantoms(out_nodes, conn_nodes, reach,
                       {r["name"]: r["module"] for r in records}, gains)
    for n in out_nodes:
        if n["l"] in phantom:
            ph = phantom[n["l"]]
            n["ph"] = dict(gain=ph["gain"])
            n["hp"] = ph["hp"]
            if ph["ends"]:
                n["u"] = ph["ends"]
        elif n.get("ln"):
            n["ph"] = dict(gain=0)
    reached = {e for ph in phantom.values() for e in ph["ends"]}
    island_list = float_islands(out_nodes, part_kind, reached)
    metric = metrics(reach, len(taxonomy.families()), island_list)
    by_cell: dict[str, Counter] = defaultdict(Counter)
    off: dict[str, list[list[str]]] = defaultdict(list)
    for p in places:
        by_cell[p.cell][p.kind] += 1
        if p.kind == "off-map":
            off[p.cell].append([p.entry, p.name[:90]])
    return dict(nodes=out_nodes, areas={a: dict(c) for a, c in by_cell.items()},
                off=dict(off), issues=issues is not None, corpus=len(places),
                parts=crown_order(taxonomy.parts()),
                cellName={k: taxonomy.label(k) for k in taxonomy.cells()} | {UPSTREAM: UPSTREAM},
                cellBlurb={k: c["blurb"] for k, c in taxonomy.cells().items()},
                families=[dict(key=k, title=f["title"], blurb=f["blurb"], hue=f["hue"],
                               socket=k in reach.sockets)
                          for k, f in taxonomy.families().items()],
                joints=taxonomy.joints(), islands=island_list, metrics=metric)


def _hop(h: float) -> int | None:
    return None if h == float("inf") else int(h)


def assign_hops(nodes: list[dict], hops: dict[str, float]) -> None:
    """Set ``hp`` on every node: the measured hop of its declaration (``None`` when infinite or
    when the node has no declaration). A frontier node with no declaration takes one more than
    the least hop among the nodes it builds on, ``None`` if none of them is measured."""
    by = {n["l"]: n for n in nodes}
    for n in nodes:
        n["hp"] = _hop(hops.get(n.get("d") or "", float("inf")))
    memo: dict[str, int | None] = {}

    def frontier_hop(label: str, seen: frozenset[str] = frozenset()) -> int | None:
        n = by[label]
        if n["s"] != "frontier" or n.get("d"):
            return n["hp"]
        if label in memo:
            return memo[label]
        us = [u for u in n["u"] if u in by and u not in seen]
        hs = [h for h in (frontier_hop(u, seen | {label}) for u in us) if h is not None]
        memo[label] = 1 + min(hs) if hs else None
        return memo[label]

    for n in nodes:
        if n["s"] == "frontier" and not n.get("d"):
            n["hp"] = frontier_hop(n["l"])


def collapse_towers(nodes: list[dict], modules: list[str], towers: list[dict]) -> list[dict]:
    """Each tower of the taxonomy becomes one node. Its members' modules are counted in
    ``modules`` (every module of the index), its hop is the best of its members' (the summit),
    its corpus count the sum, its issues the union, and every ``uses`` edge into a member points
    at the tower. A tower with no blueprint node stays absent."""
    out = list(nodes)
    for t in towers:
        mem = [n for n in out if n["s"] != "frontier" and n.get("m")
               and taxonomy.in_prefixes(n["m"], t["modules"])]
        if not mem:
            continue
        gone = {n["l"] for n in mem}
        hs = [n["hp"] for n in mem if n["hp"] is not None]
        summit = min(mem, key=lambda n: (n["hp"] is None, n["hp"] or 0, n["l"]))
        label = "tower:" + t["key"]
        count = sum(taxonomy.in_prefixes(m, t["modules"]) for m in modules)
        uses = list(dict.fromkeys(label if u in gone else u for n in mem for u in n["u"]
                                  if u not in gone))
        tower = dict(
            summit, l=label, t=f"{t['title']} tower", tw=count, u=uses,
            s="partial" if any(n["s"] == "partial" for n in mem) else "proved",
            hp=min(hs) if hs else None, e=sum(n["e"] for n in mem),
            i=[x for n in mem for x in n["i"]],
            x=f"{len(mem)} blueprint nodes in {count} modules under "
              f"{', '.join(t['modules'])}; the summit is {summit['t']}.")
        out = [n for n in out if n["l"] not in gone]
        for n in out:
            if gone & set(n["u"]):
                n["u"] = list(dict.fromkeys(label if u in gone else u for u in n["u"]))
        out.append(tower)
    return out


def float_islands(nodes: list[dict], part_kind: dict[str, str], reached: set[str],
                  standalone: list[dict] | None = None) -> list[dict]:
    """The clusters of infinite hop, drawn beside their limb. A proved node on a limb whose hop
    is infinite belongs to the ``[[standalone]]`` entry covering its module, else to its cell; a
    frontier node joins the cluster of an island node it builds on. A cluster is **declared**
    when a standalone entry covers it and **reached** when a connector mentions one of its
    nodes; one that is neither gets the red ring (``ring``). Sets ``isl`` on each member."""
    standalone = taxonomy.standalones() if standalone is None else standalone
    by = {n["l"]: n for n in nodes}
    clusters: dict[str, dict] = {}

    def home(n: dict) -> dict:
        for k, st in enumerate(standalone):
            if n.get("m") and taxonomy.in_prefixes(n["m"], st["modules"]):
                return dict(key=f"standalone:{k}", title=st.get("title") or st["reason"][:48],
                            declared=True, reason=st["reason"], socket=st.get("socket", ""))
        cell = n["p"] + ("/" + n["b"] if n.get("b") else "")
        return dict(key="cell:" + cell, title=taxonomy.label(cell), declared=False,
                    reason="", socket="")

    for n in nodes:
        if (part_kind.get(n["p"]) == "limb" and not n.get("j") and n["hp"] is None
                and n["s"] in ("proved", "partial")):
            c = home(n)
            cl = clusters.setdefault(c["key"], dict(c, p=n["p"], nodes=[]))
            cl["nodes"].append(n["l"])
            n["isl"] = c["key"]
    for n in nodes:  # a frontier node that builds on an island sits with it
        if n["s"] == "frontier" and n["hp"] is None and not n.get("isl"):
            hosts = [by[u]["isl"] for u in n["u"] if u in by and by[u].get("isl")]
            if hosts:
                n["isl"] = hosts[0]
                clusters[hosts[0]]["nodes"].append(n["l"])
    for cl in clusters.values():
        cl["ring"] = not cl["declared"] and not (set(cl["nodes"]) & reached)
    return sorted(clusters.values(), key=lambda c: (-len(c["nodes"]), c["key"]))


def phantoms(nodes: list[dict], connectors: list[tuple[str, dict]], reach: chain_reach.Reach,
             module_of: dict[str, str], gains: dict[str, int]) -> dict[str, dict]:
    """Where each connector sits. ``connectors`` pairs a node label with its record in the
    connector library's index. The ends are the blueprint nodes of the concepts its statement
    mentions (the node whose declaration is the concept, else a node of the concept's module,
    ``module_of``); the hop is one more than the least concept distance, what it would be if
    proved; the gain is ``connector_gains`` (theorems brought within three hops)."""
    by_decl = {n["d"]: n["l"] for n in nodes if n.get("d")}
    by_mod: dict[str, list[str]] = defaultdict(list)
    for n in nodes:
        if n.get("m") and n["s"] != "frontier":
            by_mod[n["m"]].append(n["l"])
    out: dict[str, dict] = {}
    for label, rec in connectors:
        ends: list[str] = []
        ds = []
        for c in sorted(reach.mentioned(rec)):
            ds.append(reach.dist.get(c, float("inf")))
            hit = by_decl.get(c) or next(iter(by_mod.get(module_of.get(c, ""), [])), None)
            if hit and hit not in ends:
                ends.append(hit)
        out[label] = dict(ends=ends, hp=_hop(1 + min(ds)) if ds else None,
                          gain=gains.get(rec["name"], 0))
    return out


def metrics(reach: chain_reach.Reach, families: int, island_list: list[dict]) -> dict:
    """The strip above the tree: how connected the library is, from the same index."""
    s = chain_reach.summary(reach)
    return dict(R3=s["R3"], sockets=s["sockets"], families=families,
                span=sum(s["joint_span"].values()), islands=len(island_list),
                unreached=sum(c["ring"] for c in island_list), theorems=s["theorems"])


def crown_order(parts: list[dict]) -> list[dict]:
    """The parts as drawn: roots, the trunk, then the limbs from the centre out, the first limb
    in the middle, the second to its left, the third to its right."""
    limbs: list[dict] = []
    for i, p in enumerate(q for q in parts if q["kind"] == "limb"):
        limbs.insert(0, p) if i % 2 else limbs.append(p)
    return [p for p in parts if p["kind"] != "limb"] + limbs


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(prog="python3 -m tools.verify.program_tree")
    ap.add_argument("index", help="decl-index.json (lake exe mathfin_index)")
    ap.add_argument("--off", metavar="CELL", help="list the off-map entries of a taxonomy cell")
    args = ap.parse_args(argv)
    places = place_corpus(DeclIndex.load(args.index), load_nodes())
    if args.off:
        for p in places:
            if p.kind == "off-map" and p.cell == args.off:
                print(f"{p.entry}\t{p.name}")
        return 0
    by_area: dict[str, Counter] = defaultdict(Counter)
    for p in places:
        by_area[p.cell][p.kind] += 1
    total = Counter(p.kind for p in places)
    print(f"{'cell':<24}" + "".join(f"{k:>15}" for k in KINDS))
    for a in sorted(by_area, key=lambda a: -sum(by_area[a].values())):
        print(f"{a:<24}" + "".join(f"{by_area[a][k]:>15}" for k in KINDS))
    print(f"{'all':<24}" + "".join(f"{total[k]:>15}" for k in KINDS))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
